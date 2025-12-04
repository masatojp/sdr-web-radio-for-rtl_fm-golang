package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"image"
	"image/color"
	"image/draw"
	"image/png"
	"io"
	"io/fs"
	"log"
	"math"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/gorilla/websocket"
	"github.com/joho/godotenv"
)

// ==========================================
// 1. 設定 (Configuration)
// ==========================================
const (
	Port           = ":3000"
	InitialFreq    = 126450000
	InitialMode    = "AM"
	SampleRate     = 48000
	RecordingsPath = "./recordings"
	BookmarksFile  = "./bookmarks.json"
	SquelchFile    = "./squelch_data.json"
)

// ==========================================
// 2. データ構造 (Data Structures)
// ==========================================

type ServerState struct {
	Freq        int     `json:"freq"`
	Mode        string  `json:"mode"`
	Title       string  `json:"title"`
	Att         string  `json:"att"`
	Squelch     int     `json:"squelch"`
	IsRecording bool    `json:"isRecording"`
	Lat         float64 `json:"lat"`       // GPS Latitude
	Lon         float64 `json:"lon"`       // GPS Longitude
	Address     string  `json:"address"`   // Reverse Geocoded Address
	GPSStatus   string  `json:"gpsStatus"` // "disconnected", "searching", "active"
	GPSUnlocked bool    `json:"gpsUnlocked"`
	RecFilename string  `json:"-"`
	mu          sync.Mutex
}

type SystemStats struct {
	CPUTemp   float64 `json:"cpuTemp"`
	LoadAvg1  float64 `json:"loadAvg1"`
	LoadAvg5  float64 `json:"loadAvg5"`
	LoadAvg15 float64 `json:"loadAvg15"`
	MemTotal  uint64  `json:"memTotal"`
	MemUsed   uint64  `json:"memUsed"`
	DiskTotal uint64  `json:"diskTotal"`
	DiskUsed  uint64  `json:"diskUsed"`
	Uptime    uint64  `json:"uptime"`
}

type Bookmark struct {
	ID       string  `json:"id"`
	Title    string  `json:"title"`
	Freq     float64 `json:"freq,omitempty"`
	Mode     string  `json:"mode,omitempty"`
	IsFolder bool    `json:"isFolder"`
	ParentID string  `json:"parentId"`
}

type WSCommand struct {
	Type           string          `json:"type"`
	Password       string          `json:"password,omitempty"`
	GPSPassword    string          `json:"gpsPassword,omitempty"`    // GPSロック解除用
	DebugPassword  string          `json:"debugPassword,omitempty"`  // デバッグモード解除用
	DeletePassword string          `json:"deletePassword,omitempty"` // 録音削除用
	Freq           float64         `json:"freq,omitempty"`
	Mode           string          `json:"mode,omitempty"`
	Title          string          `json:"title,omitempty"`
	Att            string          `json:"att,omitempty"`
	Val            int             `json:"val,omitempty"`
	Filename       string          `json:"filename,omitempty"` // 削除時はパスとして使用
	Data           json.RawMessage `json:"data,omitempty"`
	ID             string          `json:"id,omitempty"`
	Dir            string          `json:"dir,omitempty"`
	NewParentID    string          `json:"newParentId,omitempty"`
}

// Recording Structures for Nested Display
type RecFileEntry struct {
	Name string `json:"name"`
	Path string `json:"path"`
	Size int64  `json:"size"`
}
type RecFreqEntry struct {
	Freq  string         `json:"freq"`
	Files []RecFileEntry `json:"files"`
}
type RecDateEntry struct {
	Date  string         `json:"date"`
	Freqs []RecFreqEntry `json:"freqs"`
}

// Nominatim Response
type NominatimResponse struct {
	DisplayName string `json:"display_name"`
}

// Discord Payload Structure
type DiscordEmbedField struct {
	Name   string `json:"name"`
	Value  string `json:"value"`
	Inline bool   `json:"inline"`
}
type DiscordEmbed struct {
	Title       string              `json:"title"`
	Description string              `json:"description"`
	Color       int                 `json:"color"`
	Fields      []DiscordEmbedField `json:"fields"`
	Timestamp   string              `json:"timestamp"`
}
type DiscordPayload struct {
	Username string         `json:"username"`
	Embeds   []DiscordEmbed `json:"embeds"`
}

// ==========================================
// 3. DSP (Audio Processing)
// ==========================================

type AudioDSP struct {
	lastIn      float64
	lastOut     float64
	agcPeak     float64
	agcGain     float64
	squelchGate float64
	rms         float64
}

func NewAudioDSP() *AudioDSP {
	return &AudioDSP{agcGain: 1.0}
}

func (d *AudioDSP) Reset() {
	d.lastIn = 0
	d.lastOut = 0
	d.agcPeak = 0
	d.agcGain = 1.0
	d.squelchGate = 0.0
	d.rms = 0
}

type ProcessResult struct {
	Buffer []byte
	RSSI   int16
	IsOpen bool
}

func (d *AudioDSP) Process(input []byte, threshold int) ProcessResult {
	numSamples := len(input) / 2
	outBuf := new(bytes.Buffer)

	sqThresh := float64(threshold) / 100.0
	var sumSq float64 = 0

	reader := bytes.NewReader(input)

	for i := 0; i < numSamples; i++ {
		var rawInt int16
		binary.Read(reader, binary.LittleEndian, &rawInt)

		s := float64(rawInt) / 32768.0

		// DC Offset Removal
		raw := s
		s = raw - 0.95*d.lastIn + 0.95*d.lastOut
		d.lastIn = raw
		d.lastOut = s

		// AGC
		d.agcPeak = 0.999*d.agcPeak + 0.001*math.Abs(s)
		g := 0.5 / (d.agcPeak + 0.01)
		if g > 20.0 {
			g = 20.0
		}
		if g < 0.1 {
			g = 0.1
		}
		d.agcGain = 0.995*d.agcGain + 0.005*g

		p := s * d.agcGain * d.squelchGate

		// Soft Limiter
		if p > 0.95 || p < -0.95 {
			if p > 3 {
				p = 1
			} else if p < -3 {
				p = -1
			} else {
				p = p - (p*p*p)/27
			}
		}
		if p > 0.99 {
			p = 0.99
		}
		if p < -0.99 {
			p = -0.99
		}

		outInt := int16(p * 32767)
		binary.Write(outBuf, binary.LittleEndian, outInt)

		sumSq += s * s
	}

	rms := math.Sqrt(sumSq / float64(numSamples))
	d.rms = 0.9*d.rms + 0.1*rms

	open := math.Max(0.002, sqThresh)
	closeVal := open * 0.8

	if d.rms > open {
		d.squelchGate = 1.0
	} else if d.rms < closeVal {
		d.squelchGate = 0.0
	}

	rssi := int16(math.Min(100, math.Floor(math.Sqrt(d.rms)*500)))

	return ProcessResult{
		Buffer: outBuf.Bytes(),
		RSSI:   rssi,
		IsOpen: d.squelchGate == 1.0,
	}
}

// ==========================================
// 4. システム & グローバル変数
// ==========================================

// SafeClient wraps websocket connection with a mutex to prevent concurrent writes
type SafeClient struct {
	Conn      *websocket.Conn
	mu        sync.Mutex
	DebugAuth bool // デバッグ情報閲覧権限
}

func (c *SafeClient) WriteMessage(messageType int, data []byte) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.Conn.WriteMessage(messageType, data)
}

func (c *SafeClient) WriteJSON(v interface{}) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.Conn.WriteJSON(v)
}

func (c *SafeClient) Close() error {
	return c.Conn.Close()
}

var (
	state = ServerState{
		Freq:        InitialFreq,
		Mode:        InitialMode,
		Title:       "",
		Att:         "off",
		Squelch:     10,
		IsRecording: false,
		Lat:         0.0,
		Lon:         0.0,
		Address:     "",
		GPSStatus:   "init",
		GPSUnlocked: false, // Default Locked
	}
	bookmarks []Bookmark
	bmMu      sync.Mutex
	squelchDB = make(map[string]int)

	clients   = make(map[*SafeClient]bool)
	broadcast = make(chan []byte)
	statusMsg = make(chan []byte)
	clientsMu sync.Mutex

	cmdChan = make(chan bool)

	recFile *os.File
	recMu   sync.Mutex

	upgrader = websocket.Upgrader{
		CheckOrigin: func(r *http.Request) bool { return true },
	}
)

// ==========================================
// 5. Discord Notification
// ==========================================

func sendDiscordNotification() {
	webhookURL := os.Getenv("DISCORD_WEBHOOK_URL")
	if webhookURL == "" {
		return
	}

	freqStr := fmt.Sprintf("%.3f MHz", float64(state.Freq)/1e6)

	payload := DiscordPayload{
		Username: "SDR Commander",
		Embeds: []DiscordEmbed{
			{
				Title:       "📡 System Started",
				Description: "SDR Web Receiver is online (Go Backend).",
				Color:       5814783, // Greenish
				Timestamp:   time.Now().Format(time.RFC3339),
				Fields: []DiscordEmbedField{
					{Name: "Initial Freq", Value: freqStr, Inline: true},
					{Name: "Mode", Value: state.Mode, Inline: true},
				},
			},
		},
	}

	jsonData, _ := json.Marshal(payload)
	resp, err := http.Post(webhookURL, "application/json", bytes.NewBuffer(jsonData))
	if err != nil {
		log.Println("Discord Notification Failed:", err)
		return
	}
	defer resp.Body.Close()
}

// ==========================================
// 6. SDR & GPS Manager
// ==========================================

// Reverse Geocoding via Nominatim
func reverseGeocode(lat, lon float64) string {
	url := fmt.Sprintf("https://nominatim.openstreetmap.org/reverse?format=json&lat=%f&lon=%f", lat, lon)
	req, err := http.NewRequest("GET", url, nil)
	if err != nil {
		return ""
	}

	// Nominatim requires User-Agent
	req.Header.Set("User-Agent", "SDR-Commander-Go/1.0")

	client := &http.Client{Timeout: 5 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return ""
	}
	defer resp.Body.Close()

	if resp.StatusCode != 200 {
		return ""
	}

	var data NominatimResponse
	if err := json.NewDecoder(resp.Body).Decode(&data); err != nil {
		return ""
	}

	return data.DisplayName
}

func parseNMEACoord(val, dir string) float64 {
	if len(val) < 4 {
		return 0.0
	}
	dot := strings.Index(val, ".")
	if dot == -1 {
		return 0.0
	}

	degStr := val[:dot-2]
	minStr := val[dot-2:]

	deg, _ := strconv.ParseFloat(degStr, 64)
	min, _ := strconv.ParseFloat(minStr, 64)

	res := deg + min/60.0
	if dir == "S" || dir == "W" {
		res = -res
	}
	return res
}

func gpsManager() {
	gpsPort := os.Getenv("GPS_PORT")
	if gpsPort == "" {
		gpsPort = "/dev/ttyUSB0"
	}

	gpsBaud := os.Getenv("GPS_BAUD_RATE")
	if gpsBaud == "" {
		gpsBaud = "38400"
	}

	// Track the last update time
	var lastUpdate time.Time

	for {
		// Configure serial port using stty (Linux/RPi specific)
		exec.Command("stty", "-F", gpsPort, gpsBaud, "raw", "-echo").Run()

		f, err := os.Open(gpsPort)
		if err != nil {
			state.mu.Lock()
			if state.GPSStatus != "disconnected" {
				state.GPSStatus = "disconnected"
				state.mu.Unlock()
				broadcastStatus()
			} else {
				state.mu.Unlock()
			}
			time.Sleep(5 * time.Second)
			continue
		}

		state.mu.Lock()
		if state.GPSStatus == "disconnected" || state.GPSStatus == "init" {
			state.GPSStatus = "searching"
			state.mu.Unlock()
			broadcastStatus()
		} else {
			state.mu.Unlock()
		}

		scanner := bufio.NewScanner(f)
		for scanner.Scan() {
			line := scanner.Text()

			// 1. アクティブユーザー確認 (Check for active listeners)
			clientsMu.Lock()
			hasListeners := len(clients) > 0
			clientsMu.Unlock()

			// ユーザーがいなければ処理をスキップ（読み捨て）
			if !hasListeners {
				continue
			}

			// 2. 15秒間隔チェック (Check 15s interval)
			if time.Since(lastUpdate) < 15*time.Second {
				continue
			}

			if strings.Contains(line, "GGA") {
				parts := strings.Split(line, ",")
				if len(parts) >= 10 {
					if parts[6] != "0" && len(parts[2]) > 0 && len(parts[4]) > 0 {
						lat := parseNMEACoord(parts[2], parts[3])
						lon := parseNMEACoord(parts[4], parts[5])

						// Update timestamp immediately after receiving valid data
						lastUpdate = time.Now()

						state.mu.Lock()
						updated := false
						if state.GPSStatus != "active" {
							state.GPSStatus = "active"
							updated = true
						}

						// Log to Standard Output
						fmt.Printf("[GPS] Update (15s) - Lat: %.6f, Lon: %.6f\n", lat, lon)

						// Significant change check for Address Lookup
						dist := math.Abs(state.Lat-lat) + math.Abs(state.Lon-lon)

						state.Lat = lat
						state.Lon = lon
						updated = true

						// Address Lookup - Only on significant moves to protect API quota
						if dist > 0.0001 {
							go func(la, lo float64) {
								addr := reverseGeocode(la, lo)
								if addr != "" {
									state.mu.Lock()
									state.Address = addr
									state.mu.Unlock()
									broadcastStatus()
									fmt.Printf("[GPS] Address Updated: %s\n", addr)
								}
							}(lat, lon)
						}
						state.mu.Unlock()

						if updated {
							broadcastStatus()
						}
					} else {
						state.mu.Lock()
						if state.GPSStatus == "active" {
							state.GPSStatus = "searching"
							state.mu.Unlock()
							broadcastStatus()
						} else {
							state.mu.Unlock()
						}
					}
				}
			}
		}
		f.Close()
		time.Sleep(1 * time.Second)
	}
}

func sdrManager() {
	var cmd *exec.Cmd
	var stdout io.ReadCloser
	dsp := NewAudioDSP()
	chunkSize := 4096
	buf := make([]byte, chunkSize)

	for {
		state.mu.Lock()
		freqStr := fmt.Sprintf("%d", state.Freq)
		mode := state.Mode
		att := state.Att
		ppm := "0"
		state.mu.Unlock()

		dsp.Reset()

		gainVal := "48"
		switch att {
		case "weak":
			gainVal = "29"
		case "mid":
			gainVal = "9"
		case "strong":
			gainVal = "0"
		}

		args := []string{"-f", freqStr, "-g", gainVal, "-p", ppm, "-F", "9"}
		if mode == "WFM" {
			args = append(args, "-M", "wbfm", "-s", "240000", "-r", fmt.Sprintf("%d", SampleRate))
		} else {
			rtlMode := "am"
			if mode == "FM" {
				rtlMode = "fm"
			}
			args = append(args, "-M", rtlMode, "-s", fmt.Sprintf("%d", SampleRate))
		}

		fmt.Printf("[Radio] Starting: rtl_fm %v\n", args)
		cmd = exec.Command("rtl_fm", args...)

		var err error
		stdout, err = cmd.StdoutPipe()
		if err != nil {
			log.Println("Error creating stdout pipe:", err)
			time.Sleep(1 * time.Second)
			continue
		}

		if err := cmd.Start(); err != nil {
			log.Println("Error starting rtl_fm:", err)
			time.Sleep(1 * time.Second)
			continue
		}

		done := make(chan error, 1)
		go func() {
			reader := bufio.NewReader(stdout)
			for {
				n, err := io.ReadFull(reader, buf)
				if err != nil {
					done <- err
					return
				}
				if n > 0 {
					state.mu.Lock()
					sq := state.Squelch
					state.mu.Unlock()

					res := dsp.Process(buf[:n], sq)

					header := new(bytes.Buffer)
					binary.Write(header, binary.LittleEndian, res.RSSI)
					isOpenInt := int16(0)
					if res.IsOpen {
						isOpenInt = 1
					}
					binary.Write(header, binary.LittleEndian, isOpenInt)

					packet := append(header.Bytes(), res.Buffer...)

					select {
					case broadcast <- packet:
					default:
					}

					recMu.Lock()
					if state.IsRecording && recFile != nil && res.IsOpen {
						recFile.Write(res.Buffer)
					}
					recMu.Unlock()
				}
			}
		}()

		select {
		case <-cmdChan:
			if cmd.Process != nil {
				cmd.Process.Kill()
			}
		case <-done:
		}

		cmd.Wait()
		time.Sleep(200 * time.Millisecond)
	}
}

// ==========================================
// 7. System Stats
// ==========================================

func getSystemStats() SystemStats {
	var s SystemStats

	// 1. CPU Temp
	if temp, err := os.ReadFile("/sys/class/thermal/thermal_zone0/temp"); err == nil {
		if t, err := strconv.ParseFloat(strings.TrimSpace(string(temp)), 64); err == nil {
			s.CPUTemp = t / 1000.0
		}
	}

	// 2. Memory Info
	if mem, err := os.ReadFile("/proc/meminfo"); err == nil {
		lines := strings.Split(string(mem), "\n")
		var total, free, buffers, cached uint64
		for _, line := range lines {
			fields := strings.Fields(line)
			if len(fields) < 2 {
				continue
			}
			val, _ := strconv.ParseUint(fields[1], 10, 64)
			switch strings.TrimSuffix(fields[0], ":") {
			case "MemTotal":
				total = val * 1024
			case "MemFree":
				free = val * 1024
			case "Buffers":
				buffers = val * 1024
			case "Cached":
				cached = val * 1024
			}
		}
		s.MemTotal = total
		s.MemUsed = total - (free + buffers + cached)
	}

	// 3. Disk Usage
	var stat syscall.Statfs_t
	if err := syscall.Statfs(RecordingsPath, &stat); err == nil {
		s.DiskTotal = stat.Blocks * uint64(stat.Bsize)
		s.DiskUsed = (stat.Blocks - stat.Bfree) * uint64(stat.Bsize)
	}

	// 4. Uptime
	if uptime, err := os.ReadFile("/proc/uptime"); err == nil {
		parts := strings.Fields(string(uptime))
		if len(parts) > 0 {
			if u, err := strconv.ParseFloat(parts[0], 64); err == nil {
				s.Uptime = uint64(u)
			}
		}
	}

	// 5. Load Average
	if loadavg, err := os.ReadFile("/proc/loadavg"); err == nil {
		fields := strings.Fields(string(loadavg))
		if len(fields) >= 3 {
			s.LoadAvg1, _ = strconv.ParseFloat(fields[0], 64)
			s.LoadAvg5, _ = strconv.ParseFloat(fields[1], 64)
			s.LoadAvg15, _ = strconv.ParseFloat(fields[2], 64)
		}
	}

	return s
}

func debugMonitor() {
	ticker := time.NewTicker(1 * time.Second)
	for range ticker.C {
		stats := getSystemStats()
		msg := map[string]interface{}{
			"type": "debug_info",
			"data": stats,
		}
		jsonBytes, _ := json.Marshal(msg)

		clientsMu.Lock()
		for client := range clients {
			if client.DebugAuth {
				client.WriteMessage(websocket.TextMessage, jsonBytes)
			}
		}
		clientsMu.Unlock()
	}
}

// ==========================================
// 8. Recording Logic
// ==========================================

func startRecording() {
	state.mu.Lock()
	// Do NOT use defer state.mu.Unlock() here to prevent deadlock with broadcastStatus
	if state.IsRecording {
		state.mu.Unlock()
		return
	}

	now := time.Now()
	// Folder: YYYY-MM-DD
	dateStr := now.Format("2006-01-02")
	// Folder: xxx.xxxMHz
	freqStr := fmt.Sprintf("%.3fMHz", float64(state.Freq)/1e6)

	// File Prefix: YYYY-MM-DD_hh-mm-ss
	timeStr := now.Format("2006-01-02_15-04-05")

	// ブックマーク名
	var titlePart string
	if state.Title != "" {
		// ファイル名に使用できない文字を置換
		safeTitle := state.Title
		replacer := strings.NewReplacer("/", "-", "\\", "-", ":", "-", "*", "-", "?", "-", "\"", "-", "<", "-", ">", "-", "|", "-")
		safeTitle = replacer.Replace(safeTitle)
		titlePart = "_" + safeTitle
	}

	// GPS情報
	var gpsInfo string
	if state.GPSUnlocked && (state.Lat != 0 || state.Lon != 0) {
		gpsInfo = fmt.Sprintf("_Lat%.4f_Lon%.4f", state.Lat, state.Lon)
	}

	// Create Directory Structure: recordings/YYYY-MM-DD/xxx.xxxMHz/
	dirPath := filepath.Join(RecordingsPath, dateStr, freqStr)
	if err := os.MkdirAll(dirPath, 0755); err != nil {
		log.Println("Mkdir error:", err)
		state.mu.Unlock()
		return
	}

	// File Name: YYYY-MM-DD_hh-mm-ss_Freq_Title_GPS.wav
	filename := fmt.Sprintf("%s_%s%s%s.wav", timeStr, freqStr, titlePart, gpsInfo)
	path := filepath.Join(dirPath, filename)

	f, err := os.Create(path)
	if err != nil {
		log.Println("Rec error:", err)
		state.mu.Unlock()
		return
	}

	writeWavHeader(f, SampleRate, 0)

	recMu.Lock()
	recFile = f
	recMu.Unlock()

	state.IsRecording = true
	state.RecFilename = path // Store full path for stopping later

	state.mu.Unlock()

	broadcastStatus()
}

func stopRecording() {
	state.mu.Lock()
	if !state.IsRecording {
		state.mu.Unlock()
		return
	}
	state.IsRecording = false
	state.mu.Unlock()

	recMu.Lock()
	defer recMu.Unlock()

	if recFile != nil {
		stat, _ := recFile.Stat()
		size := stat.Size()
		dataLen := uint32(size - 44)

		recFile.Seek(0, 0)
		writeWavHeader(recFile, SampleRate, dataLen)
		recFile.Close()
		recFile = nil
	}
	broadcastStatus()
	broadcastRecordings()
}

func writeWavHeader(w io.Writer, rate uint32, dataLen uint32) {
	buf := new(bytes.Buffer)
	buf.WriteString("RIFF")
	binary.Write(buf, binary.LittleEndian, uint32(36+dataLen))
	buf.WriteString("WAVEfmt ")
	binary.Write(buf, binary.LittleEndian, uint32(16))
	binary.Write(buf, binary.LittleEndian, uint16(1))
	binary.Write(buf, binary.LittleEndian, uint16(1))
	binary.Write(buf, binary.LittleEndian, rate)
	binary.Write(buf, binary.LittleEndian, rate*2)
	binary.Write(buf, binary.LittleEndian, uint16(2))
	binary.Write(buf, binary.LittleEndian, uint16(16))
	buf.WriteString("data")
	binary.Write(buf, binary.LittleEndian, dataLen)
	w.Write(buf.Bytes())
}

// ==========================================
// 9. Data Persistence
// ==========================================

func loadData() {
	if _, err := os.Stat(RecordingsPath); os.IsNotExist(err) {
		os.Mkdir(RecordingsPath, 0755)
	}

	bmMu.Lock()
	defer bmMu.Unlock()

	bData, err := os.ReadFile(BookmarksFile)
	if err == nil {
		json.Unmarshal(bData, &bookmarks)
	} else {
		bookmarks = []Bookmark{}
		saveBookmarksToFile()
	}

	sData, err := os.ReadFile(SquelchFile)
	if err == nil {
		json.Unmarshal(sData, &squelchDB)
	}
}

func saveBookmarksToFile() {
	d, _ := json.MarshalIndent(bookmarks, "", "  ")
	os.WriteFile(BookmarksFile, d, 0644)
}

func saveBookmarks() {
	bmMu.Lock()
	defer bmMu.Unlock()
	saveBookmarksToFile()
}

func saveSquelch() {
	d, _ := json.MarshalIndent(squelchDB, "", "  ")
	os.WriteFile(SquelchFile, d, 0644)
}

// ==========================================
// 10. WebSocket Handlers
// ==========================================

func isDescendant(checkID, potentialAncestorID string, all []Bookmark) bool {
	currentID := checkID
	for {
		if currentID == "" {
			return false
		}
		if currentID == potentialAncestorID {
			return true
		}

		parentID := ""
		found := false
		for _, b := range all {
			if b.ID == currentID {
				parentID = b.ParentID
				found = true
				break
			}
		}
		if !found {
			return false
		}
		currentID = parentID
	}
}

func broadcastStatus() {
	state.mu.Lock()
	defer state.mu.Unlock()

	clientsMu.Lock()
	connCount := len(clients)
	clientsMu.Unlock()

	var lat, lon float64
	var addr, gpsStatus string
	if state.GPSUnlocked {
		lat, lon = state.Lat, state.Lon
		addr = state.Address
		gpsStatus = state.GPSStatus
	} else {
		lat, lon = 0, 0
		addr = ""
		gpsStatus = "locked"
	}

	msg := map[string]interface{}{
		"type":        "status_update",
		"freq":        state.Freq,
		"mode":        state.Mode,
		"title":       state.Title,
		"att":         state.Att,
		"squelch":     state.Squelch,
		"isRecording": state.IsRecording,
		"connections": connCount,
		"lat":         lat,
		"lon":         lon,
		"address":     addr,
		"gpsStatus":   gpsStatus,
		"gpsUnlocked": state.GPSUnlocked,
	}
	bytes, _ := json.Marshal(msg)
	statusMsg <- bytes
}

func broadcastRecordings() {
	// Walk directories to build tree structure
	dateMap := make(map[string]map[string][]RecFileEntry)

	filepath.WalkDir(RecordingsPath, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return nil
		}
		if !d.IsDir() && strings.HasSuffix(d.Name(), ".wav") {
			rel, _ := filepath.Rel(RecordingsPath, path)
			parts := strings.Split(rel, string(os.PathSeparator))

			info, _ := d.Info()
			var date, freq string

			if len(parts) >= 3 {
				// 既にフォルダ分けされている場合: recordings/YYYY-MM-DD/xxx.xxxMHz/file.wav
				date = parts[0]
				freq = parts[1]
			} else {
				// ルートにあるファイルなどを解析して分類
				fname := d.Name()

				// 1. 日付の特定
				if len(fname) >= 10 && fname[4] == '-' && fname[7] == '-' {
					date = fname[:10]
				} else {
					date = info.ModTime().Format("2006-01-02")
				}

				// 2. 周波数の特定
				freq = "Unknown Freq"
				nameParts := strings.Split(fname, "_")
				for _, p := range nameParts {
					if strings.Contains(p, "MHz") {
						freq = p
						break
					}
				}
			}

			if dateMap[date] == nil {
				dateMap[date] = make(map[string][]RecFileEntry)
			}

			dateMap[date][freq] = append(dateMap[date][freq], RecFileEntry{
				Name: d.Name(),
				Path: rel, // 相対パス（ダウンロード・削除用）
				Size: info.Size(),
			})
		}
		return nil
	})

	// Convert map to sorted slice for JSON
	var dateList []RecDateEntry
	for date, freqMap := range dateMap {
		var freqList []RecFreqEntry
		for freq, files := range freqMap {
			// Sort files by name (time) asc
			sort.Slice(files, func(i, j int) bool { return files[i].Name < files[j].Name })
			freqList = append(freqList, RecFreqEntry{Freq: freq, Files: files})
		}
		// Sort freqs asc
		sort.Slice(freqList, func(i, j int) bool { return freqList[i].Freq < freqList[j].Freq })

		dateList = append(dateList, RecDateEntry{Date: date, Freqs: freqList})
	}
	// Sort dates desc (newest first)
	sort.Slice(dateList, func(i, j int) bool { return dateList[i].Date > dateList[j].Date })

	msg := map[string]interface{}{
		"type": "recordings",
		"data": dateList,
	}
	bytes, _ := json.Marshal(msg)
	statusMsg <- bytes
}

func handleMessages() {
	for {
		select {
		case audio := <-broadcast:
			clientsMu.Lock()
			for client := range clients {
				err := client.WriteMessage(websocket.BinaryMessage, audio)
				if err != nil {
					client.Close()
					delete(clients, client)
				}
			}
			clientsMu.Unlock()
		case msg := <-statusMsg:
			clientsMu.Lock()
			for client := range clients {
				client.WriteMessage(websocket.TextMessage, msg)
			}
			clientsMu.Unlock()
		}
	}
}

func checkAuthHash(envKey, inputPass string) bool {
	targetHash := os.Getenv(envKey)
	if targetHash == "" {
		return false
	}

	sum := sha256.Sum256([]byte(inputPass))
	inputHash := hex.EncodeToString(sum[:])
	return inputHash == targetHash
}

func wsHandler(w http.ResponseWriter, r *http.Request) {
	ws, err := upgrader.Upgrade(w, r, nil)
	if err != nil {
		return
	}

	client := &SafeClient{Conn: ws}

	clientsMu.Lock()
	clients[client] = true
	clientsMu.Unlock()

	broadcastStatus()

	bmMu.Lock()
	bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
	bmMu.Unlock()
	client.WriteMessage(websocket.TextMessage, bmMsg)

	broadcastRecordings()

	for {
		_, msg, err := ws.ReadMessage()
		if err != nil {
			clientsMu.Lock()
			delete(clients, client)
			clientsMu.Unlock()
			broadcastStatus()
			break
		}

		var cmd WSCommand
		if err := json.Unmarshal(msg, &cmd); err != nil {
			continue
		}

		switch cmd.Type {
		case "auth_tune":
			if checkAuthHash("TUNE_AUTH_HASH", cmd.Password) {
				state.mu.Lock()
				state.Freq = int(cmd.Freq)
				state.Mode = cmd.Mode
				state.Title = cmd.Title
				state.mu.Unlock()
				k := fmt.Sprintf("%d", int(cmd.Freq))
				if v, ok := squelchDB[k]; ok {
					state.mu.Lock()
					state.Squelch = v
					state.mu.Unlock()
				}
				go func() { cmdChan <- true }()
				broadcastStatus()
			}

		case "auth_gps":
			if checkAuthHash("GPS_AUTH_HASH", cmd.GPSPassword) {
				state.mu.Lock()
				state.GPSUnlocked = !state.GPSUnlocked
				state.mu.Unlock()
				broadcastStatus()
			}

		case "auth_debug":
			if checkAuthHash("DEBUG_AUTH_HASH", cmd.DebugPassword) {
				client.mu.Lock()
				client.DebugAuth = true
				client.mu.Unlock()
				client.WriteJSON(map[string]interface{}{"type": "debug_auth_success"})
			}

		case "set_att":
			state.mu.Lock()
			state.Att = cmd.Att
			state.mu.Unlock()
			go func() { cmdChan <- true }()
			broadcastStatus()
		case "set_squelch":
			state.mu.Lock()
			state.Squelch = cmd.Val
			state.mu.Unlock()
			squelchDB[fmt.Sprintf("%d", state.Freq)] = cmd.Val
			saveSquelch()
			broadcastStatus()
		case "start_recording":
			startRecording()
		case "stop_recording":
			stopRecording()
		case "delete_recording":
			if !checkAuthHash("DELETE_AUTH_HASH", cmd.DeletePassword) {
				client.WriteJSON(map[string]interface{}{"type": "error", "msg": "Invalid delete password"})
				break
			}
			// Filename is now a relative path
			// Prevent traversal
			if !strings.Contains(cmd.Filename, "..") {
				os.Remove(filepath.Join(RecordingsPath, cmd.Filename))
				// Check if dir is empty and remove it? (Optional, skipping for safety)
				broadcastRecordings()
			}

		case "add_bookmark":
			bmMu.Lock()
			var b Bookmark
			json.Unmarshal(cmd.Data, &b)
			b.ID = fmt.Sprintf("%d", time.Now().UnixMilli())
			bookmarks = append(bookmarks, b)
			saveBookmarksToFile()
			bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
			bmMu.Unlock()
			statusMsg <- bmMsg

		case "delete_bookmark":
			bmMu.Lock()
			newBM := []Bookmark{}
			for _, b := range bookmarks {
				if b.ID != cmd.ID && b.ParentID != cmd.ID {
					newBM = append(newBM, b)
				}
			}
			bookmarks = newBM
			saveBookmarksToFile()
			bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
			bmMu.Unlock()
			statusMsg <- bmMsg

		case "edit_bookmark":
			bmMu.Lock()
			var data Bookmark
			json.Unmarshal(cmd.Data, &data)
			for i, b := range bookmarks {
				if b.ID == data.ID {
					bookmarks[i].Title = data.Title
					if !data.IsFolder {
						bookmarks[i].Freq = data.Freq
						bookmarks[i].Mode = data.Mode
					}
					break
				}
			}
			saveBookmarksToFile()
			bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
			bmMu.Unlock()
			statusMsg <- bmMsg

		case "move_bookmark":
			bmMu.Lock()
			idx := -1
			for i, b := range bookmarks {
				if b.ID == cmd.ID {
					idx = i
					break
				}
			}
			if idx != -1 {
				target := bookmarks[idx]
				siblings := []int{}
				for i, b := range bookmarks {
					if b.ParentID == target.ParentID {
						siblings = append(siblings, i)
					}
				}

				sIdx := -1
				for i, globalIdx := range siblings {
					if globalIdx == idx {
						sIdx = i
						break
					}
				}

				if cmd.Dir == "up" && sIdx > 0 {
					swapIdx := siblings[sIdx-1]
					bookmarks[idx], bookmarks[swapIdx] = bookmarks[swapIdx], bookmarks[idx]
				} else if cmd.Dir == "down" && sIdx < len(siblings)-1 {
					swapIdx := siblings[sIdx+1]
					bookmarks[idx], bookmarks[swapIdx] = bookmarks[swapIdx], bookmarks[idx]
				}
				saveBookmarksToFile()
				bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
				statusMsg <- bmMsg
			}
			bmMu.Unlock()

		case "change_parent":
			bmMu.Lock()
			var target Bookmark
			for _, b := range bookmarks {
				if b.ID == cmd.ID {
					target = b
					break
				}
			}

			if target.IsFolder {
				if isDescendant(cmd.NewParentID, target.ID, bookmarks) {
					bmMu.Unlock()
					continue
				}
			}

			for i, b := range bookmarks {
				if b.ID == cmd.ID && b.ID != cmd.NewParentID {
					bookmarks[i].ParentID = cmd.NewParentID
					break
				}
			}
			saveBookmarksToFile()
			bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
			bmMu.Unlock()
			statusMsg <- bmMsg
		}
	}
}

// ==========================================
// 11. PWA & Main & HTML Content
// ==========================================

// PWA: Manifest JSON
const manifestContent = `{
  "name": "SDR COMMANDER",
  "short_name": "SDR Cmd",
  "start_url": "/",
  "display": "standalone",
  "background_color": "#050507",
  "theme_color": "#050507",
  "icons": [
    {
      "src": "/icons/icon-192.png",
      "sizes": "192x192",
      "type": "image/png"
    },
    {
      "src": "/icons/icon-512.png",
      "sizes": "512x512",
      "type": "image/png"
    }
  ]
}`

// PWA: Service Worker JS
const swContent = `
const CACHE_NAME = 'sdr-cmd-v1';
const ASSETS = [
  '/',
  '/manifest.json',
  '/icons/icon-192.png',
  '/icons/icon-512.png'
];

self.addEventListener('install', (e) => {
  e.waitUntil(
    caches.open(CACHE_NAME).then((cache) => cache.addAll(ASSETS))
  );
});

self.addEventListener('fetch', (e) => {
  const url = new URL(e.request.url);
  // Do not cache API/WS calls
  if (url.pathname.startsWith('/ws') || url.pathname.startsWith('/download/')) {
    return;
  }
  e.respondWith(
    caches.match(e.request).then((res) => res || fetch(e.request))
  );
});
`

// Helper to generate a dummy icon png
func generateIcon(w http.ResponseWriter, size int) {
	img := image.NewRGBA(image.Rect(0, 0, size, size))
	// Black background
	draw.Draw(img, img.Bounds(), &image.Uniform{color.RGBA{5, 5, 7, 255}}, image.Point{}, draw.Src)
	// Green accent box in middle
	draw.Draw(img, image.Rect(size/4, size/4, size*3/4, size*3/4), &image.Uniform{color.RGBA{0, 255, 200, 255}}, image.Point{}, draw.Src)

	w.Header().Set("Content-Type", "image/png")
	png.Encode(w, img)
}

func main() {
	flag.Parse()

	err := godotenv.Load()
	if err != nil {
		log.Println("Note: .env file not found, continuing without env vars")
	}

	loadData()

	// PWA Handlers
	http.HandleFunc("/manifest.json", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		w.Write([]byte(manifestContent))
	})
	http.HandleFunc("/service-worker.js", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/javascript")
		w.Write([]byte(swContent))
	})
	http.HandleFunc("/icons/", func(w http.ResponseWriter, r *http.Request) {
		if strings.Contains(r.URL.Path, "192") {
			generateIcon(w, 192)
		} else {
			generateIcon(w, 512)
		}
	})

	http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/" {
			w.Header().Set("Content-Type", "text/html")
			w.Write([]byte(htmlContent))
			return
		}
		if len(r.URL.Path) > 10 && r.URL.Path[:10] == "/download/" {
			// Support nested paths like /download/2023-10-27/128.000MHz/file.wav
			relPath := r.URL.Path[10:] // strip "/download/"
			// Check for traversal attempts
			if strings.Contains(relPath, "..") {
				http.NotFound(w, r)
				return
			}

			fpath := filepath.Join(RecordingsPath, relPath)
			if _, err := os.Stat(fpath); err == nil {
				w.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=\"%s\"", filepath.Base(fpath)))
				http.ServeFile(w, r, fpath)
				return
			}
		}
		http.NotFound(w, r)
	})

	http.HandleFunc("/ws", wsHandler)

	go sdrManager()
	go gpsManager()   // GPS
	go debugMonitor() // System Stats
	go handleMessages()

	go func() {
		time.Sleep(2 * time.Second)
		sendDiscordNotification()
	}()

	fmt.Printf("SDR Server (Go) running on http://localhost%s\n", Port)
	log.Fatal(http.ListenAndServe(Port, nil))
}

const htmlContent = `
<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
<meta name="theme-color" content="#050507">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<link rel="manifest" href="/manifest.json">
<link rel="apple-touch-icon" href="/icons/icon-192.png">
<title>SDR COMMANDER</title>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Inter:wght@400;600;800&family=JetBrains+Mono:wght@700&display=swap">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Material+Symbols+Outlined:opsz,wght,FILL,GRAD@24,400,0,0" />
<!-- Leaflet CSS -->
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css" integrity="sha256-p4NxAoJBhIIN+hmNHrzRCf9tD/miZyoHS5obTRR9BMY=" crossorigin=""/>
<style>
    :root { --bg: #050507; --panel: rgba(30, 30, 35, 0.7); --acc: #00ffc8; --acc-dim: rgba(0,255,200,0.15); --txt: #fff; --sub: #8b9bb4; --mute: #4a4a4a; --open: #00e676; --stop: #ff3b30; --warn: #ffcc00; }
    body { background: var(--bg); color: var(--txt); font-family: 'Inter', sans-serif; margin: 0; display: flex; justify-content: center; min-height: 100vh; user-select: none; -webkit-user-select: none; touch-action: manipulation; }
    .app { width: 100%; max-width: 480px; padding: 20px 20px 100px; box-sizing: border-box; padding-bottom: 150px; position: relative; }
    .panel { background: var(--panel); backdrop-filter: blur(12px); border-radius: 16px; border: 1px solid rgba(255,255,255,0.08); padding: 20px; margin-bottom: 16px; position: relative; }
    .freq { font-family: 'JetBrains Mono', monospace; font-size: 3.2rem; text-align: center; font-weight: 700; line-height: 1; text-shadow: 0 0 20px var(--acc-dim); margin: 5px 0 0 0; }
    .channel-title { font-family: 'Inter', sans-serif; font-size: 1.2rem; text-align: center; color: var(--acc); font-weight: 600; min-height: 1.5em; text-shadow: 0 0 10px rgba(0,255,200,0.3); margin-top: 10px; }
    .address-display { font-size: 0.8rem; text-align: center; color: var(--sub); margin-bottom: 5px; min-height: 1em; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
    .badges { display: flex; justify-content: center; gap: 8px; }
    .badge { font-size: 0.75rem; padding: 4px 10px; border-radius: 20px; background: rgba(255,255,255,0.05); color: var(--sub); border: 1px solid rgba(255,255,255,0.05); transition: 0.2s; }
    .badge-sql { background: var(--mute); color: #ccc; }
    .badge-sql.open { background: var(--open); color: #000; box-shadow: 0 0 10px var(--open); font-weight: bold; }
    /* Debug button integrated into badges row */
    .debug-badge { cursor: pointer; display: flex; align-items: center; justify-content: center; padding: 4px 8px; }
    .debug-badge:hover { background: rgba(255,255,255,0.1); }
    
    .meter-wrap { position: relative; height: 32px; margin-top: 15px; border: 1px solid rgba(255,255,255,0.1); border-radius: 6px; overflow: hidden; background: #111; }
    .meter-fill { height: 100%; width: 0%; background: var(--mute); transition: width 0.05s ease-out, background 0.1s; }
    .meter-fill.active { background: var(--open); box-shadow: 0 0 15px var(--open); }
    .sq-mark { position: absolute; top: 0; bottom: 0; width: 2px; background: #ffd700; z-index: 5; transition: left 0.1s; box-shadow: 0 0 8px #ffd700; }
    .sq-ctrl-row { display: flex; justify-content: space-between; align-items: center; margin-top: 15px; }
    .sq-val-display { font-family: 'JetBrains Mono', monospace; font-size: 1rem; color: #ffd700; font-weight: bold; margin-left: 5px; }
    .sq-btn-group { display: flex; gap: 4px; }
    .btn-sq { background: rgba(255,255,255,0.1); border: 1px solid rgba(255,255,255,0.1); color: var(--txt); padding: 8px 0; width: 36px; border-radius: 6px; font-size: 0.75rem; cursor: pointer; text-align: center; }
    .btn-sq:active { background: var(--acc); color: #000; border-color: var(--acc); }
    .ctrls { display: flex; flex-direction: column; gap: 12px; margin-bottom: 20px; }
    .btn-row { display: flex; gap: 8px; width: 100%; }
    .btn { flex: 1; background: rgba(255,255,255,0.05); border: 1px solid rgba(255,255,255,0.1); color: var(--txt); padding: 12px 8px; border-radius: 12px; font-weight: 600; cursor: pointer; display: flex; justify-content: center; align-items: center; gap: 6px; font-size: 0.75rem; transition: background 0.1s; white-space: nowrap; }
    .btn:active { background: rgba(255,255,255,0.15); transform: scale(0.98); }
    .btn.active { background: var(--acc-dim); border-color: var(--acc); color: var(--acc); }
    .btn-tune { background: linear-gradient(135deg, rgba(255,255,255,0.1), rgba(255,255,255,0.05)); font-size: 1rem; }
    .rec.on { background: #ff3b30; color: #fff; border-color: #ff3b30; animation: p 2s infinite; }
    @keyframes p { 0% {opacity:1} 50% {opacity:0.7} 100% {opacity:1} }
    .btn-audio-toggle { width: 100%; padding: 16px; background: rgba(0,255,200,0.15); border: 1px solid var(--acc); color: var(--acc); border-radius: 14px; font-weight: 800; font-size: 1rem; cursor: pointer; display: flex; justify-content: center; align-items: center; gap: 10px; transition: 0.2s; box-shadow: 0 0 15px rgba(0,255,200,0.1); margin-bottom: 5px; }
    .btn-audio-toggle.stop { background: rgba(255, 59, 48, 0.15); border-color: var(--stop); color: var(--stop); box-shadow: 0 0 15px rgba(255, 59, 48, 0.1); }
    .btn-audio-toggle:active { transform: scale(0.98); }
    .section-header { display: flex; justify-content: space-between; align-items: center; margin: 24px 4px 8px 4px; }
    .section-title { font-size: 0.8rem; text-transform: uppercase; letter-spacing: 1px; color: var(--sub); }
    .btn-edit-toggle { background: transparent; border: 1px solid var(--sub); color: var(--sub); padding: 4px 12px; border-radius: 6px; font-size: 0.75rem; cursor: pointer; transition: 0.2s; }
    .btn-edit-toggle.editing { background: var(--warn); color: #000; border-color: var(--warn); font-weight: bold; }
    .edit-controls { display: none; gap: 8px; }
    .edit-controls.show { display: flex; }
    .btn-add { background: var(--acc-dim); border: 1px solid var(--acc); color: var(--acc); padding: 4px 10px; border-radius: 6px; font-size: 0.75rem; font-weight: bold; cursor: pointer; }
    .tree { display: flex; flex-direction: column; gap: 2px; }
    .panel.edit-mode { border-color: var(--warn); background: rgba(255, 204, 0, 0.05); }
    .panel.edit-mode .row { cursor: default; }
    .row { display: flex; align-items: center; padding: 12px; background: rgba(255,255,255,0.02); border-radius: 8px; cursor: pointer; justify-content: space-between; transition: background 0.1s; }
    .row:hover { background: rgba(255,255,255,0.05); }
    .row-click-area { display: flex; align-items: center; flex: 1; height: 100%; } 
    .folder-c { margin-left: 10px; border-left: 2px solid rgba(255,255,255,0.1); padding-left: 10px; display: none; }
    .folder-c.open { display: block; }
    .icon { color: var(--sub); font-size: 1.2rem; transition: transform 0.2s; }
    .icon.rot { transform: rotate(90deg); }
    .txt { display: flex; flex-direction: column; }
    .sub { font-size: 0.8rem; color: var(--sub); }
    .act { display: flex; gap: 4px; }
    .ib { background: transparent; border: none; color: var(--sub); padding: 8px; cursor: pointer; border-radius: 50%; z-index: 10; display:flex; align-items:center; justify-content:center; }
    .ib:hover { color: var(--txt); background: rgba(255,255,255,0.1); }
    .ib-move { color: var(--warn); }
    .ib-del { color: var(--stop); }
    .ovl { position: fixed; top:0; left:0; width:100%; height:100%; background:rgba(0,0,0,0.8); backdrop-filter:blur(8px); display:none; justify-content:center; align-items:center; z-index: 1000; }
    .card { background: #1a1b20; width:90%; max-width:400px; padding:30px; border-radius:24px; box-shadow: 0 10px 40px #000; animation: pop 0.2s cubic-bezier(0.175, 0.885, 0.32, 1.275); }
    @keyframes pop { from{transform:scale(0.9); opacity:0} to{transform:scale(1); opacity:1} }
    .inp { width:100%; background:#27282e; border:none; padding:16px; border-radius:12px; color:#fff; font-size:1.2rem; margin-bottom:15px; box-sizing:border-box; outline:none; }
    .inp:focus { outline: 2px solid var(--acc); }
    .move-item { padding: 12px; background: rgba(255,255,255,0.05); border-radius: 8px; cursor: pointer; display: flex; align-items: center; transition: 0.2s; }
    .move-item:hover { background: rgba(255,255,255,0.1); }
    .move-item.selected { background: var(--acc-dim); border: 1px solid var(--acc); color: var(--acc); }
    
    /* Map Styles */
    #map { width: 100%; height: 200px; border-radius: 12px; margin-top: 12px; border: 1px solid rgba(255,255,255,0.1); background: #222; }
    .leaflet-tile { filter: grayscale(100%) invert(100%) contrast(0.8); }
    .leaflet-bar a { background-color: var(--panel) !important; color: var(--txt) !important; border-bottom: 1px solid rgba(255,255,255,0.2) !important; }
    .map-container { position: relative; width: 100%; height: 200px; margin-top: 12px; border-radius: 12px; overflow: hidden; border: 1px solid rgba(255,255,255,0.1); display: none; }
    #map { width: 100%; height: 100%; margin: 0; border: none; }
    .map-overlay {
        position: absolute; top: 0; left: 0; width: 100%; height: 100%;
        background: rgba(0,0,0,0.7); color: #fff; display: flex;
        justify-content: center; align-items: center; z-index: 1000;
        backdrop-filter: blur(2px); font-weight: bold; flex-direction: column; gap:10px;
    }
    .btn-unlock { background: var(--acc); color:#000; font-weight:bold; padding:8px 16px; border-radius:8px; border:none; cursor:pointer; }

    /* Debug Styles */
    .debug-panel { position: fixed; bottom: 0; left: 0; right: 0; background: rgba(10,10,12,0.95); padding: 15px; border-top: 1px solid #333; font-family: 'JetBrains Mono', monospace; font-size: 0.75rem; color: #aaa; z-index: 2000; display: none; justify-content: space-around; flex-wrap: wrap; }
    .debug-item { text-align: center; margin: 5px; }
    .debug-val { font-size: 1.0rem; color: #fff; font-weight: bold; }
    
    /* Version Tag */
    .ver-tag { position: absolute; top: 10px; right: 10px; font-size: 0.7rem; color: rgba(255,255,255,0.3); font-family: 'JetBrains Mono', monospace; pointer-events: none; }
</style>
<!-- Leaflet JS -->
<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js" integrity="sha256-20nQCchB9co0qIjJZRGuk2/Z9VM+kNiyxNV1lvTlZBo=" crossorigin=""></script>
</head>
<body>

    <div class="app">
        <div class="ver-tag">v2.1 (iOS Fix)</div>
        <div class="panel">
            <div class="badges">
                <span class="badge" id="bdgMode">AM</span>
                <span class="badge" id="bdgAtt" style="display:none">ATT</span>
                <span class="badge badge-sql" id="bdgSql">MUTED</span>
                <span class="badge" id="bdgConn">👤 0</span>
                <!-- Debug Badge Button -->
                <button class="badge debug-badge" onclick="window.ui.toggleDebug()" title="Debug Stats">
                    <span class="material-symbols-outlined" style="font-size: 0.9rem;">bug_report</span>
                </button>
            </div>
            <div class="channel-title" id="dspTitle"></div>
            <div class="freq" id="dspFreq">---.---</div>
            <div class="address-display" id="dspAddr"></div>
            
            <div class="meter-wrap">
                <div class="meter-fill" id="dspRssi"></div>
                <div class="sq-mark" id="sqMarker" style="left:10%"></div>
            </div>
            <div class="sq-ctrl-row">
                <div style="font-size:0.8rem; color:var(--sub);">AUDIO LEVEL > <span id="valSq" class="sq-val-display">10</span></div>
                <div class="sq-btn-group">
                    <button class="btn-sq" onclick="window.ui.adjSq(-10)">-10</button>
                    <button class="btn-sq" onclick="window.ui.adjSq(-5)">-5</button>
                    <button class="btn-sq" onclick="window.ui.adjSq(-1)">-1</button>
                    <button class="btn-sq" onclick="window.ui.adjSq(1)">+1</button>
                    <button class="btn-sq" onclick="window.ui.adjSq(5)">+5</button>
                    <button class="btn-sq" onclick="window.ui.adjSq(10)">+10</button>
                </div>
            </div>
            
            <!-- Map Container starts hidden -->
            <button id="btnGPSAuth" class="btn" style="margin-top:10px; width:100%" onclick="window.ui.modal('auth_gps')">UNLOCK MAP & GPS</button>
            
            <div class="map-container" id="mapContainer">
                <div id="map"></div>
                <div id="mapMsg" class="map-overlay"></div>
            </div>
        </div>

        <!-- Controls etc... -->
        <div class="ctrls">
            <button class="btn-audio-toggle" id="btnAudio" onclick="window.ui.togAudio()">
                <span class="material-symbols-outlined">volume_up</span> START LISTENING
            </button>
            <div class="btn-row">
                <button class="btn btn-tune" style="flex:2" onclick="window.ui.modal('tune')"><span class="material-symbols-outlined">dialpad</span> TUNE</button>
                <button class="btn" id="btnRec" style="flex:1" onclick="window.ws.togRec()"><span class="material-symbols-outlined">fiber_manual_record</span> REC</button>
            </div>
            <div class="btn-row">
                <button class="btn active" id="attOff" onclick="window.ws.setAtt('off')">NO ATT</button>
                <button class="btn" id="attWeak" onclick="window.ws.setAtt('weak')">WEAK</button>
                <button class="btn" id="attMid" onclick="window.ws.setAtt('mid')">MID</button>
                <button class="btn" id="attStrong" onclick="window.ws.setAtt('strong')">STRONG</button>
            </div>
        </div>

        <div class="section-header">
            <span class="section-title">CHANNELS</span>
            <div style="display:flex; gap:8px; align-items:center;">
                <button id="btnEditToggle" class="btn-edit-toggle" onclick="window.ui.togEdit()">EDIT</button>
                <div id="addBtns" class="edit-controls">
                    <button class="btn-add" onclick="window.ui.modal('add_folder')">+ FOLDER</button>
                    <button class="btn-add" onclick="window.ui.modal('add_freq')">+ FREQ</button>
                </div>
            </div>
        </div>
        
        <div class="panel" id="listBM" style="padding:10px;"></div>
        <div class="section-header"><span class="section-title">RECORDINGS</span></div>
        <div class="panel" id="listRec" style="padding:10px;"></div>
    </div>

    <!-- Debug Panel -->
    <div id="debugPanel" class="debug-panel">
        <div class="debug-item">
            <div class="debug-val" id="dbgTemp">--°C</div>
            <div>CPU TEMP</div>
        </div>
        <div class="debug-item">
            <div class="debug-val" id="dbgLoad1">--</div>
            <div>LOAD 1m</div>
        </div>
        <div class="debug-item">
            <div class="debug-val" id="dbgLoad5">--</div>
            <div>LOAD 5m</div>
        </div>
        <div class="debug-item">
            <div class="debug-val" id="dbgLoad15">--</div>
            <div>LOAD 15m</div>
        </div>
        <div class="debug-item">
            <div class="debug-val" id="dbgMem">--%</div>
            <div>MEM</div>
        </div>
        <div class="debug-item">
            <div class="debug-val" id="dbgDisk">--%</div>
            <div>DISK</div>
        </div>
    </div>

    <!-- Modals -->
    <div class="ovl" id="modalTune">
        <div class="card">
            <div style="color:#fff; font-weight:700; font-size:1.2rem; margin-bottom:20px;">Set Frequency</div>
            <input type="number" class="inp" id="inpFreq" placeholder="128.800" step="0.001">
            <div style="display:flex; gap:10px; margin-bottom:15px;">
                <button class="btn" id="modAM" onclick="window.ui.selMod('AM')">AM</button>
                <button class="btn" id="modFM" onclick="window.ui.selMod('FM')">FM</button>
                <button class="btn" id="modWFM" onclick="window.ui.selMod('WFM')">WFM</button>
            </div>
            <input type="password" class="inp" id="inpPass" placeholder="Password (required)">
            <div style="display:flex; gap:10px;">
                <button class="btn" style="flex:1" onclick="window.ui.closeModal()">CANCEL</button>
                <button class="btn" style="flex:1; background:var(--acc); color:#000;" onclick="window.ws.tune()">TUNE</button>
            </div>
        </div>
    </div>

    <div class="ovl" id="modalGPSAuth">
        <div class="card">
            <div id="gpsModalTitle" style="color:#fff; font-weight:700; font-size:1.2rem; margin-bottom:20px;">Unlock GPS</div>
            <p id="gpsModalDesc" style="color:var(--sub); margin-bottom:20px">Enter password to enable GPS tracking for all users.</p>
            <input type="password" class="inp" id="inpGPSPass" placeholder="GPS Password">
            <div style="display:flex; gap:10px;">
                <button class="btn" style="flex:1" onclick="window.ui.closeModal()">CANCEL</button>
                <button id="btnGPSModalAction" class="btn" style="flex:1; background:var(--acc); color:#000;" onclick="window.ws.authGPS()">UNLOCK</button>
            </div>
        </div>
    </div>

    <div class="ovl" id="modalDebugAuth">
        <div class="card">
            <div style="color:#fff; font-weight:700; font-size:1.2rem; margin-bottom:20px;">Debug Mode</div>
            <p style="color:var(--sub); margin-bottom:20px">Enter password to view system stats.</p>
            <input type="password" class="inp" id="inpDebugPass" placeholder="Debug Password">
            <div style="display:flex; gap:10px;">
                <button class="btn" style="flex:1" onclick="window.ui.closeModal()">CANCEL</button>
                <button class="btn" style="flex:1; background:var(--acc); color:#000;" onclick="window.ws.authDebug()">AUTH</button>
            </div>
        </div>
    </div>
    
    <div class="ovl" id="modalDeleteAuth">
        <div class="card">
            <div style="color:#ff3b30; font-weight:700; font-size:1.2rem; margin-bottom:20px;">Delete Recording</div>
            <p style="color:var(--sub); margin-bottom:20px">Enter password to delete this file.</p>
            <input type="password" class="inp" id="inpDeletePass" placeholder="Delete Password">
            <div style="display:flex; gap:10px;">
                <button class="btn" style="flex:1" onclick="window.ui.closeModal()">CANCEL</button>
                <button class="btn" style="flex:1; background:var(--stop); color:#fff;" onclick="window.ws.execDel()">DELETE</button>
            </div>
        </div>
    </div>

    <div class="ovl" id="modalAdd">
        <div class="card">
            <div style="color:#fff; font-weight:700; font-size:1.2rem; margin-bottom:20px;" id="addTitle">Add Channel</div>
            <input type="text" class="inp" id="addName" placeholder="Name">
            <div id="addFreqGroup">
                <input type="number" class="inp" id="addFreq" placeholder="Frequency (MHz)">
                <div style="display:flex; gap:10px; margin-bottom:15px;">
                    <button class="btn" id="addModAM" onclick="window.ui.selAddMod('AM')">AM</button>
                    <button class="btn" id="addModFM" onclick="window.ui.selAddMod('FM')">FM</button>
                    <button class="btn" id="addModWFM" onclick="window.ui.selAddMod('WFM')">WFM</button>
                </div>
            </div>
            <div style="display:flex; gap:10px;">
                <button class="btn" style="flex:1" onclick="window.ui.closeModal()">CANCEL</button>
                <button class="btn" style="flex:1; background:var(--acc); color:#000;" onclick="window.ws.saveBookmark()">SAVE</button>
            </div>
        </div>
    </div>

    <div class="ovl" id="modalMove">
        <div class="card">
            <div style="color:#fff; font-weight:700; font-size:1.2rem; margin-bottom:20px;">Move to Folder</div>
            <div id="moveFolderList" style="max-height:300px; overflow-y:auto; display:flex; flex-direction:column; gap:8px;"></div>
            <div style="display:flex; gap:10px; margin-top:20px;">
                <button class="btn" style="flex:1" onclick="window.ui.closeModal()">CANCEL</button>
            </div>
        </div>
    </div>

    <!-- iOS Fix: Audio Bridge with NO Loop (Fix stutter) -->
    <audio id="audioBridge" autoplay playsinline x-webkit-airplay="allow" style="opacity:0; pointer-events:none; position:absolute; left:-9999px;"></audio>

<script>
    // iOS Background Fix v2.1
    // Implements robust audio scheduling, silence injection, and aggressive wake-lock strategies.

    if ('serviceWorker' in navigator) {
        window.addEventListener('load', () => {
            navigator.serviceWorker.register('/service-worker.js').catch(()=>{});
        });
    }

    let audioCtx;
    let audioQueue = [];
    let isPlaying = false;
    let schedulerTimer = null;
    let nextStartTime = 0; 
    let silenceNode = null;
    let noiseNode = null; // Comfort noise to keep driver alive
    
    // Config
    const SCHEDULE_AHEAD_TIME = 0.1; // Schedule 100ms ahead
    const LOOKAHEAD_MS = 25; // Check every 25ms
    const IOS_BG_BUFFER = 0.5; // Extra buffer for iOS background

    // WebSocket Definition
    window.ws = {
        c: null,
        connect() {
            const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
            this.c = new WebSocket(proto + '//' + location.host + '/ws');
            this.c.binaryType = 'arraybuffer';
            this.c.onmessage = e => {
                if(typeof e.data === 'string') {
                    const m = JSON.parse(e.data);
                    if(m.type==='status_update') window.ui.upd(m);
                    else if(m.type==='bookmarks') { window.ui.state.bm = m.data; window.ui.renderBM(); }
                    else if(m.type==='recordings') window.ui.renderRec(m.data);
                    else if(m.type==='debug_info') window.ui.updDebug(m.data);
                    else if(m.type==='debug_auth_success') {
                          window.ui.closeModal();
                          document.getElementById('debugPanel').style.display = 'flex';
                      }
                    else if(m.type==='error') alert(m.msg);
                } else {
                    this.queueAudio(e.data);
                }
            };
            this.c.onclose = () => setTimeout(()=>this.connect(), 3000);
        },
        send(o) { if(this.c&&this.c.readyState===1) this.c.send(JSON.stringify(o)); },
        sendSq(v) { this.send({type:'set_squelch', val:parseInt(v)}); },
        setMode(m) { window.ui.state.mode=m; this.tune(true); },
        setAtt(a) { this.send({type:'set_att', att:a}); },
        togRec() { this.send({type:window.ui.state.rec?'stop_recording':'start_recording'}); },
        move(id, dir) { this.send({type:'move_bookmark', id, dir}); },
        changeParent(pid) {
            if (window.ui.state.moveTargetId) {
                this.send({type:'change_parent', id:window.ui.state.moveTargetId, newParentId:pid});
                window.ui.closeModal();
            }
        },
        tune(skip=false) {
            let f = window.ui.state.freq;
            const m = window.ui.modalMode; 
            if(!skip) { const v = parseFloat(document.getElementById('inpFreq').value); if(v) f = Math.floor(v*1e6); }
            const p = document.getElementById('inpPass').value;
            this.send({type:'auth_tune', password:p, freq:f, mode:m, title:''});
            window.ui.closeModal();
        },
        tuneDir(f, m, t) {
            const p = document.getElementById('inpPass').value;
            if (!p) {
                window.ui.state.freq = Math.floor(f*1e6);
                window.ui.state.mode = m;
                document.getElementById('inpFreq').value = f.toFixed(3);
                window.ui.selMod(m);
                window.ui.modal('tune');
                return;
            }
            this.send({type:'auth_tune', password:p, freq:Math.floor(f*1e6), mode:m, title:t});
            window.ui.state.mode = m;
        },
        authGPS() {
            const p = document.getElementById('inpGPSPass').value;
            this.send({type:'auth_gps', gpsPassword:p});
            window.ui.closeModal();
        },
        authDebug() {
            const p = document.getElementById('inpDebugPass').value;
            this.send({type:'auth_debug', debugPassword:p});
        },
        saveBookmark() {
            const title = document.getElementById('addName').value;
            if (!title) return;
            const isFolder = (window.ui.addType === 'folder');
            
            if (window.ui.state.editTargetId) {
                const data = { id: window.ui.state.editTargetId, title, isFolder };
                if (!isFolder) {
                    const freqVal = parseFloat(document.getElementById('addFreq').value);
                    if (!freqVal) return;
                    data.freq = freqVal;
                    data.mode = window.ui.addMode;
                }
                this.send({type:'edit_bookmark', data: data});
            } else {
                const data = { title, isFolder, parentId: window.ui.targetParent };
                if (!isFolder) {
                    const freqVal = parseFloat(document.getElementById('addFreq').value);
                    if (!freqVal) return;
                    data.freq = freqVal;
                    data.mode = window.ui.addMode;
                }
                this.send({type:'add_bookmark', data: data});
            }
            window.ui.closeModal();
        },
        delRec(path) {
            window.ui.state.deleteTarget = path;
            window.ui.modal('auth_delete');
        },
        execDel() {
            const p = document.getElementById('inpDeletePass').value;
            if(!window.ui.state.deleteTarget) return;
            this.send({type:'delete_recording', filename:window.ui.state.deleteTarget, deletePassword:p});
            window.ui.closeModal();
            document.getElementById('inpDeletePass').value = ''; // clear
        },
        
        // --- NEW AUDIO PIPELINE ---
        queueAudio(b) {
            if(!audioCtx || !isPlaying) return;
            
            // Extract Signal Info
            const dv = new DataView(b);
            const rssi = dv.getInt16(0, true);
            const sqlOpen = dv.getInt16(2, true);
            
            // Update UI immediately (visuals don't need audio sync)
            requestAnimationFrame(() => {
                const bar = document.getElementById('dspRssi');
                if(bar) {
                    bar.style.width = Math.min(100, (rssi/200)*100)+'%';
                    if(sqlOpen) bar.classList.add('active'); else bar.classList.remove('active');
                }
                const bdgSql = document.getElementById('bdgSql');
                if(bdgSql) {
                    if (sqlOpen) { bdgSql.innerText = 'SQL OPEN'; bdgSql.className = 'badge badge-sql open'; } 
                    else { bdgSql.innerText = 'MUTED'; bdgSql.className = 'badge badge-sql'; }
                }
            });

            // Decode PCM
            const f = new Float32Array((b.byteLength - 4) / 2);
            const s16 = new Int16Array(b, 4);
            for(let i=0; i<f.length; i++) f[i] = s16[i]/32768.0;

            audioQueue.push(f);
        }
    };

    // --- ROBUST AUDIO SCHEDULER ---
    function audioScheduler() {
        if (!audioCtx || !isPlaying) return;

        const currentTime = audioCtx.currentTime;
        
        // Logic: If nextStartTime is behind currentTime, we are underrunning (stutter risk).
        // On iOS background, this happens often. We MUST jump ahead.
        // If we are way behind (>0.5s), reset the clock entirely.
        if (nextStartTime < currentTime) {
            nextStartTime = currentTime + 0.01; // Catch up
        }

        // Schedule chunks until we are sufficiently ahead
        while (audioQueue.length > 0 && nextStartTime < currentTime + SCHEDULE_AHEAD_TIME) {
            const pcm = audioQueue.shift();
            const buf = audioCtx.createBuffer(1, pcm.length, 48000);
            buf.getChannelData(0).set(pcm);
            
            const src = audioCtx.createBufferSource();
            src.buffer = buf;
            
            // Always route to MediaStreamDestination for iOS background support
            if (window.audioDest) {
                src.connect(window.audioDest);
            } else {
                src.connect(audioCtx.destination);
            }
            
            src.start(nextStartTime);
            nextStartTime += buf.duration;
        }
        
        // --- SILENCE INJECTION (Anti-Loop) ---
        // If the queue is empty but we are running out of scheduled audio,
        // the hardware driver might loop the last buffer.
        // We preemptively schedule a silent buffer to keep the driver fed.
        if (audioQueue.length === 0 && nextStartTime < currentTime + 0.2) {
             const silentBuf = audioCtx.createBuffer(1, 1024, 48000); // Small silent chunk
             const silentSrc = audioCtx.createBufferSource();
             silentSrc.buffer = silentBuf;
             if (window.audioDest) silentSrc.connect(window.audioDest);
             else silentSrc.connect(audioCtx.destination);
             silentSrc.start(nextStartTime);
             nextStartTime += silentBuf.duration;
        }
    }

    // UI Definition
    window.ui = {
        state: { freq:0, mode:'AM', att:'off', rec:false, bm:[], expanded:new Set(), squelch: 10, editTargetId: null, editMode: false, moveTargetId: null, gpsUnlocked: false, deleteTarget: null },
        modalMode: 'AM',
        addMode: 'AM',
        targetParent: null,
        addType: 'freq',

        init() {
            if (window.ws) { window.ws.connect(); } 
            
            // Map Init
            if (document.getElementById('map')) {
                map = L.map('map').setView([35.6895, 139.6917], 13);
                L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
                    attribution: '&copy; OSM'
                }).addTo(map);
                marker = L.marker([35.6895, 139.6917]).addTo(map);
                setTimeout(() => map.invalidateSize(), 100);
            }
            
            // Visibility Handler: Force resume
            document.addEventListener('visibilitychange', () => {
                if (document.visibilityState === 'visible') {
                    // Sync up when returning
                    if(audioCtx) nextStartTime = audioCtx.currentTime + 0.1;
                }
            });
            
            // Media Session
            if ('mediaSession' in navigator) {
                const ms = navigator.mediaSession;
                ms.setActionHandler('play', () => this.togAudio());
                ms.setActionHandler('pause', () => this.togAudio());
                ms.setActionHandler('stop', () => this.togAudio());
            }
        },

        // --- CORE AUDIO STARTUP ---
        async togAudio() {
            const btn = document.getElementById('btnAudio');
            
            if (!audioCtx) {
                // 1. Create Context
                const Ctx = window.AudioContext || window.webkitAudioContext;
                audioCtx = new Ctx({ latencyHint: 'playback', sampleRate: 48000 });
                
                // 2. Setup Destination for <audio> tag (The Bridge)
                const dest = audioCtx.createMediaStreamDestination();
                window.audioDest = dest;
                
                const audioEl = document.getElementById('audioBridge');
                audioEl.srcObject = dest.stream;
                
                // 3. Setup Comfort Noise (Anti-suspend)
                // This plays faint noise continuously to prevent the OS from killing the audio thread
                noiseNode = audioCtx.createBufferSource();
                const noiseBuf = audioCtx.createBuffer(1, 48000, 48000);
                const noiseData = noiseBuf.getChannelData(0);
                for (let i = 0; i < 48000; i++) noiseData[i] = (Math.random() - 0.5) * 0.002; // Very quiet
                noiseNode.buffer = noiseBuf;
                noiseNode.loop = true;
                noiseNode.connect(dest); // Connect to output
                noiseNode.start(0);

                // 4. Force iOS to unlock audio by playing a buffer right now (inside click event)
                const unlockBuf = audioCtx.createBuffer(1, 1, 48000);
                const unlockSrc = audioCtx.createBufferSource();
                unlockSrc.buffer = unlockBuf;
                unlockSrc.connect(dest);
                unlockSrc.start(0);

                // 5. Start the <audio> tag
                try {
                    await audioEl.play();
                } catch(e) { console.error("Audio tag play failed", e); }

                // 6. Start Scheduler Loop
                // Using setInterval is usually bad for audio, but strictly necessary for 
                // Web Audio API on iOS background if not using AudioWorklet (which needs external file).
                // The ScriptProcessor hack is another way, but we use interval + buffer queue here.
                if (schedulerTimer) clearInterval(schedulerTimer);
                schedulerTimer = setInterval(audioScheduler, LOOKAHEAD_MS);
                
                isPlaying = true;
                this.updateBtnState('running');
                this.updateMediaMetadata();
                return;
            }

            if (isPlaying) {
                // Stop
                await audioCtx.suspend();
                document.getElementById('audioBridge').pause();
                isPlaying = false;
                if(noiseNode) { try{noiseNode.stop();}catch(e){} noiseNode=null; } // Stop noise
                if(schedulerTimer) clearInterval(schedulerTimer);
                this.updateBtnState('suspended');
                if('mediaSession' in navigator) navigator.mediaSession.playbackState = 'paused';
            } else {
                // Resume
                await audioCtx.resume();
                document.getElementById('audioBridge').play();
                
                // Restart noise if missing
                if(!noiseNode) {
                    noiseNode = audioCtx.createBufferSource();
                    const noiseBuf = audioCtx.createBuffer(1, 48000, 48000);
                    const d = noiseBuf.getChannelData(0);
                    for(let i=0; i<48000; i++) d[i] = (Math.random()-0.5)*0.002;
                    noiseNode.buffer = noiseBuf;
                    noiseNode.loop = true;
                    noiseNode.connect(window.audioDest);
                    noiseNode.start(0);
                }
                
                isPlaying = true;
                nextStartTime = audioCtx.currentTime + 0.1;
                schedulerTimer = setInterval(audioScheduler, LOOKAHEAD_MS);
                this.updateBtnState('running');
                this.updateMediaMetadata();
            }
        },

        updateBtnState(s) {
            const btn = document.getElementById('btnAudio');
            if (s === 'running') {
                btn.innerHTML = '<span class="material-symbols-outlined">volume_off</span> STOP LISTENING';
                btn.className = 'btn-audio-toggle stop';
            } else {
                btn.innerHTML = '<span class="material-symbols-outlined">volume_up</span> START LISTENING';
                btn.className = 'btn-audio-toggle';
            }
        },
        
        updateMediaMetadata() {
            if (!('mediaSession' in navigator) || !audioCtx || !isPlaying) return;
            navigator.mediaSession.playbackState = 'playing';
            
            const titleStr = this.state.title ? this.state.title : (this.state.freq/1e6).toFixed(3) + ' MHz';
            const artistStr = this.state.mode + ' | SQL: ' + this.state.squelch + ' | ' + (this.state.rec ? '● REC' : 'LIVE');
            
            navigator.mediaSession.metadata = new MediaMetadata({
                title: titleStr,
                artist: artistStr,
                album: 'SDR Commander',
                artwork: [
                    { src: '/icons/icon-512.png', sizes: '512x512', type: 'image/png' },
                    { src: '/icons/icon-192.png', sizes: '192x192', type: 'image/png' }
                ]
            });
        },

        upd(m) {
            const prevFreq = this.state.freq;
            const prevRec = this.state.rec;

            this.state.freq=m.freq; this.state.mode=m.mode; this.state.att=m.att; this.state.rec=m.isRecording; this.state.squelch=m.squelch;
            this.state.title=m.title;
            this.state.gpsUnlocked = m.gpsUnlocked;
            
            document.getElementById('dspFreq').innerText = (m.freq/1e6).toFixed(3);
            document.getElementById('dspTitle').innerText = m.title || '';
            document.getElementById('bdgMode').innerText = m.mode;
            document.getElementById('bdgAtt').style.display = m.att!=='off'?'inline-block':'none';
            document.getElementById('bdgAtt').innerText = 'ATT '+m.att.toUpperCase();
            
            if (m.connections !== undefined) {
                document.getElementById('bdgConn').innerText = '👤 ' + m.connections;
            }

            // GPS Logic
            const btnGPS = document.getElementById('btnGPSAuth');
            const mapContainer = document.getElementById('mapContainer');
            const addrDisp = document.getElementById('dspAddr');

            if (m.gpsUnlocked) {
                btnGPS.innerText = "LOCK MAP & GPS";
                btnGPS.classList.add('active');
                
                const wasHidden = mapContainer.style.display === 'none';
                mapContainer.style.display = 'block';
                addrDisp.innerText = m.address || '';
                
                if (!map) {
                    window.ui.initMap();
                } else if (wasHidden) {
                    setTimeout(() => map.invalidateSize(), 100);
                }

                const mapMsg = document.getElementById('mapMsg');
                if (m.gpsStatus === 'active' && m.lat && m.lon && m.lat !== 0 && m.lon !== 0) {
                    mapMsg.style.display = 'none';
                    const latLng = [m.lat, m.lon];
                    if (marker) marker.setLatLng(latLng);
                    if (map) {
                        map.setView(latLng, 13);
                    }
                } else if (m.gpsStatus === 'searching') {
                    mapMsg.style.display = 'flex';
                    mapMsg.innerText = '📡 GPS信号を受信中...';
                } else if (m.gpsStatus === 'disconnected') {
                    mapMsg.style.display = 'flex';
                    mapMsg.innerText = '⚠️ GPSモジュール未接続';
                }
            } else {
                btnGPS.innerText = "UNLOCK MAP & GPS";
                btnGPS.classList.remove('active');
                mapContainer.style.display = 'none';
                addrDisp.innerText = '';
            }
            
            ['off','weak','mid','strong'].forEach(k => { 
                const el = document.getElementById('att'+k.charAt(0).toUpperCase()+k.slice(1));
                if(el) el.className = 'btn '+(m.att===k?'active':''); 
            });
            document.getElementById('btnRec').className = 'btn '+(m.isRecording?'rec on':'');
            this.renderSq(m.squelch);
            
            if (prevFreq !== m.freq || prevRec !== m.isRecording) {
                this.updateMediaMetadata();
            }
        },

        updDebug(d) {
            document.getElementById('dbgTemp').innerText = d.cpuTemp.toFixed(1) + '°C';
            document.getElementById('dbgLoad1').innerText = d.loadAvg1.toFixed(2);
            document.getElementById('dbgLoad5').innerText = d.loadAvg5.toFixed(2);
            document.getElementById('dbgLoad15').innerText = d.loadAvg15.toFixed(2);
            const memPct = (d.memUsed / d.memTotal) * 100;
            document.getElementById('dbgMem').innerText = memPct.toFixed(1) + '%';
            const diskPct = (d.diskUsed / d.diskTotal) * 100;
            document.getElementById('dbgDisk').innerText = diskPct.toFixed(0) + '%';
        },
        
        renderSq(v) { document.getElementById('sqMarker').style.left = v + '%'; document.getElementById('valSq').innerText = v; },
        adjSq(delta) { let n = this.state.squelch + delta; if (n < 0) n = 0; if (n > 100) n = 100; this.state.squelch = n; this.renderSq(n); window.ws.sendSq(n); this.updateMediaMetadata(); },
        
        toggleDebug() {
            const panel = document.getElementById('debugPanel');
            if (panel.style.display === 'flex') {
                panel.style.display = 'none';
            } else {
                this.modal('auth_debug');
            }
        },
        
        togEdit() {
            this.state.editMode = !this.state.editMode;
            const btn = document.getElementById('btnEditToggle');
            const ctrls = document.getElementById('addBtns');
            const panel = document.getElementById('listBM');
            
            if (this.state.editMode) {
                btn.innerText = 'DONE';
                btn.classList.add('editing');
                ctrls.classList.add('show');
                panel.classList.add('edit-mode');
            } else {
                btn.innerText = 'EDIT';
                btn.classList.remove('editing');
                ctrls.classList.remove('show');
                panel.classList.remove('edit-mode');
            }
            this.renderBM();
        },

        modal(type, id=null) {
            this.closeModal(); 
            if (type === 'tune') {
                document.getElementById('modalTune').style.display = 'flex';
                document.getElementById('inpFreq').value = (this.state.freq/1e6).toFixed(3); 
                this.selMod(this.state.mode); 
                document.getElementById('inpPass').focus();
            } else if (type === 'auth_gps') {
                const isLocked = !this.state.gpsUnlocked;
                document.getElementById('gpsModalTitle').innerText = isLocked ? "Unlock GPS" : "Lock GPS";
                document.getElementById('gpsModalDesc').innerText = isLocked ? 
                    "Enter password to enable GPS tracking for all users." : 
                    "Enter password to disable GPS tracking.";
                document.getElementById('btnGPSModalAction').innerText = isLocked ? "UNLOCK" : "LOCK";
                
                document.getElementById('modalGPSAuth').style.display = 'flex';
                document.getElementById('inpGPSPass').focus();
            } else if (type === 'auth_debug') {
                document.getElementById('modalDebugAuth').style.display = 'flex';
                document.getElementById('inpDebugPass').focus();
            } else if (type === 'auth_delete') {
                document.getElementById('modalDeleteAuth').style.display = 'flex';
                document.getElementById('inpDeletePass').focus();
            } else if (type === 'add_folder' || type === 'add_freq') {
                document.getElementById('modalAdd').style.display = 'flex';
                this.targetParent = id; 
                this.state.editTargetId = null; 
                this.addType = (type === 'add_folder') ? 'folder' : 'freq';
                document.getElementById('addTitle').innerText = (this.addType === 'folder') ? "Create Folder" : "Add Channel";
                document.getElementById('addName').value = "";
                if (this.addType === 'folder') {
                    document.getElementById('addFreqGroup').style.display = 'none';
                } else {
                    document.getElementById('addFreqGroup').style.display = 'block';
                    document.getElementById('addFreq').value = (this.state.freq/1e6).toFixed(3);
                    this.selAddMod(this.state.mode);
                }
                document.getElementById('addName').focus();
            } else if (type === 'edit') {
                const target = this.state.bm.find(b => b.id === id);
                if (!target) return;
                this.state.editTargetId = id;
                document.getElementById('modalAdd').style.display = 'flex';
                this.addType = target.isFolder ? 'folder' : 'freq';
                document.getElementById('addTitle').innerText = target.isFolder ? "Edit Folder" : "Edit Channel";
                document.getElementById('addName').value = target.title;
                if (target.isFolder) {
                      document.getElementById('addFreqGroup').style.display = 'none';
                } else {
                      document.getElementById('addFreqGroup').style.display = 'block';
                      document.getElementById('addFreq').value = target.freq;
                      this.selAddMod(target.mode);
                }
            } else if (type === 'move') {
                this.state.moveTargetId = id;
                document.getElementById('modalMove').style.display = 'flex';
                const list = document.getElementById('moveFolderList');
                list.innerHTML = this.genFolderListHtml(null, 0);
            }
        },
        genFolderListHtml(parentId, depth) {
            let html = '';
            if (parentId === null) {
                html += '<div class="move-item" onclick="window.ws.changeParent(null)"><span class="material-symbols-outlined" style="margin-right:8px">home</span> ROOT</div>';
            }
            
            const children = this.state.bm.filter(b => {
                if (!b.isFolder) return false;
                if (parentId === null) return !b.parentId || b.parentId === "null"; 
                return b.parentId === parentId;
            });
            
            children.forEach(c => {
                if (c.id === this.state.moveTargetId) return; 

                const pad = depth * 20;
                html += '<div class="move-item" style="padding-left:'+(12+pad)+'px" onclick="window.ws.changeParent(\''+c.id+'\')"><span class="material-symbols-outlined" style="margin-right:8px">folder</span> '+c.title+'</div>';
                html += this.genFolderListHtml(c.id, depth + 1);
            });
            return html;
        },
        closeModal() {
            document.getElementById('modalTune').style.display = 'none';
            document.getElementById('modalAdd').style.display = 'none';
            document.getElementById('modalMove').style.display = 'none';
            document.getElementById('modalGPSAuth').style.display = 'none';
            document.getElementById('modalDebugAuth').style.display = 'none';
            document.getElementById('modalDeleteAuth').style.display = 'none';
        },
        selMod(m) {
            this.modalMode = m;
            document.getElementById('modAM').className = 'btn '+(m==='AM'?'active':'');
            document.getElementById('modFM').className = 'btn '+(m==='FM'?'active':'');
            document.getElementById('modWFM').className = 'btn '+(m==='WFM'?'active':'');
        },
        selAddMod(m) {
            this.addMode = m;
            document.getElementById('addModAM').className = 'btn '+(m==='AM'?'active':'');
            document.getElementById('addModFM').className = 'btn '+(m==='FM'?'active':'');
            document.getElementById('addModWFM').className = 'btn '+(m==='WFM'?'active':'');
        },
        renderBM(list) {
            const d = list || this.state.bm;
            const roots = []; const map = {};
            d.forEach(i => map[i.id] = {...i, c:[]});
            d.forEach(i => { if(i.parentId && map[i.parentId]) map[i.parentId].c.push(map[i.id]); else roots.push(map[i.id]); });
            document.getElementById('listBM').innerHTML = this.tree(roots);
        },
        tree(nodes) {
            const isEdit = this.state.editMode;
            
            return nodes.map((n, idx) => {
                const isFirst = idx === 0;
                const isLast = idx === nodes.length - 1;
                
                let acts = '';
                if (isEdit) {
                    const moveBtns = 
                        (!isFirst ? '<button class="ib ib-move" onclick="event.stopPropagation(); window.ws.move(\''+n.id+'\', \'up\')"><span class="material-symbols-outlined">arrow_upward</span></button>' : '') +
                        (!isLast ? '<button class="ib ib-move" onclick="event.stopPropagation(); window.ws.move(\''+n.id+'\', \'down\')"><span class="material-symbols-outlined">arrow_downward</span></button>' : '');
                    
                    let addSubBtns = '';
                    if (n.isFolder) {
                        addSubBtns += '<button class="ib" onclick="event.stopPropagation(); window.ui.modal(\'add_freq\', \''+n.id+'\')" title="Add Channel"><span class="material-symbols-outlined">add</span></button>';
                        addSubBtns += '<button class="ib" onclick="event.stopPropagation(); window.ui.modal(\'add_folder\', \''+n.id+'\')" title="Add Sub-Folder"><span class="material-symbols-outlined">create_new_folder</span></button>';
                    }
                    
                    const moveParentBtn = '<button class="ib" onclick="event.stopPropagation(); window.ui.modal(\'move\', \''+n.id+'\')" title="Move to Folder"><span class="material-symbols-outlined">drive_file_move</span></button>';

                    acts = moveBtns + moveParentBtn + addSubBtns + 
                        '<button class="ib" onclick="event.stopPropagation(); window.ui.modal(\'edit\', \''+n.id+'\')"><span class="material-symbols-outlined">edit</span></button>' + 
                        '<button class="ib ib-del" onclick="event.stopPropagation(); window.ws.del(\''+n.id+'\')"><span class="material-symbols-outlined">delete</span></button>';
                }

                let onClick = '';
                if (n.isFolder) {
                    onClick = 'window.ui.tog(\''+n.id+'\')';
                } else {
                    if (!isEdit) {
                        const safeTitle = n.title.replace(/'/g, "\\'");
                        onClick = 'window.ws.tuneDir('+n.freq+', \''+n.mode+'\', \''+safeTitle+'\')';
                    } else {
                        onClick = "event.stopPropagation(); window.ui.modal('edit', '"+n.id+"')"; 
                    }
                }

                if(n.isFolder) {
                    const open = this.state.expanded.has(n.id);
                    return '<div>' +
                            '<div class="row" onclick="'+onClick+'">' +
                                '<div class="row-click-area">' +
                                    '<span class="material-symbols-outlined icon '+(open?'rot':'')+'">chevron_right</span>' +
                                    '<span style="font-weight:600; margin-left:10px;">'+n.title+'</span>' +
                                '</div>' +
                                '<div class="act">'+acts+'</div>' +
                            '</div>' +
                            '<div class="folder-c '+(open?'open':'')+'">'+this.tree(n.c)+'</div>' +
                        '</div>';
                }
                return '<div class="row" onclick="'+onClick+'">' +
                        '<div class="row-click-area">' +
                            '<div class="txt">' +
                                '<span style="font-weight:600;">'+n.title+'</span>' +
                                '<span class="sub">'+n.freq.toFixed(3)+' MHz '+n.mode+'</span>' +
                            '</div>' +
                        '</div>' +
                        '<div class="act">'+acts+'</div>' +
                    '</div>';
            }).join('');
        },
        tog(id) {
            if(this.state.expanded.has(id)) this.state.expanded.delete(id); else this.state.expanded.add(id);
            this.renderBM();
        },
        togDate(date) {
            const id = 'date_' + date;
            if(this.state.expanded.has(id)) this.state.expanded.delete(id); else this.state.expanded.add(id);
            if (this.state.recData) this.renderRec(this.state.recData);
        },
        togFreq(date, freq) {
            const id = 'freq_' + date + '_' + freq;
            if(this.state.expanded.has(id)) this.state.expanded.delete(id); else this.state.expanded.add(id);
            if (this.state.recData) this.renderRec(this.state.recData);
        },
        renderRec(list) {
            this.state.recData = list; // Store for re-rendering
            let html = '';
            list.forEach(dateGroup => {
                const dateId = 'date_' + dateGroup.date;
                const isDateOpen = this.state.expanded.has(dateId);
                
                html += '<div class="row" onclick="window.ui.togDate(\'' + dateGroup.date + '\')" style="background:rgba(255,255,255,0.08); margin-top:5px;">' +
                        '<div class="row-click-area">' +
                             '<span class="material-symbols-outlined icon '+(isDateOpen?'rot':'')+'">chevron_right</span>' +
                             '<span style="font-weight:800; margin-left:10px;">' + dateGroup.date + '</span>' +
                        '</div></div>';
                
                if (isDateOpen) {
                    dateGroup.freqs.forEach(freqGroup => {
                          const freqId = 'freq_' + dateGroup.date + '_' + freqGroup.freq;
                          const isFreqOpen = this.state.expanded.has(freqId);

                          html += '<div style="margin-left:15px; border-left:2px solid rgba(255,255,255,0.1); padding-left:10px;">' +
                                  '<div onclick="window.ui.togFreq(\'' + dateGroup.date + '\', \'' + freqGroup.freq + '\')" style="padding:8px 0; font-size:0.9rem; color:var(--acc); font-weight:bold; cursor:pointer; display:flex; align-items:center;">' + 
                                  '<span class="material-symbols-outlined icon '+(isFreqOpen?'rot':'')+'" style="font-size:1rem; margin-right:5px;">chevron_right</span>' +
                                  freqGroup.freq + '</div>';
                          
                          if (isFreqOpen) {
                              freqGroup.files.forEach(f => {
                                  html += '<div class="row" style="margin-bottom:2px;">' +
                                              '<div class="row-click-area">' +
                                                  '<div class="txt">' +
                                                      '<span style="font-weight:600; font-size:0.85rem; word-break:break-all;">'+f.name+'</span>' +
                                                      '<span class="sub">'+(f.size/1024/1024).toFixed(2)+' MB</span>' +
                                                  '</div>' +
                                              '</div>' +
                                              '<div class="act">' +
                                                  '<a href="/download/'+f.path+'" class="ib" download><span class="material-symbols-outlined">download</span></a>' +
                                                  '<button class="ib ib-del" onclick="window.ws.delRec(\''+f.path+'\')"><span class="material-symbols-outlined">delete</span></button>' +
                                              '</div>' +
                                          '</div>';
                              });
                          }
                          html += '</div>';
                    });
                }
            });
            document.getElementById('listRec').innerHTML = html;
        }
    };

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', () => window.ui.init());
    } else {
        window.ui.init();
    }
</script>
</body>
</html>
`