package main

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"math"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"sync"
	"time"

	"github.com/gorilla/websocket"
	"github.com/joho/godotenv"
)

// ==========================================
// 1. 設定 (Configuration)
// ==========================================
const (
	Port           = ":3000"
	Password       = "admin"
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
	Att         string  `json:"att"`
	Squelch     int     `json:"squelch"`
	IsRecording bool    `json:"isRecording"`
	RecFilename string  `json:"-"`
	mu          sync.Mutex
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
	Type        string          `json:"type"`
	Password    string          `json:"password,omitempty"`
	Freq        float64         `json:"freq,omitempty"`
	Mode        string          `json:"mode,omitempty"`
	Att         string          `json:"att,omitempty"`
	Val         int             `json:"val,omitempty"`
	Filename    string          `json:"filename,omitempty"`
	Data        json.RawMessage `json:"data,omitempty"`
	ID          string          `json:"id,omitempty"`
	Dir         string          `json:"dir,omitempty"`
	NewParentID string          `json:"newParentId,omitempty"`
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
		if g > 20.0 { g = 20.0 }
		if g < 0.1 { g = 0.1 }
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
		if p > 0.99 { p = 0.99 }
		if p < -0.99 { p = -0.99 }

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
	Conn *websocket.Conn
	mu   sync.Mutex
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
		Att:         "off",
		Squelch:     10,
		IsRecording: false,
	}
	bookmarks []Bookmark
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
// 6. SDR Manager
// ==========================================

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
		case "weak": gainVal = "29"
		case "mid": gainVal = "9"
		case "strong": gainVal = "0"
		}

		args := []string{"-f", freqStr, "-g", gainVal, "-p", ppm, "-F", "9"}
		if mode == "WFM" {
			args = append(args, "-M", "wbfm", "-s", "240000", "-r", fmt.Sprintf("%d", SampleRate))
		} else {
			rtlMode := "am"
			if mode == "FM" { rtlMode = "fm" }
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
					if res.IsOpen { isOpenInt = 1 }
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
// 7. Recording Logic
// ==========================================

func startRecording() {
	state.mu.Lock()
	defer state.mu.Unlock()
	if state.IsRecording { return }

	ts := time.Now().Format("2006-01-02T15-04-05")
	filename := fmt.Sprintf("%s_%.3fMHz_%s.wav", state.Mode, float64(state.Freq)/1e6, ts)
	path := filepath.Join(RecordingsPath, filename)
	
	f, err := os.Create(path)
	if err != nil {
		log.Println("Rec error:", err)
		return
	}
	
	writeWavHeader(f, SampleRate, 0)
	
	recMu.Lock()
	recFile = f
	state.IsRecording = true
	state.RecFilename = filename
	recMu.Unlock()
	
	broadcastStatus()
}

func stopRecording() {
	state.mu.Lock()
	if !state.IsRecording { state.mu.Unlock(); return }
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
// 8. Data Persistence
// ==========================================

func loadData() {
	if _, err := os.Stat(RecordingsPath); os.IsNotExist(err) {
		os.Mkdir(RecordingsPath, 0755)
	}

	bData, err := os.ReadFile(BookmarksFile)
	if err == nil {
		json.Unmarshal(bData, &bookmarks)
	} else {
		bookmarks = []Bookmark{
			{ID: "1", Title: "Default Folder", IsFolder: true},
		}
		saveBookmarks()
	}

	sData, err := os.ReadFile(SquelchFile)
	if err == nil {
		json.Unmarshal(sData, &squelchDB)
	}
}

func saveBookmarks() {
	d, _ := json.MarshalIndent(bookmarks, "", "  ")
	os.WriteFile(BookmarksFile, d, 0644)
}

func saveSquelch() {
	d, _ := json.MarshalIndent(squelchDB, "", "  ")
	os.WriteFile(SquelchFile, d, 0644)
}

// ==========================================
// 9. WebSocket Handlers
// ==========================================

// Helper: Check if moving checkID to potentialAncestorID would cause a cycle
func isDescendant(checkID, potentialAncestorID string, all []Bookmark) bool {
	currentID := checkID
	for {
		if currentID == "" { return false } // Reached root, safe
		if currentID == potentialAncestorID { return true } // Cycle detected
		
		// Find parent
		parentID := ""
		found := false
		for _, b := range all {
			if b.ID == currentID {
				parentID = b.ParentID
				found = true
				break
			}
		}
		if !found { return false } // Should not happen if data is consistent
		currentID = parentID
	}
}

func broadcastStatus() {
	state.mu.Lock()
	defer state.mu.Unlock()
	msg := map[string]interface{}{
		"type":        "status_update",
		"freq":        state.Freq,
		"mode":        state.Mode,
		"att":         state.Att,
		"squelch":     state.Squelch,
		"isRecording": state.IsRecording,
	}
	bytes, _ := json.Marshal(msg)
	statusMsg <- bytes
}

func broadcastRecordings() {
	files, _ := os.ReadDir(RecordingsPath)
	var list []map[string]interface{}
	for _, f := range files {
		if filepath.Ext(f.Name()) == ".wav" {
			info, _ := f.Info()
			list = append(list, map[string]interface{}{
				"name": f.Name(),
				"size": info.Size(),
			})
		}
	}
	sort.Slice(list, func(i, j int) bool {
		return list[i]["name"].(string) > list[j]["name"].(string)
	})
	
	msg := map[string]interface{}{
		"type": "recordings",
		"data": list,
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

func wsHandler(w http.ResponseWriter, r *http.Request) {
	ws, err := upgrader.Upgrade(w, r, nil)
	if err != nil { return }
	
	client := &SafeClient{Conn: ws}

	clientsMu.Lock()
	clients[client] = true
	clientsMu.Unlock()

	broadcastStatus()
	
	bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
	client.WriteMessage(websocket.TextMessage, bmMsg)
	
	broadcastRecordings()

	for {
		_, msg, err := ws.ReadMessage()
		if err != nil {
			clientsMu.Lock()
			delete(clients, client)
			clientsMu.Unlock()
			break
		}
		
		var cmd WSCommand
		if err := json.Unmarshal(msg, &cmd); err != nil { continue }
		
		switch cmd.Type {
		case "auth_tune":
			if cmd.Password == Password {
				state.mu.Lock()
				state.Freq = int(cmd.Freq)
				state.Mode = cmd.Mode
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
			os.Remove(filepath.Join(RecordingsPath, cmd.Filename))
			broadcastRecordings()
		
		case "add_bookmark":
			var b Bookmark
			json.Unmarshal(cmd.Data, &b)
			b.ID = fmt.Sprintf("%d", time.Now().UnixMilli())
			bookmarks = append(bookmarks, b)
			saveBookmarks()
			bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
			statusMsg <- bmMsg

		case "delete_bookmark":
			newBM := []Bookmark{}
			for _, b := range bookmarks {
				if b.ID != cmd.ID && b.ParentID != cmd.ID {
					newBM = append(newBM, b)
				}
			}
			bookmarks = newBM
			saveBookmarks()
			bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
			statusMsg <- bmMsg
		
		case "edit_bookmark":
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
			saveBookmarks()
			bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
			statusMsg <- bmMsg

		case "move_bookmark":
			idx := -1
			for i, b := range bookmarks { if b.ID == cmd.ID { idx = i; break } }
			if idx != -1 {
				target := bookmarks[idx]
				siblings := []int{}
				for i, b := range bookmarks { if b.ParentID == target.ParentID { siblings = append(siblings, i) } }
				
				sIdx := -1
				for i, globalIdx := range siblings { if globalIdx == idx { sIdx = i; break } }
				
				if cmd.Dir == "up" && sIdx > 0 {
					swapIdx := siblings[sIdx-1]
					bookmarks[idx], bookmarks[swapIdx] = bookmarks[swapIdx], bookmarks[idx]
				} else if cmd.Dir == "down" && sIdx < len(siblings)-1 {
					swapIdx := siblings[sIdx+1]
					bookmarks[idx], bookmarks[swapIdx] = bookmarks[swapIdx], bookmarks[idx]
				}
				saveBookmarks()
				bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
				statusMsg <- bmMsg
			}

		case "change_parent":
			// Check if new parent is a descendant of the moving item (Circular Reference)
			var target Bookmark
			for _, b := range bookmarks { if b.ID == cmd.ID { target = b; break } }
			
			if target.IsFolder {
				if isDescendant(cmd.NewParentID, target.ID, bookmarks) {
					// Cannot move folder into its own descendant
					continue 
				}
			}

			for i, b := range bookmarks {
				if b.ID == cmd.ID && b.ID != cmd.NewParentID {
					bookmarks[i].ParentID = cmd.NewParentID
					break
				}
			}
			saveBookmarks()
			bmMsg, _ := json.Marshal(map[string]interface{}{"type": "bookmarks", "data": bookmarks})
			statusMsg <- bmMsg
		}
	}
}

// ==========================================
// 10. Main & HTML Content (Fixed for Folder Move)
// ==========================================

func main() {
	flag.Parse()
	
	err := godotenv.Load()
	if err != nil {
		log.Println("Note: .env file not found, continuing without env vars")
	}

	loadData()

	http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/" {
			w.Header().Set("Content-Type", "text/html")
			w.Write([]byte(htmlContent))
			return
		}
		if len(r.URL.Path) > 10 && r.URL.Path[:10] == "/download/" {
			fname := filepath.Base(r.URL.Path)
			fpath := filepath.Join(RecordingsPath, fname)
			if _, err := os.Stat(fpath); err == nil {
				w.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=\"%s\"", fname))
				http.ServeFile(w, r, fpath)
				return
			}
		}
		http.NotFound(w, r)
	})

	http.HandleFunc("/ws", wsHandler)

	go sdrManager()
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
<title>SDR COMMANDER (Go)</title>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Inter:wght@400;600;800&family=JetBrains+Mono:wght@700&display=swap">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Material+Symbols+Outlined:opsz,wght,FILL,GRAD@24,400,0,0" />
<style>
    :root { --bg: #050507; --panel: rgba(30, 30, 35, 0.7); --acc: #00ffc8; --acc-dim: rgba(0,255,200,0.15); --txt: #fff; --sub: #8b9bb4; --mute: #4a4a4a; --open: #00e676; --stop: #ff3b30; --warn: #ffcc00; }
    body { background: var(--bg); color: var(--txt); font-family: 'Inter', sans-serif; margin: 0; display: flex; justify-content: center; min-height: 100vh; user-select: none; -webkit-user-select: none; touch-action: manipulation; }
    .app { width: 100%; max-width: 480px; padding: 20px 20px 100px; box-sizing: border-box; }
    .panel { background: var(--panel); backdrop-filter: blur(12px); border-radius: 16px; border: 1px solid rgba(255,255,255,0.08); padding: 20px; margin-bottom: 16px; }
    .freq { font-family: 'JetBrains Mono', monospace; font-size: 3.2rem; text-align: center; font-weight: 700; line-height: 1; text-shadow: 0 0 20px var(--acc-dim); margin: 15px 0; }
    .badges { display: flex; justify-content: center; gap: 8px; }
    .badge { font-size: 0.75rem; padding: 4px 10px; border-radius: 20px; background: rgba(255,255,255,0.05); color: var(--sub); border: 1px solid rgba(255,255,255,0.05); transition: 0.2s; }
    .badge-sql { background: var(--mute); color: #ccc; }
    .badge-sql.open { background: var(--open); color: #000; box-shadow: 0 0 10px var(--open); font-weight: bold; }
    .meter-wrap { position: relative; height: 32px; margin-top: 20px; border: 1px solid rgba(255,255,255,0.1); border-radius: 6px; overflow: hidden; background: #111; }
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
</style>
</head>
<body>
    <div class="app">
        <div class="panel">
            <div class="badges">
                <span class="badge" id="bdgMode">AM</span>
                <span class="badge" id="bdgAtt" style="display:none">ATT</span>
                <span class="badge badge-sql" id="bdgSql">MUTED</span>
            </div>
            <div class="freq" id="dspFreq">---.---</div>
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
        </div>

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

    <audio id="audioBridge" autoplay playsinline loop style="display:none;"></audio>

<script>
    let audioCtx;
    const state = { freq:0, mode:'AM', att:'off', rec:false, bm:[], expanded:new Set(), squelch: 10, editTargetId: null, editMode: false, moveTargetId: null };
    let nextStartTime = 0; 

    // WebSocket Definition
    window.ws = {
        c: null,
        connect() {
            this.c = new WebSocket((location.protocol==='https:'?'wss:':'ws:')+'//'+location.host + '/ws');
            this.c.binaryType = 'arraybuffer';
            this.c.onmessage = e => {
                if(typeof e.data === 'string') {
                    const m = JSON.parse(e.data);
                    if(m.type==='status_update') window.ui.upd(m);
                    else if(m.type==='bookmarks') { state.bm = m.data; window.ui.renderBM(); }
                    else if(m.type==='recordings') window.ui.renderRec(m.data);
                    else if(m.type==='error') alert(m.msg);
                } else this.audio(e.data);
            };
            this.c.onclose = () => setTimeout(()=>this.connect(), 3000);
        },
        send(o) { if(this.c&&this.c.readyState===1) this.c.send(JSON.stringify(o)); },
        sendSq(v) { this.send({type:'set_squelch', val:parseInt(v)}); },
        setMode(m) { state.mode=m; this.tune(true); },
        setAtt(a) { this.send({type:'set_att', att:a}); },
        togRec() { this.send({type:state.rec?'stop_recording':'start_recording'}); },
        move(id, dir) { this.send({type:'move_bookmark', id, dir}); },
        changeParent(pid) {
            if (state.moveTargetId) {
                this.send({type:'change_parent', id:state.moveTargetId, newParentId:pid});
                window.ui.closeModal();
            }
        },
        tune(skip=false) {
            let f = state.freq;
            const m = window.ui.modalMode; 
            if(!skip) { const v = parseFloat(document.getElementById('inpFreq').value); if(v) f = Math.floor(v*1e6); }
            const p = document.getElementById('inpPass').value;
            this.send({type:'auth_tune', password:p, freq:f, mode:m});
            window.ui.closeModal();
        },
        tuneDir(f, m) {
            const p = document.getElementById('inpPass').value;
            if (!p) {
                state.freq = Math.floor(f*1e6);
                state.mode = m;
                document.getElementById('inpFreq').value = f.toFixed(3);
                window.ui.selMod(m);
                window.ui.modal('tune');
                return;
            }
            this.send({type:'auth_tune', password:p, freq:Math.floor(f*1e6), mode:m});
            state.mode = m;
        },
        saveBookmark() {
            const title = document.getElementById('addName').value;
            if (!title) return;
            const isFolder = (window.ui.addType === 'folder');
            
            if (state.editTargetId) {
                const data = { id: state.editTargetId, title, isFolder };
                if (!isFolder) {
                    const freqVal = parseFloat(document.getElementById('addFreq').value);
                    if (!freqVal) return;
                    data.freq = freqVal;
                    data.mode = window.ui.addMode;
                }
                this.send({type:'edit_bookmark', data: JSON.stringify(data)});
            } else {
                const data = { title, isFolder, parentId: window.ui.targetParent };
                if (!isFolder) {
                    const freqVal = parseFloat(document.getElementById('addFreq').value);
                    if (!freqVal) return;
                    data.freq = freqVal;
                    data.mode = window.ui.addMode;
                }
                this.send({type:'add_bookmark', data: JSON.stringify(data)});
            }
            window.ui.closeModal();
        },
        del(id) { if(confirm('Delete?')) this.send({type:'delete_bookmark', id}); },
        delRec(n) { if(confirm('Delete?')) this.send({type:'delete_recording', filename:n}); },
        
        audio(b) {
            if(!audioCtx || audioCtx.state !== 'running') return;
            const dv = new DataView(b);
            const rssi = dv.getInt16(0, true);
            const sqlOpen = dv.getInt16(2, true);
            
            const bar = window.ui.els.rssi;
            bar.style.width = Math.min(100, (rssi/200)*100)+'%';
            if(sqlOpen) bar.classList.add('active'); else bar.classList.remove('active');
            const bdgSql = document.getElementById('bdgSql');
            if (sqlOpen) { bdgSql.innerText = 'SQL OPEN'; bdgSql.className = 'badge badge-sql open'; } 
            else { bdgSql.innerText = 'MUTED'; bdgSql.className = 'badge badge-sql'; }

            const f = new Float32Array((b.byteLength - 4) / 2);
            const s16 = new Int16Array(b, 4);
            for(let i=0; i<f.length; i++) f[i] = s16[i]/32768.0;

            const buf = audioCtx.createBuffer(1, f.length, 48000);
            buf.getChannelData(0).set(f);

            const now = audioCtx.currentTime;
            if (nextStartTime < now) nextStartTime = now;

            const s = audioCtx.createBufferSource();
            s.buffer = buf;
            if (window.audioDest) s.connect(window.audioDest);
            else s.connect(audioCtx.destination);
            
            s.start(nextStartTime);
            nextStartTime += buf.duration;
        }
    };

    // UI Definition
    window.ui = {
        els: { freq:document.getElementById('dspFreq'), rssi:document.getElementById('dspRssi'), sq:document.getElementById('sqMarker'), valSq:document.getElementById('valSq') },
        modalMode: 'AM',
        addMode: 'AM',
        targetParent: null,
        addType: 'freq',

        init() {
            if (window.ws) { window.ws.connect(); } 
            
            if ('mediaSession' in navigator) {
                const ms = navigator.mediaSession;
                ms.setActionHandler('play', () => this.togAudio());
                ms.setActionHandler('pause', () => this.togAudio());
                ms.setActionHandler('stop', () => this.togAudio());
                ms.setActionHandler('previoustrack', () => {
                    const newFreq = state.freq - 100000;
                    window.ws.tuneDir(newFreq / 1e6, state.mode);
                });
                ms.setActionHandler('nexttrack', () => {
                    const newFreq = state.freq + 100000;
                    window.ws.tuneDir(newFreq / 1e6, state.mode);
                });
            }
        },

        togAudio() {
            const btn = document.getElementById('btnAudio');
            if (!audioCtx) {
                const Ctx = window.AudioContext || window.webkitAudioContext;
                audioCtx = new Ctx({ latencyHint: 'interactive' }); 
                
                const dest = audioCtx.createMediaStreamDestination();
                const audioEl = document.getElementById('audioBridge');
                audioEl.srcObject = dest.stream;
                
                audioEl.play().catch(e => console.warn(e));
                window.audioDest = dest;
                
                const osc = audioCtx.createOscillator();
                const g = audioCtx.createGain();
                osc.connect(g); g.connect(dest); g.connect(audioCtx.destination);
                osc.frequency.value = 20; g.gain.value = 0.001;
                osc.start();
                
                this.updateBtnState('running');
                this.updateMediaMetadata();
                return;
            }

            if (audioCtx.state === 'running') {
                audioCtx.suspend().then(() => {
                    this.updateBtnState('suspended');
                    document.getElementById('audioBridge').pause();
                    if('mediaSession' in navigator) navigator.mediaSession.playbackState = 'paused';
                });
            } else {
                audioCtx.resume().then(() => {
                    this.updateBtnState('running');
                    document.getElementById('audioBridge').play().catch(()=>{});
                    this.updateMediaMetadata();
                });
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
            if (!('mediaSession' in navigator) || !audioCtx || audioCtx.state !== 'running') return;
            navigator.mediaSession.playbackState = 'playing';
            
            // Fixed backticks issue by using concatenation
            const titleStr = (state.freq/1e6).toFixed(3) + ' MHz';
            const artistStr = state.mode + ' | SQL: ' + state.squelch + ' | ' + (state.rec ? '● REC' : 'LIVE');
            
            navigator.mediaSession.metadata = new MediaMetadata({
                title: titleStr,
                artist: artistStr,
                album: 'SDR Commander',
                artwork: [
                    { src: 'https://placehold.co/512x512/111/00ffc8?text=SDR', sizes: '512x512', type: 'image/png' },
                    { src: 'https://placehold.co/192x192/111/00ffc8?text='+state.mode, sizes: '192x192', type: 'image/png' }
                ]
            });
        },

        upd(m) {
            const prevFreq = state.freq;
            const prevRec = state.rec;

            state.freq=m.freq; state.mode=m.mode; state.att=m.att; state.rec=m.isRecording; state.squelch=m.squelch;
            
            this.els.freq.innerText = (m.freq/1e6).toFixed(3);
            document.getElementById('bdgMode').innerText = m.mode;
            document.getElementById('bdgAtt').style.display = m.att!=='off'?'inline-block':'none';
            document.getElementById('bdgAtt').innerText = 'ATT '+m.att.toUpperCase();
            
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
        
        renderSq(v) { this.els.sq.style.left = v + '%'; this.els.valSq.innerText = v; },
        adjSq(delta) { let n = state.squelch + delta; if (n < 0) n = 0; if (n > 100) n = 100; state.squelch = n; this.renderSq(n); window.ws.sendSq(n); this.updateMediaMetadata(); },
        
        togEdit() {
            state.editMode = !state.editMode;
            const btn = document.getElementById('btnEditToggle');
            const ctrls = document.getElementById('addBtns');
            const panel = document.getElementById('listBM');
            
            if (state.editMode) {
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
                document.getElementById('inpFreq').value = (state.freq/1e6).toFixed(3); 
                this.selMod(state.mode); 
                document.getElementById('inpPass').focus();
            } else if (type === 'add_folder' || type === 'add_freq') {
                document.getElementById('modalAdd').style.display = 'flex';
                this.targetParent = id; 
                state.editTargetId = null; 
                this.addType = (type === 'add_folder') ? 'folder' : 'freq';
                document.getElementById('addTitle').innerText = (this.addType === 'folder') ? "Create Folder" : "Add Channel";
                document.getElementById('addName').value = "";
                if (this.addType === 'folder') {
                    document.getElementById('addFreqGroup').style.display = 'none';
                } else {
                    document.getElementById('addFreqGroup').style.display = 'block';
                    document.getElementById('addFreq').value = (state.freq/1e6).toFixed(3);
                    this.selAddMod(state.mode);
                }
                document.getElementById('addName').focus();
            } else if (type === 'edit') {
                const target = state.bm.find(b => b.id === id);
                if (!target) return;
                state.editTargetId = id;
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
                state.moveTargetId = id;
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
            
            // Fix: correctly handle null/empty parentId logic
            const children = state.bm.filter(b => {
                if (!b.isFolder) return false;
                if (parentId === null) return !b.parentId; 
                return b.parentId === parentId;
            });
            
            children.forEach(c => {
                // Prevent moving a folder into itself
                if (c.id === state.moveTargetId) return; 

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
            const d = list || state.bm;
            const roots = []; const map = {};
            d.forEach(i => map[i.id] = {...i, c:[]});
            d.forEach(i => { if(i.parentId && map[i.parentId]) map[i.parentId].c.push(map[i.id]); else roots.push(map[i.id]); });
            document.getElementById('listBM').innerHTML = this.tree(roots);
        },
        tree(nodes) {
            const isEdit = state.editMode;
            
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
                    if (!isEdit) onClick = 'window.ws.tuneDir('+n.freq+', \''+n.mode+'\')';
                    else onClick = "event.stopPropagation(); window.ui.modal('edit', '"+n.id+"')"; 
                }

                if(n.isFolder) {
                    const open = state.expanded.has(n.id);
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
            if(state.expanded.has(id)) state.expanded.delete(id); else state.expanded.add(id);
            this.renderBM();
        },
        renderRec(list) {
            document.getElementById('listRec').innerHTML = list.map(f => 
                '<div class="row">' +
                    '<div class="row-click-area">' +
                        '<div class="txt">' +
                            '<span style="font-weight:600;">'+(f.name.split('_')[2]||f.name)+'</span>' +
                            '<span class="sub">'+(f.size/1024/1024).toFixed(2)+' MB</span>' +
                        '</div>' +
                    '</div>' +
                    '<div class="act">' +
                        '<a href="/download/'+f.name+'" class="ib" download><span class="material-symbols-outlined">download</span></a>' +
                        '<button class="ib ib-del" onclick="window.ws.delRec(\''+f.name+'\')"><span class="material-symbols-outlined">delete</span></button>' +
                    '</div>' +
                '</div>').join('');
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