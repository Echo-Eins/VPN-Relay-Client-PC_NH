package main

import (
	"crypto/ecdh"
	"crypto/rand"
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"strings"
	"sync"
	"time"

	"fyne.io/fyne/v2"
	"fyne.io/fyne/v2/app"
	"fyne.io/fyne/v2/container"
	"fyne.io/fyne/v2/widget"
	"github.com/miekg/dns"
	"github.com/pion/dtls/v2"
)

const (
	MULTICAST_ADDR = "224.0.0.251:8888"
	MAGIC_BYTES    = "VPNR"
	SHARED_SECRET  = "2108" // Должен совпадать с сервером

	// Типы пакетов (копируем с сервера)
	PACKET_HTTP     = 1
	PACKET_TCP      = 2
	PACKET_DNS      = 3
	PACKET_UDP      = 4
	PACKET_RESPONSE = 100
	PACKET_ERROR    = 200

	// Ограничения
	MAX_PACKET_SIZE    = 65536
	CONNECTION_TIMEOUT = 10 // секунд
	DISCOVERY_TIMEOUT  = 30 // секунд
	HEARTBEAT_INTERVAL = 60 // секунд
)

// Структуры протокола (идентичны серверу)
type DiscoveryPacket struct {
	Magic     [4]byte
	ClientID  [16]byte
	PublicKey [33]byte
	Timestamp int64
}

type HandshakeResponse struct {
	SessionID [16]byte
	PublicKey [33]byte
	DTLSPort  uint16
}

type PacketHeader struct {
	Type      uint32
	ID        uint32
	Length    uint32
	Timestamp int64
}

// Активное TCP соединение
type ClientTCPConnection struct {
	ID         uint32
	RemoteAddr string
	LocalAddr  string
	State      string // "connecting", "connected", "closed", "error"
	CreatedAt  time.Time
	LastUsed   time.Time
	BytesIn    uint64
	BytesOut   uint64
	mu         sync.RWMutex
}

// Активное UDP соединение
type ClientUDPConnection struct {
	ID         uint32
	RemoteAddr string
	LocalAddr  string
	State      string
	CreatedAt  time.Time
	LastUsed   time.Time
	BytesIn    uint64
	BytesOut   uint64
	mu         sync.RWMutex
}

// Ожидающий ответа запрос
type PendingRequest struct {
	ID          uint32
	Type        uint32
	SentAt      time.Time
	ResponseCh  chan []byte
	ErrorCh     chan error
	Description string
}

// Основной VPN клиент
type VPNClient struct {
	// Сетевые компоненты
	multicastConn *net.UDPConn
	dtlsConn      *dtls.Conn
	serverAddr    *net.UDPAddr

	// Криптографические компоненты
	clientID   [16]byte
	sessionID  [16]byte
	privateKey *ecdh.PrivateKey
	publicKey  *ecdh.PublicKey
	sharedKey  []byte

	// Состояние соединения
	isConnected     bool
	isDiscovering   bool
	connectionState string
	lastHeartbeat   time.Time
	reconnectCount  int

	// Управление соединениями
	tcpConnections      map[uint32]*ClientTCPConnection
	udpConnections      map[uint32]*ClientUDPConnection
	pendingRequests     map[uint32]*PendingRequest
	connectionIDCounter uint32
	requestIDCounter    uint32

	// Статистика
	totalBytesIn      uint64
	totalBytesOut     uint64
	totalPacketsIn    uint64
	totalPacketsOut   uint64
	totalHTTPRequests uint64
	totalDNSQueries   uint64
	connectTime       time.Time

	// DNS кэш клиента
	dnsCache   map[string]*DNSCacheEntry
	dnsCacheMu sync.RWMutex

	// HTTP прокси сервер
	httpProxy     *http.Server
	httpProxyPort int

	// DNS сервер
	dnsServer     *dns.Server
	dnsServerPort int

	// GUI элементы
	statusLabel      *widget.Label
	connectionLabel  *widget.Label
	statsLabel       *widget.Label
	logText          *widget.Entry
	connectButton    *widget.Button
	disconnectButton *widget.Button
	connectionsList  *widget.List

	// Поля настроек
	httpPortEntry *widget.Entry
	dnsPortEntry  *widget.Entry
	serverIPEntry *widget.Entry

	// Каналы управления
	stopChan      chan struct{}
	logChan       chan string
	heartbeatChan chan struct{}

	// Мьютексы
	connMu     sync.RWMutex
	requestsMu sync.RWMutex
	tcpConnMu  sync.RWMutex
	udpConnMu  sync.RWMutex
}

// DNS кэш запись
type DNSCacheEntry struct {
	Response  *dns.Msg
	ExpiresAt time.Time
}

// Создание нового VPN клиента
func NewVPNClient() (*VPNClient, error) {
	// Генерируем ECDH ключи
	curve := ecdh.P256()
	privateKey, err := curve.GenerateKey(rand.Reader)
	if err != nil {
		return nil, fmt.Errorf("failed to generate ECDH key: %v", err)
	}

	// Проверяем формат публичного ключа
	publicKeyBytes := privateKey.PublicKey().Bytes()
	log.Printf("Client public key format: length=%d, prefix=%02x", len(publicKeyBytes), publicKeyBytes[0])

	if len(publicKeyBytes) != 33 || (publicKeyBytes[0] != 0x02 && publicKeyBytes[0] != 0x03) {
		return nil, fmt.Errorf("Unexpected public key format: expected 33 bytes with 0x02/0x03 prefix, got %d bytes with %02x prefix",
			len(publicKeyBytes), publicKeyBytes[0])
	}

	// Генерируем уникальный client ID
	clientID := [16]byte{}
	if _, err := rand.Read(clientID[:]); err != nil {
		return nil, fmt.Errorf("failed to generate client ID: %v", err)
	}

	client := &VPNClient{
		clientID:        clientID,
		privateKey:      privateKey,
		publicKey:       privateKey.PublicKey(),
		connectionState: "Disconnected",
		tcpConnections:  make(map[uint32]*ClientTCPConnection),
		udpConnections:  make(map[uint32]*ClientUDPConnection),
		pendingRequests: make(map[uint32]*PendingRequest),
		dnsCache:        make(map[string]*DNSCacheEntry),
		stopChan:        make(chan struct{}),
		logChan:         make(chan string, 1000),
		heartbeatChan:   make(chan struct{}),
		httpProxyPort:   8080,
		dnsServerPort:   5353,
	}

	// Запускаем фоновые горутины
	go client.heartbeatRoutine()
	go client.cleanupRoutine()

	return client, nil
}

// === DISCOVERY И ПОДКЛЮЧЕНИЕ ===

// Поиск и подключение к серверу
func (c *VPNClient) DiscoverAndConnect() error {
	c.connMu.Lock()
	if c.isConnected || c.isDiscovering {
		c.connMu.Unlock()
		return fmt.Errorf("already connected or discovering")
	}
	c.isDiscovering = true
	c.connectionState = "Discovering..."
	c.connMu.Unlock()

	c.log("Starting server discovery...")

	// Создаем multicast соединение
	addr, err := net.ResolveUDPAddr("udp", MULTICAST_ADDR)
	if err != nil {
		c.setConnectionState("Discovery Failed")
		return fmt.Errorf("failed to resolve multicast address: %v", err)
	}

	// Создаем обычное UDP соединение для отправки multicast
	conn, err := net.DialUDP("udp", nil, addr)
	if err != nil {
		c.setConnectionState("Discovery Failed")
		return fmt.Errorf("failed to create multicast connection: %v", err)
	}
	defer conn.Close()

	// Создаем discovery пакет
	discoveryPacket := c.createDiscoveryPacket()

	// Также создаем UDP соединение для получения ответа
	responseConn, err := net.ListenUDP("udp", &net.UDPAddr{IP: net.IPv4zero, Port: 0})
	if err != nil {
		c.setConnectionState("Discovery Failed")
		return fmt.Errorf("failed to create response listener: %v", err)
	}
	defer responseConn.Close()

	// Отправляем discovery пакет несколько раз
	discoveryAttempts := 3
	for i := 0; i < discoveryAttempts; i++ {
		c.log(fmt.Sprintf("Sending discovery packet (attempt %d/%d)", i+1, discoveryAttempts))

		if _, err := conn.Write(discoveryPacket); err != nil {
			c.log(fmt.Sprintf("Failed to send discovery packet: %v", err))
			continue
		}

		// Ждем ответ с таймаутом
		responseConn.SetReadDeadline(time.Now().Add(5 * time.Second))
		buffer := make([]byte, 1024)

		n, serverAddr, err := responseConn.ReadFromUDP(buffer)
		if err != nil {
			if netErr, ok := err.(net.Error); ok && netErr.Timeout() {
				continue // Таймаут, пробуем еще раз
			}
			c.log(fmt.Sprintf("Error reading discovery response: %v", err))
			continue
		}

		// Парсим ответ
		if n >= 50 { // Минимальный размер HandshakeResponse
			response, err := c.parseHandshakeResponse(buffer[:n])
			if err != nil {
				c.log(fmt.Sprintf("Invalid handshake response: %v", err))
				continue
			}

			c.log(fmt.Sprintf("Server found at %v", serverAddr))

			// Устанавливаем DTLS соединение
			if err := c.connectDTLS(serverAddr, response); err != nil {
				c.log(fmt.Sprintf("DTLS connection failed: %v", err))
				continue
			}

			c.connMu.Lock()
			c.isDiscovering = false
			c.isConnected = true
			c.serverAddr = serverAddr
			c.sessionID = response.SessionID
			c.connectionState = "Connected"
			c.connectTime = time.Now()
			c.connMu.Unlock()

			c.log("Successfully connected to VPN server!")

			// Запускаем обработчик пакетов
			go c.handleServerPackets()

			return nil
		}
	}

	c.connMu.Lock()
	c.isDiscovering = false
	c.connectionState = "Discovery Failed"
	c.connMu.Unlock()

	return fmt.Errorf("server discovery failed after %d attempts", discoveryAttempts)
}

// Создание discovery пакета
func (c *VPNClient) createDiscoveryPacket() []byte {
	packet := DiscoveryPacket{
		ClientID:  c.clientID,
		Timestamp: time.Now().Unix(),
	}

	copy(packet.Magic[:], []byte(MAGIC_BYTES))

	// Получаем публичный ключ и сохраняем в compressed формате
	pubKeyBytes := c.publicKey.Bytes()

	if len(pubKeyBytes) == 33 {
		// Уже в compressed формате
		copy(packet.PublicKey[:], pubKeyBytes)
	} else if len(pubKeyBytes) == 65 && pubKeyBytes[0] == 0x04 {
		// Uncompressed формат - нужно конвертировать в compressed
		// Это сложнее, проще всего пересоздать ключ
		log.Fatalf("Uncompressed public key format not supported in this implementation")
	} else {
		log.Fatalf("Unknown public key format: length=%d, prefix=%02x", len(pubKeyBytes), pubKeyBytes[0])
	}

	// Сериализация пакета - теперь 61 байт (4 + 16 + 33 + 8)
	data := make([]byte, 61)
	copy(data[0:4], packet.Magic[:])
	copy(data[4:20], packet.ClientID[:])
	copy(data[20:53], packet.PublicKey[:])
	binary.LittleEndian.PutUint64(data[53:61], uint64(packet.Timestamp))

	return data
}

// Парсинг handshake ответа
func (c *VPNClient) parseHandshakeResponse(data []byte) (*HandshakeResponse, error) {
	if len(data) < 51 { // Изменено с 50 на 51
		return nil, fmt.Errorf("response too short")
	}

	response := &HandshakeResponse{}
	copy(response.SessionID[:], data[0:16])
	copy(response.PublicKey[:], data[16:49]) // Изменено диапазон
	response.DTLSPort = binary.LittleEndian.Uint16(data[49:51])

	return response, nil
}

// Установка DTLS соединения
func (c *VPNClient) connectDTLS(serverAddr *net.UDPAddr, response *HandshakeResponse) error {
	c.log("Establishing DTLS connection...")

	// Теперь у нас полный compressed публичный ключ сервера
	serverPublicKey, err := ecdh.P256().NewPublicKey(response.PublicKey[:])
	if err != nil {
		return fmt.Errorf("invalid server public key: %v", err)
	}

	sharedSecret, err := c.privateKey.ECDH(serverPublicKey)
	if err != nil {
		return fmt.Errorf("ECDH failed: %v", err)
	}

	// Комбинируем с PSK
	hasher := sha256.New()
	hasher.Write(sharedSecret)
	hasher.Write([]byte(SHARED_SECRET))
	c.sharedKey = hasher.Sum(nil)

	// DTLS конфигурация
	config := &dtls.Config{
		PSK: func(hint []byte) ([]byte, error) {
			return []byte(SHARED_SECRET), nil
		},
		PSKIdentityHint: []byte("vpn-client"),
		CipherSuites:    []dtls.CipherSuiteID{dtls.TLS_PSK_WITH_AES_128_GCM_SHA256},
	}

	// Подключаемся к DTLS серверу
	dtlsAddr := &net.UDPAddr{
		IP:   serverAddr.IP,
		Port: int(response.DTLSPort),
	}

	conn, err := dtls.Dial("udp", dtlsAddr, config)
	if err != nil {
		return fmt.Errorf("DTLS dial failed: %v", err)
	}

	c.dtlsConn = conn
	c.log("DTLS connection established successfully")
	return nil
}

// === ОБРАБОТКА ПАКЕТОВ СЕРВЕРА ===

// Обработка пакетов от сервера
func (c *VPNClient) handleServerPackets() {
	defer c.dtlsConn.Close()
	buffer := make([]byte, MAX_PACKET_SIZE)

	for {
		select {
		case <-c.stopChan:
			return
		default:
		}

		// Читаем пакет
		c.dtlsConn.SetReadDeadline(time.Now().Add(30 * time.Second))
		n, err := c.dtlsConn.Read(buffer)
		if err != nil {
			if netErr, ok := err.(net.Error); ok && netErr.Timeout() {
				continue
			}
			c.log(fmt.Sprintf("Server connection lost: %v", err))
			c.onConnectionLost()
			return
		}

		if n < 20 { // Минимальный размер заголовка
			continue
		}

		// Парсим заголовок
		var header PacketHeader
		header.Type = binary.LittleEndian.Uint32(buffer[0:4])
		header.ID = binary.LittleEndian.Uint32(buffer[4:8])
		header.Length = binary.LittleEndian.Uint32(buffer[8:12])
		header.Timestamp = int64(binary.LittleEndian.Uint64(buffer[12:20]))

		if header.Length > MAX_PACKET_SIZE-20 {
			c.log("Received packet too large, ignoring")
			continue
		}

		payload := buffer[20 : 20+header.Length]

		// Обновляем статистику
		c.connMu.Lock()
		c.totalPacketsIn++
		c.totalBytesIn += uint64(n)
		c.lastHeartbeat = time.Now()
		c.connMu.Unlock()

		// Обрабатываем пакет
		c.handleServerPacket(&header, payload)
	}
}

// Обработка конкретного пакета
func (c *VPNClient) handleServerPacket(header *PacketHeader, payload []byte) {
	switch header.Type {
	case PACKET_RESPONSE:
		c.handleResponse(header.ID, payload)
	case PACKET_ERROR:
		c.handleError(header.ID, payload)
	case PACKET_TCP:
		c.handleTCPData(payload)
	case PACKET_UDP:
		c.handleUDPData(payload)
	default:
		c.log(fmt.Sprintf("Unknown packet type from server: %d", header.Type))
	}
}

// Обработка ответа
func (c *VPNClient) handleResponse(requestID uint32, payload []byte) {
	c.requestsMu.Lock()
	pending, exists := c.pendingRequests[requestID]
	if exists {
		delete(c.pendingRequests, requestID)
	}
	c.requestsMu.Unlock()

	if exists {
		select {
		case pending.ResponseCh <- payload:
		case <-time.After(time.Second):
			// Канал заблокирован
		}
	}
}

// Обработка ошибки
func (c *VPNClient) handleError(requestID uint32, payload []byte) {
	c.requestsMu.Lock()
	pending, exists := c.pendingRequests[requestID]
	if exists {
		delete(c.pendingRequests, requestID)
	}
	c.requestsMu.Unlock()

	if exists {
		errorMsg := string(payload)
		select {
		case pending.ErrorCh <- fmt.Errorf("server error: %s", errorMsg):
		case <-time.After(time.Second):
			// Канал заблокирован
		}
	}
}

// Обработка TCP данных
func (c *VPNClient) handleTCPData(payload []byte) {
	if len(payload) < 5 {
		return
	}

	command := payload[0]
	connID := binary.LittleEndian.Uint32(payload[1:5])
	data := payload[5:]

	if command == 4 { // TCP данные
		c.tcpConnMu.RLock()
		conn, exists := c.tcpConnections[connID]
		c.tcpConnMu.RUnlock()

		if exists {
			conn.mu.Lock()
			conn.BytesIn += uint64(len(data))
			conn.LastUsed = time.Now()
			conn.mu.Unlock()

			c.log(fmt.Sprintf("Received %d bytes for TCP connection %d", len(data), connID))
			// В реальной реализации здесь бы были данные переданы в локальное TCP соединение
		}
	}
}

// Обработка UDP данных
func (c *VPNClient) handleUDPData(payload []byte) {
	if len(payload) < 5 {
		return
	}

	command := payload[0]
	connID := binary.LittleEndian.Uint32(payload[1:5])
	data := payload[5:]

	if command == 4 { // UDP данные
		c.udpConnMu.RLock()
		conn, exists := c.udpConnections[connID]
		c.udpConnMu.RUnlock()

		if exists {
			conn.mu.Lock()
			conn.BytesIn += uint64(len(data))
			conn.LastUsed = time.Now()
			conn.mu.Unlock()

			c.log(fmt.Sprintf("Received %d bytes for UDP connection %d", len(data), connID))
			// В реальной реализации здесь бы были данные переданы в локальное UDP соединение
		}
	}
}

// === ОТПРАВКА ЗАПРОСОВ ===

// Отправка пакета серверу
func (c *VPNClient) sendPacket(packetType uint32, payload []byte) (uint32, error) {
	if !c.isConnected || c.dtlsConn == nil {
		return 0, fmt.Errorf("not connected to server")
	}

	c.connMu.Lock()
	c.requestIDCounter++
	requestID := c.requestIDCounter
	c.connMu.Unlock()

	// Создаем заголовок
	header := PacketHeader{
		Type:      packetType,
		ID:        requestID,
		Length:    uint32(len(payload)),
		Timestamp: time.Now().Unix(),
	}

	// Сериализуем пакет
	packet := make([]byte, 20+len(payload))
	binary.LittleEndian.PutUint32(packet[0:4], header.Type)
	binary.LittleEndian.PutUint32(packet[4:8], header.ID)
	binary.LittleEndian.PutUint32(packet[8:12], header.Length)
	binary.LittleEndian.PutUint64(packet[12:20], uint64(header.Timestamp))
	copy(packet[20:], payload)

	// Отправляем пакет
	_, err := c.dtlsConn.Write(packet)
	if err != nil {
		return 0, fmt.Errorf("failed to send packet: %v", err)
	}

	// Обновляем статистику
	c.connMu.Lock()
	c.totalPacketsOut++
	c.totalBytesOut += uint64(len(packet))
	c.connMu.Unlock()

	return requestID, nil
}

// Отправка запроса с ожиданием ответа
func (c *VPNClient) sendRequest(packetType uint32, payload []byte, description string) ([]byte, error) {
	requestID, err := c.sendPacket(packetType, payload)
	if err != nil {
		return nil, err
	}

	// Создаем pending request
	pending := &PendingRequest{
		ID:          requestID,
		Type:        packetType,
		SentAt:      time.Now(),
		ResponseCh:  make(chan []byte, 1),
		ErrorCh:     make(chan error, 1),
		Description: description,
	}

	c.requestsMu.Lock()
	c.pendingRequests[requestID] = pending
	c.requestsMu.Unlock()

	// Ждем ответ
	timeout := time.NewTimer(CONNECTION_TIMEOUT * time.Second)
	defer timeout.Stop()

	select {
	case response := <-pending.ResponseCh:
		return response, nil
	case err := <-pending.ErrorCh:
		return nil, err
	case <-timeout.C:
		c.requestsMu.Lock()
		delete(c.pendingRequests, requestID)
		c.requestsMu.Unlock()
		return nil, fmt.Errorf("request timeout")
	case <-c.stopChan:
		return nil, fmt.Errorf("client shutting down")
	}
}

// === HTTP ПРОКСИ ===

// HTTP прокси запрос
func (c *VPNClient) MakeHTTPRequest(method, url string, headers map[string]string, body []byte) (*http.Response, error) {
	if !c.isConnected {
		return nil, fmt.Errorf("not connected to VPN server")
	}

	c.log(fmt.Sprintf("Making HTTP request: %s %s", method, url))

	// Парсим URL для получения адреса
	var targetAddr string
	if strings.HasPrefix(url, "http://") {
		url = url[7:] // убираем http://
	} else if strings.HasPrefix(url, "https://") {
		url = url[8:] // убираем https://
	}

	// Находим разделитель между хостом и путем
	parts := strings.SplitN(url, "/", 2)
	host := parts[0]
	path := "/"
	if len(parts) > 1 {
		path = "/" + parts[1]
	}

	// Определяем порт
	if !strings.Contains(host, ":") {
		if strings.HasPrefix(url, "https://") {
			host += ":443"
		} else {
			host += ":80"
		}
	}
	targetAddr = host

	// Формируем HTTP запрос
	httpRequest := fmt.Sprintf("%s %s HTTP/1.1\r\nHost: %s\r\n", method, path, strings.Split(host, ":")[0])

	for key, value := range headers {
		httpRequest += fmt.Sprintf("%s: %s\r\n", key, value)
	}

	if body != nil && len(body) > 0 {
		httpRequest += fmt.Sprintf("Content-Length: %d\r\n", len(body))
	}

	httpRequest += "\r\n"

	if body != nil {
		httpRequest += string(body)
	}

	// Формируем payload
	addrBytes := []byte(targetAddr)
	payload := make([]byte, 2+len(addrBytes)+len(httpRequest))
	binary.LittleEndian.PutUint16(payload[0:2], uint16(len(addrBytes)))
	copy(payload[2:2+len(addrBytes)], addrBytes)
	copy(payload[2+len(addrBytes):], []byte(httpRequest))

	// Отправляем запрос
	response, err := c.sendRequest(PACKET_HTTP, payload, fmt.Sprintf("HTTP %s %s", method, url))
	if err != nil {
		return nil, err
	}

	c.connMu.Lock()
	c.totalHTTPRequests++
	c.connMu.Unlock()

	c.log(fmt.Sprintf("HTTP request completed, got %d bytes", len(response)))

	// Парсим HTTP ответ (упрощенно)
	// В полной реализации здесь был бы полноценный HTTP парсер
	return &http.Response{
		Status:     "200 OK",
		StatusCode: 200,
		Body:       io.NopCloser(strings.NewReader(string(response))),
	}, nil
}

// === TCP ТУННЕЛИРОВАНИЕ ===

// Установка TCP соединения
func (c *VPNClient) EstablishTCPConnection(remoteAddr string) (uint32, error) {
	if !c.isConnected {
		return 0, fmt.Errorf("not connected to VPN server")
	}

	c.connMu.Lock()
	c.connectionIDCounter++
	connID := c.connectionIDCounter
	c.connMu.Unlock()

	c.log(fmt.Sprintf("Establishing TCP connection %d to %s", connID, remoteAddr))

	// Формируем payload: [команда][ID][адрес]
	addrBytes := []byte(remoteAddr)
	payload := make([]byte, 1+4+2+len(addrBytes))
	payload[0] = 1 // команда "connect"
	binary.LittleEndian.PutUint32(payload[1:5], connID)
	binary.LittleEndian.PutUint16(payload[5:7], uint16(len(addrBytes)))
	copy(payload[7:], addrBytes)

	// Отправляем запрос
	_, err := c.sendRequest(PACKET_TCP, payload, fmt.Sprintf("TCP connect to %s", remoteAddr))
	if err != nil {
		return 0, err
	}

	// Создаем запись соединения
	tcpConn := &ClientTCPConnection{
		ID:         connID,
		RemoteAddr: remoteAddr,
		State:      "connected",
		CreatedAt:  time.Now(),
		LastUsed:   time.Now(),
	}

	c.tcpConnMu.Lock()
	c.tcpConnections[connID] = tcpConn
	c.tcpConnMu.Unlock()

	c.log(fmt.Sprintf("TCP connection %d established", connID))
	return connID, nil
}

// Отправка данных через TCP
func (c *VPNClient) SendTCPData(connID uint32, data []byte) error {
	c.tcpConnMu.RLock()
	conn, exists := c.tcpConnections[connID]
	c.tcpConnMu.RUnlock()

	if !exists {
		return fmt.Errorf("TCP connection %d not found", connID)
	}

	// Формируем payload: [команда][ID][данные]
	payload := make([]byte, 5+len(data))
	payload[0] = 2 // команда "send"
	binary.LittleEndian.PutUint32(payload[1:5], connID)
	copy(payload[5:], data)

	_, err := c.sendRequest(PACKET_TCP, payload, fmt.Sprintf("TCP send %d bytes", len(data)))
	if err != nil {
		return err
	}

	conn.mu.Lock()
	conn.BytesOut += uint64(len(data))
	conn.LastUsed = time.Now()
	conn.mu.Unlock()

	return nil
}

// Закрытие TCP соединения
func (c *VPNClient) CloseTCPConnection(connID uint32) error {
	c.tcpConnMu.Lock()
	conn, exists := c.tcpConnections[connID]
	if exists {
		delete(c.tcpConnections, connID)
	}
	c.tcpConnMu.Unlock()

	if !exists {
		return fmt.Errorf("TCP connection %d not found", connID)
	}

	// Формируем payload: [команда][ID]
	payload := make([]byte, 5)
	payload[0] = 3 // команда "close"
	binary.LittleEndian.PutUint32(payload[1:5], connID)

	_, err := c.sendRequest(PACKET_TCP, payload, fmt.Sprintf("TCP close connection %d", connID))
	if err != nil {
		return err
	}

	conn.mu.Lock()
	conn.State = "closed"
	conn.mu.Unlock()

	c.log(fmt.Sprintf("TCP connection %d closed", connID))
	return nil
}

// === UDP ТУННЕЛИРОВАНИЕ ===

// Установка UDP соединения
func (c *VPNClient) EstablishUDPConnection(remoteAddr string) (uint32, error) {
	if !c.isConnected {
		return 0, fmt.Errorf("not connected to VPN server")
	}

	c.connMu.Lock()
	c.connectionIDCounter++
	connID := c.connectionIDCounter
	c.connMu.Unlock()

	c.log(fmt.Sprintf("Establishing UDP connection %d to %s", connID, remoteAddr))

	// Формируем payload: [команда][ID][адрес]
	addrBytes := []byte(remoteAddr)
	payload := make([]byte, 1+4+2+len(addrBytes))
	payload[0] = 1 // команда "connect"
	binary.LittleEndian.PutUint32(payload[1:5], connID)
	binary.LittleEndian.PutUint16(payload[5:7], uint16(len(addrBytes)))
	copy(payload[7:], addrBytes)

	// Отправляем запрос
	_, err := c.sendRequest(PACKET_UDP, payload, fmt.Sprintf("UDP connect to %s", remoteAddr))
	if err != nil {
		return 0, err
	}

	// Создаем запись соединения
	udpConn := &ClientUDPConnection{
		ID:         connID,
		RemoteAddr: remoteAddr,
		State:      "connected",
		CreatedAt:  time.Now(),
		LastUsed:   time.Now(),
	}

	c.udpConnMu.Lock()
	c.udpConnections[connID] = udpConn
	c.udpConnMu.Unlock()

	c.log(fmt.Sprintf("UDP connection %d established", connID))
	return connID, nil
}

// Отправка UDP данных
func (c *VPNClient) SendUDPData(connID uint32, data []byte) error {
	c.udpConnMu.RLock()
	conn, exists := c.udpConnections[connID]
	c.udpConnMu.RUnlock()

	if !exists {
		return fmt.Errorf("UDP connection %d not found", connID)
	}

	// Формируем payload: [команда][ID][данные]
	payload := make([]byte, 5+len(data))
	payload[0] = 2 // команда "send"
	binary.LittleEndian.PutUint32(payload[1:5], connID)
	copy(payload[5:], data)

	_, err := c.sendRequest(PACKET_UDP, payload, fmt.Sprintf("UDP send %d bytes", len(data)))
	if err != nil {
		return err
	}

	conn.mu.Lock()
	conn.BytesOut += uint64(len(data))
	conn.LastUsed = time.Now()
	conn.mu.Unlock()

	return nil
}

// Закрытие UDP соединения
func (c *VPNClient) CloseUDPConnection(connID uint32) error {
	c.udpConnMu.Lock()
	conn, exists := c.udpConnections[connID]
	if exists {
		delete(c.udpConnections, connID)
	}
	c.udpConnMu.Unlock()

	if !exists {
		return fmt.Errorf("UDP connection %d not found", connID)
	}

	// Формируем payload: [команда][ID]
	payload := make([]byte, 5)
	payload[0] = 3 // команда "close"
	binary.LittleEndian.PutUint32(payload[1:5], connID)

	_, err := c.sendRequest(PACKET_UDP, payload, fmt.Sprintf("UDP close connection %d", connID))
	if err != nil {
		return err
	}

	conn.mu.Lock()
	conn.State = "closed"
	conn.mu.Unlock()

	c.log(fmt.Sprintf("UDP connection %d closed", connID))
	return nil
}

// === DNS ЗАПРОСЫ ===

// DNS запрос через туннель
func (c *VPNClient) ResolveDNS(domain string, queryType uint16) (*dns.Msg, error) {
	if !c.isConnected {
		return nil, fmt.Errorf("not connected to VPN server")
	}

	// Проверяем кэш
	cacheKey := fmt.Sprintf("%s:%d", strings.ToLower(domain), queryType)
	if cachedResponse := c.getDNSFromCache(cacheKey); cachedResponse != nil {
		c.log(fmt.Sprintf("DNS query for %s resolved from cache", domain))
		return cachedResponse, nil
	}

	c.log(fmt.Sprintf("Resolving DNS: %s (type %d)", domain, queryType))

	// Создаем DNS запрос
	msg := new(dns.Msg)
	msg.SetQuestion(dns.Fqdn(domain), queryType)
	msg.RecursionDesired = true

	// Сериализуем DNS запрос
	dnsData, err := msg.Pack()
	if err != nil {
		return nil, fmt.Errorf("failed to pack DNS query: %v", err)
	}

	// Отправляем запрос
	response, err := c.sendRequest(PACKET_DNS, dnsData, fmt.Sprintf("DNS query %s", domain))
	if err != nil {
		return nil, err
	}

	// Парсим ответ
	dnsResponse := new(dns.Msg)
	if err := dnsResponse.Unpack(response); err != nil {
		return nil, fmt.Errorf("failed to unpack DNS response: %v", err)
	}

	// Кэшируем ответ
	c.cacheDNSResponse(cacheKey, dnsResponse)

	c.connMu.Lock()
	c.totalDNSQueries++
	c.connMu.Unlock()

	c.log(fmt.Sprintf("DNS query for %s resolved (%d answers)", domain, len(dnsResponse.Answer)))
	return dnsResponse, nil
}

// Получение DNS из кэша
func (c *VPNClient) getDNSFromCache(key string) *dns.Msg {
	c.dnsCacheMu.RLock()
	defer c.dnsCacheMu.RUnlock()

	entry, exists := c.dnsCache[key]
	if !exists || time.Now().After(entry.ExpiresAt) {
		return nil
	}

	return entry.Response.Copy()
}

// Кэширование DNS ответа
func (c *VPNClient) cacheDNSResponse(key string, response *dns.Msg) {
	if response == nil {
		return
	}

	// Определяем TTL
	ttl := uint32(300) // 5 минут по умолчанию
	for _, rr := range response.Answer {
		if rr.Header().Ttl > 0 && rr.Header().Ttl < ttl {
			ttl = rr.Header().Ttl
		}
	}

	if ttl < 60 {
		ttl = 60
	} else if ttl > 3600 {
		ttl = 3600
	}

	entry := &DNSCacheEntry{
		Response:  response.Copy(),
		ExpiresAt: time.Now().Add(time.Duration(ttl) * time.Second),
	}

	c.dnsCacheMu.Lock()
	c.dnsCache[key] = entry
	c.dnsCacheMu.Unlock()
}

// === ЛОКАЛЬНЫЕ СЕРВИСЫ ===

// Запуск HTTP прокси сервера
func (c *VPNClient) StartHTTPProxy() error {
	if c.httpProxy != nil {
		return fmt.Errorf("HTTP proxy already running")
	}

	handler := http.HandlerFunc(c.handleHTTPProxyRequest)
	c.httpProxy = &http.Server{
		Addr:    fmt.Sprintf(":%d", c.httpProxyPort),
		Handler: handler,
	}

	go func() {
		c.log(fmt.Sprintf("Starting HTTP proxy on port %d", c.httpProxyPort))
		if err := c.httpProxy.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			c.log(fmt.Sprintf("HTTP proxy error: %v", err))
		}
	}()

	return nil
}

// Обработка HTTP прокси запросов
func (c *VPNClient) handleHTTPProxyRequest(w http.ResponseWriter, r *http.Request) {
	c.log(fmt.Sprintf("HTTP Proxy: %s %s", r.Method, r.URL.String()))

	// Читаем тело запроса
	body, err := io.ReadAll(r.Body)
	if err != nil {
		http.Error(w, "Failed to read request body", http.StatusBadRequest)
		return
	}
	r.Body.Close()

	// Извлекаем заголовки
	headers := make(map[string]string)
	for name, values := range r.Header {
		if len(values) > 0 {
			headers[name] = values[0]
		}
	}

	// Выполняем запрос через туннель
	response, err := c.MakeHTTPRequest(r.Method, r.URL.String(), headers, body)
	if err != nil {
		c.log(fmt.Sprintf("HTTP proxy request failed: %v", err))
		http.Error(w, err.Error(), http.StatusBadGateway)
		return
	}
	defer response.Body.Close()

	// Копируем заголовки ответа
	for key, values := range response.Header {
		for _, value := range values {
			w.Header().Add(key, value)
		}
	}

	w.WriteHeader(response.StatusCode)

	// Копируем тело ответа
	if _, err := io.Copy(w, response.Body); err != nil {
		c.log(fmt.Sprintf("Failed to copy response body: %v", err))
	}
}

// Остановка HTTP прокси
func (c *VPNClient) StopHTTPProxy() error {
	if c.httpProxy == nil {
		return nil
	}

	err := c.httpProxy.Close()
	c.httpProxy = nil
	c.log("HTTP proxy stopped")
	return err
}

// Запуск DNS сервера
func (c *VPNClient) StartDNSServer() error {
	if c.dnsServer != nil {
		return fmt.Errorf("DNS server already running")
	}

	mux := dns.NewServeMux()
	mux.HandleFunc(".", c.handleDNSRequest)

	c.dnsServer = &dns.Server{
		Addr:    fmt.Sprintf(":%d", c.dnsServerPort),
		Net:     "udp",
		Handler: mux,
	}

	go func() {
		c.log(fmt.Sprintf("Starting DNS server on port %d", c.dnsServerPort))
		if err := c.dnsServer.ListenAndServe(); err != nil {
			c.log(fmt.Sprintf("DNS server error: %v", err))
		}
	}()

	return nil
}

// Обработка DNS запросов
func (c *VPNClient) handleDNSRequest(w dns.ResponseWriter, r *dns.Msg) {
	if len(r.Question) == 0 {
		return
	}

	question := r.Question[0]
	c.log(fmt.Sprintf("DNS Server: query for %s (type %d)", question.Name, question.Qtype))

	// Выполняем запрос через туннель
	response, err := c.ResolveDNS(strings.TrimSuffix(question.Name, "."), question.Qtype)
	if err != nil {
		c.log(fmt.Sprintf("DNS resolution failed: %v", err))

		// Отправляем ошибку
		msg := new(dns.Msg)
		msg.SetReply(r)
		msg.SetRcode(r, dns.RcodeServerFailure)
		w.WriteMsg(msg)
		return
	}

	// Отправляем ответ
	response.SetReply(r)
	w.WriteMsg(response)
}

// Остановка DNS сервера
func (c *VPNClient) StopDNSServer() error {
	if c.dnsServer == nil {
		return nil
	}

	err := c.dnsServer.Shutdown()
	c.dnsServer = nil
	c.log("DNS server stopped")
	return err
}

// === УПРАВЛЕНИЕ СОЕДИНЕНИЕМ ===

// Обработка потери соединения
func (c *VPNClient) onConnectionLost() {
	c.connMu.Lock()
	c.isConnected = false
	c.connectionState = "Connection Lost"
	c.reconnectCount++
	c.connMu.Unlock()

	c.log("Connection to server lost")

	// Очищаем соединения
	c.tcpConnMu.Lock()
	for _, conn := range c.tcpConnections {
		conn.mu.Lock()
		conn.State = "disconnected"
		conn.mu.Unlock()
	}
	c.tcpConnMu.Unlock()

	c.udpConnMu.Lock()
	for _, conn := range c.udpConnections {
		conn.mu.Lock()
		conn.State = "disconnected"
		conn.mu.Unlock()
	}
	c.udpConnMu.Unlock()

	// Очищаем pending requests
	c.requestsMu.Lock()
	for _, pending := range c.pendingRequests {
		select {
		case pending.ErrorCh <- fmt.Errorf("connection lost"):
		default:
		}
	}
	c.pendingRequests = make(map[uint32]*PendingRequest)
	c.requestsMu.Unlock()
}

// Отключение от сервера
func (c *VPNClient) Disconnect() error {
	c.connMu.Lock()
	defer c.connMu.Unlock()

	if !c.isConnected {
		return fmt.Errorf("not connected")
	}

	c.log("Disconnecting from server...")

	// Закрываем DTLS соединение
	if c.dtlsConn != nil {
		c.dtlsConn.Close()
		c.dtlsConn = nil
	}

	c.isConnected = false
	c.connectionState = "Disconnected"

	// Останавливаем локальные сервисы
	c.StopHTTPProxy()
	c.StopDNSServer()

	c.log("Disconnected from server")
	return nil
}

// === ФОНОВЫЕ ГОРУТИНЫ ===

// Heartbeat горутина
func (c *VPNClient) heartbeatRoutine() {
	ticker := time.NewTicker(HEARTBEAT_INTERVAL * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-c.stopChan:
			return
		case <-ticker.C:
			if c.isConnected {
				// Отправляем heartbeat (можно использовать пустой DNS запрос)
				go func() {
					_, err := c.ResolveDNS("heartbeat.local", dns.TypeA)
					if err != nil {
						c.log(fmt.Sprintf("Heartbeat failed: %v", err))
					}
				}()
			}
		}
	}
}

// Cleanup горутина
func (c *VPNClient) cleanupRoutine() {
	ticker := time.NewTicker(60 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-c.stopChan:
			return
		case <-ticker.C:
			c.cleanupExpiredRequests()
			c.cleanupDNSCache()
		}
	}
}

// Очистка просроченных запросов
func (c *VPNClient) cleanupExpiredRequests() {
	c.requestsMu.Lock()
	defer c.requestsMu.Unlock()

	now := time.Now()
	for id, pending := range c.pendingRequests {
		if now.Sub(pending.SentAt) > CONNECTION_TIMEOUT*time.Second {
			select {
			case pending.ErrorCh <- fmt.Errorf("request timeout"):
			default:
			}
			delete(c.pendingRequests, id)
		}
	}
}

// Очистка DNS кэша
func (c *VPNClient) cleanupDNSCache() {
	c.dnsCacheMu.Lock()
	defer c.dnsCacheMu.Unlock()

	now := time.Now()
	for key, entry := range c.dnsCache {
		if now.After(entry.ExpiresAt) {
			delete(c.dnsCache, key)
		}
	}
}

// === УТИЛИТЫ ===

// Установка состояния соединения
func (c *VPNClient) setConnectionState(state string) {
	c.connMu.Lock()
	c.connectionState = state
	c.connMu.Unlock()
}

// Логирование
func (c *VPNClient) log(message string) {
	timestamp := time.Now().Format("15:04:05")
	logMessage := fmt.Sprintf("[%s] %s", timestamp, message)

	select {
	case c.logChan <- logMessage:
	default:
		// Канал переполнен
	}

	log.Println(message)
}

// === GUI ===

// Создание GUI интерфейса
func (c *VPNClient) CreateGUI() fyne.Window {
	myApp := app.New()
	myWindow := myApp.NewWindow("VPN Relay Client")
	myWindow.Resize(fyne.NewSize(900, 700))

	// Статус соединения
	c.statusLabel = widget.NewLabel("Status: Disconnected")
	c.statusLabel.TextStyle.Bold = true

	c.connectionLabel = widget.NewLabel("Server: Not connected")

	// Кнопки управления
	c.connectButton = widget.NewButton("Connect to Server", func() {
		go func() {
			c.connectButton.Disable()
			if err := c.DiscoverAndConnect(); err != nil {
				c.log(fmt.Sprintf("Connection failed: %v", err))
			}
			c.connectButton.Enable()
		}()
	})

	c.disconnectButton = widget.NewButton("Disconnect", func() {
		go c.Disconnect()
	})
	c.disconnectButton.Disable()

	// Настройки
	c.serverIPEntry = widget.NewEntry()
	c.serverIPEntry.SetText("Auto-discovery")
	c.serverIPEntry.Disable() // В этой реализации используется только auto-discovery

	c.httpPortEntry = widget.NewEntry()
	c.httpPortEntry.SetText(fmt.Sprintf("%d", c.httpProxyPort))
	c.httpPortEntry.OnChanged = func(text string) {
		if port := parseInt(text); port > 0 && port < 65536 {
			c.httpProxyPort = port
		}
	}

	c.dnsPortEntry = widget.NewEntry()
	c.dnsPortEntry.SetText(fmt.Sprintf("%d", c.dnsServerPort))
	c.dnsPortEntry.OnChanged = func(text string) {
		if port := parseInt(text); port > 0 && port < 65536 {
			c.dnsServerPort = port
		}
	}

	// Кнопки сервисов
	startHTTPButton := widget.NewButton("Start HTTP Proxy", func() {
		if err := c.StartHTTPProxy(); err != nil {
			c.log(fmt.Sprintf("Failed to start HTTP proxy: %v", err))
		}
	})

	stopHTTPButton := widget.NewButton("Stop HTTP Proxy", func() {
		c.StopHTTPProxy()
	})

	startDNSButton := widget.NewButton("Start DNS Server", func() {
		if err := c.StartDNSServer(); err != nil {
			c.log(fmt.Sprintf("Failed to start DNS server: %v", err))
		}
	})

	stopDNSButton := widget.NewButton("Stop DNS Server", func() {
		c.StopDNSServer()
	})

	// Тестовые кнопки
	testHTTPButton := widget.NewButton("Test HTTP", func() {
		go func() {
			_, err := c.MakeHTTPRequest("GET", "http://httpbin.org/ip", nil, nil)
			if err != nil {
				c.log(fmt.Sprintf("HTTP test failed: %v", err))
			} else {
				c.log("HTTP test successful")
			}
		}()
	})

	testDNSButton := widget.NewButton("Test DNS", func() {
		go func() {
			_, err := c.ResolveDNS("google.com", dns.TypeA)
			if err != nil {
				c.log(fmt.Sprintf("DNS test failed: %v", err))
			} else {
				c.log("DNS test successful")
			}
		}()
	})

	testTCPButton := widget.NewButton("Test TCP", func() {
		go func() {
			connID, err := c.EstablishTCPConnection("google.com:80")
			if err != nil {
				c.log(fmt.Sprintf("TCP test failed: %v", err))
				return
			}

			httpRequest := "GET / HTTP/1.1\r\nHost: google.com\r\n\r\n"
			err = c.SendTCPData(connID, []byte(httpRequest))
			if err != nil {
				c.log(fmt.Sprintf("TCP send failed: %v", err))
				return
			}

			c.log("TCP test successful")

			// Закрываем через секунду
			time.Sleep(time.Second)
			c.CloseTCPConnection(connID)
		}()
	})

	// Статистика
	c.statsLabel = widget.NewLabel("Statistics: No data")

	// Список соединений
	c.connectionsList = widget.NewList(
		func() int {
			c.tcpConnMu.RLock()
			c.udpConnMu.RLock()
			count := len(c.tcpConnections) + len(c.udpConnections)
			c.udpConnMu.RUnlock()
			c.tcpConnMu.RUnlock()
			return count
		},
		func() fyne.CanvasObject {
			return widget.NewLabel("Template")
		},
		func(id widget.ListItemID, obj fyne.CanvasObject) {
			c.tcpConnMu.RLock()
			c.udpConnMu.RLock()
			defer c.udpConnMu.RUnlock()
			defer c.tcpConnMu.RUnlock()

			label := obj.(*widget.Label)
			i := 0

			for connID, conn := range c.tcpConnections {
				if i == id {
					conn.mu.RLock()
					text := fmt.Sprintf("TCP %d -> %s [%s] In:%.1fKB Out:%.1fKB",
						connID, conn.RemoteAddr, conn.State,
						float64(conn.BytesIn)/1024, float64(conn.BytesOut)/1024)
					conn.mu.RUnlock()
					label.SetText(text)
					return
				}
				i++
			}

			for connID, conn := range c.udpConnections {
				if i == id {
					conn.mu.RLock()
					text := fmt.Sprintf("UDP %d -> %s [%s] In:%.1fKB Out:%.1fKB",
						connID, conn.RemoteAddr, conn.State,
						float64(conn.BytesIn)/1024, float64(conn.BytesOut)/1024)
					conn.mu.RUnlock()
					label.SetText(text)
					return
				}
				i++
			}
		},
	)

	// Лог
	c.logText = widget.NewMultiLineEntry()
	c.logText.SetText("VPN Client log will appear here...\n")
	c.logText.Wrapping = fyne.TextWrapWord
	logScroll := container.NewScroll(c.logText)
	logScroll.SetMinSize(fyne.NewSize(400, 300))

	// Компоновка
	// Верхняя панель - статус и управление
	statusContainer := container.NewVBox(
		c.statusLabel,
		c.connectionLabel,
		c.statsLabel,
	)

	connectionContainer := container.NewHBox(
		c.connectButton,
		c.disconnectButton,
	)

	// Настройки
	settingsContainer := container.NewVBox(
		widget.NewLabel("Settings:"),
		widget.NewForm(
			widget.NewFormItem("Server", c.serverIPEntry),
			widget.NewFormItem("HTTP Proxy Port", c.httpPortEntry),
			widget.NewFormItem("DNS Server Port", c.dnsPortEntry),
		),
	)

	// Сервисы
	servicesContainer := container.NewVBox(
		widget.NewLabel("Local Services:"),
		container.NewHBox(startHTTPButton, stopHTTPButton),
		container.NewHBox(startDNSButton, stopDNSButton),
	)

	// Тесты
	testsContainer := container.NewVBox(
		widget.NewLabel("Tests:"),
		container.NewHBox(testHTTPButton, testDNSButton, testTCPButton),
	)

	// Соединения
	connectionsContainer := container.NewVBox(
		widget.NewLabel("Active Connections:"),
		container.NewBorder(nil, nil, nil, nil, c.connectionsList),
	)

	// Левая панель
	leftPanel := container.NewVBox(
		statusContainer,
		widget.NewSeparator(),
		connectionContainer,
		widget.NewSeparator(),
		settingsContainer,
		widget.NewSeparator(),
		servicesContainer,
		widget.NewSeparator(),
		testsContainer,
		widget.NewSeparator(),
		connectionsContainer,
	)

	// Лог панель
	logPanel := container.NewVBox(
		widget.NewLabel("Log:"),
		logScroll,
	)

	// Основная компоновка
	content := container.NewHSplit(leftPanel, logPanel)
	content.SetOffset(0.4)

	myWindow.SetContent(content)

	// Запускаем обновление GUI
	go c.updateGUI()

	// Обработчик закрытия
	myWindow.SetCloseIntercept(func() {
		c.Shutdown()
		myWindow.Close()
	})

	return myWindow
}

// Обновление GUI
func (c *VPNClient) updateGUI() {
	ticker := time.NewTicker(time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-c.stopChan:
			return
		case logMessage := <-c.logChan:
			if c.logText != nil {
				currentText := c.logText.Text
				newText := currentText + logMessage + "\n"

				// Ограничиваем размер лога
				lines := strings.Split(newText, "\n")
				if len(lines) > 1000 {
					lines = lines[len(lines)-1000:]
					newText = strings.Join(lines, "\n")
				}

				c.logText.SetText(newText)
				c.logText.CursorRow = len(lines) - 1
			}
		case <-ticker.C:
			c.updateStatus()
		}
	}
}

// Обновление статуса
func (c *VPNClient) updateStatus() {
	if c.statusLabel == nil {
		return
	}

	c.connMu.RLock()
	isConnected := c.isConnected
	connectionState := c.connectionState
	c.connMu.RUnlock()

	// Обновляем статус
	if isConnected {
		c.statusLabel.SetText("Status: Connected")
		if c.serverAddr != nil {
			c.connectionLabel.SetText(fmt.Sprintf("Server: %s", c.serverAddr.String()))
		}
		c.connectButton.Disable()
		c.disconnectButton.Enable()
	} else {
		c.statusLabel.SetText(fmt.Sprintf("Status: %s", connectionState))
		c.connectionLabel.SetText("Server: Not connected")
		c.connectButton.Enable()
		c.disconnectButton.Disable()
	}

	// Обновляем статистику
	uptime := time.Duration(0)
	if isConnected {
		uptime = time.Since(c.connectTime)
	}

	c.connMu.RLock()
	c.tcpConnMu.RLock()
	c.udpConnMu.RLock()
	c.requestsMu.RLock()

	statsText := fmt.Sprintf(
		"Uptime: %v | Reconnects: %d\n"+
			"Traffic In: %.2f MB | Traffic Out: %.2f MB\n"+
			"Packets In: %d | Packets Out: %d\n"+
			"HTTP Requests: %d | DNS Queries: %d\n"+
			"TCP Connections: %d | UDP Connections: %d | Pending Requests: %d\n"+
			"DNS Cache: %d entries",
		uptime.Truncate(time.Second),
		c.reconnectCount,
		float64(c.totalBytesIn)/(1024*1024),
		float64(c.totalBytesOut)/(1024*1024),
		c.totalPacketsIn,
		c.totalPacketsOut,
		c.totalHTTPRequests,
		c.totalDNSQueries,
		len(c.tcpConnections),
		len(c.udpConnections),
		len(c.pendingRequests),
		len(c.dnsCache),
	)

	c.requestsMu.RUnlock()
	c.udpConnMu.RUnlock()
	c.tcpConnMu.RUnlock()
	c.connMu.RUnlock()

	c.statsLabel.SetText(statsText)

	// Обновляем список соединений
	if c.connectionsList != nil {
		c.connectionsList.Refresh()
	}
}

// === УПРАВЛЕНИЕ ЖИЗНЕННЫМ ЦИКЛОМ ===

// Завершение работы клиента
func (c *VPNClient) Shutdown() {
	c.log("Shutting down VPN client...")

	// Сигнализируем о завершении
	select {
	case <-c.stopChan:
		// Уже закрыт
	default:
		close(c.stopChan)
	}

	// Отключаемся от сервера
	c.Disconnect()

	// Останавливаем локальные сервисы
	c.StopHTTPProxy()
	c.StopDNSServer()

	// Закрываем все соединения
	c.tcpConnMu.Lock()
	for _, conn := range c.tcpConnections {
		conn.mu.Lock()
		conn.State = "shutdown"
		conn.mu.Unlock()
	}
	c.tcpConnections = make(map[uint32]*ClientTCPConnection)
	c.tcpConnMu.Unlock()

	c.udpConnMu.Lock()
	for _, conn := range c.udpConnections {
		conn.mu.Lock()
		conn.State = "shutdown"
		conn.mu.Unlock()
	}
	c.udpConnections = make(map[uint32]*ClientUDPConnection)
	c.udpConnMu.Unlock()

	// Очищаем pending requests
	c.requestsMu.Lock()
	for _, pending := range c.pendingRequests {
		select {
		case pending.ErrorCh <- fmt.Errorf("client shutting down"):
		default:
		}
	}
	c.pendingRequests = make(map[uint32]*PendingRequest)
	c.requestsMu.Unlock()

	// Очищаем DNS кэш
	c.dnsCacheMu.Lock()
	c.dnsCache = make(map[string]*DNSCacheEntry)
	c.dnsCacheMu.Unlock()

	c.log("VPN client shutdown complete")
}

// === ДОПОЛНИТЕЛЬНЫЕ МЕТОДЫ ===

// Получение информации о соединении
func (c *VPNClient) GetConnectionInfo() map[string]interface{} {
	c.connMu.RLock()
	defer c.connMu.RUnlock()

	info := map[string]interface{}{
		"connected":           c.isConnected,
		"connection_state":    c.connectionState,
		"client_id":           fmt.Sprintf("%x", c.clientID),
		"session_id":          fmt.Sprintf("%x", c.sessionID),
		"server_addr":         "",
		"connect_time":        c.connectTime,
		"reconnect_count":     c.reconnectCount,
		"total_bytes_in":      c.totalBytesIn,
		"total_bytes_out":     c.totalBytesOut,
		"total_packets_in":    c.totalPacketsIn,
		"total_packets_out":   c.totalPacketsOut,
		"total_http_requests": c.totalHTTPRequests,
		"total_dns_queries":   c.totalDNSQueries,
	}

	if c.serverAddr != nil {
		info["server_addr"] = c.serverAddr.String()
	}

	return info
}

// Получение списка активных TCP соединений
func (c *VPNClient) GetTCPConnections() []*ClientTCPConnection {
	c.tcpConnMu.RLock()
	defer c.tcpConnMu.RUnlock()

	connections := make([]*ClientTCPConnection, 0, len(c.tcpConnections))
	for _, conn := range c.tcpConnections {
		// Создаем копию для безопасности
		connCopy := &ClientTCPConnection{
			ID:         conn.ID,
			RemoteAddr: conn.RemoteAddr,
			LocalAddr:  conn.LocalAddr,
			State:      conn.State,
			CreatedAt:  conn.CreatedAt,
			LastUsed:   conn.LastUsed,
			BytesIn:    conn.BytesIn,
			BytesOut:   conn.BytesOut,
		}
		connections = append(connections, connCopy)
	}

	return connections
}

// Получение списка активных UDP соединений
func (c *VPNClient) GetUDPConnections() []*ClientUDPConnection {
	c.udpConnMu.RLock()
	defer c.udpConnMu.RUnlock()

	connections := make([]*ClientUDPConnection, 0, len(c.udpConnections))
	for _, conn := range c.udpConnections {
		// Создаем копию для безопасности
		connCopy := &ClientUDPConnection{
			ID:         conn.ID,
			RemoteAddr: conn.RemoteAddr,
			LocalAddr:  conn.LocalAddr,
			State:      conn.State,
			CreatedAt:  conn.CreatedAt,
			LastUsed:   conn.LastUsed,
			BytesIn:    conn.BytesIn,
			BytesOut:   conn.BytesOut,
		}
		connections = append(connections, connCopy)
	}

	return connections
}

// Получение статистики DNS кэша
func (c *VPNClient) GetDNSCacheStats() map[string]interface{} {
	c.dnsCacheMu.RLock()
	defer c.dnsCacheMu.RUnlock()

	totalEntries := len(c.dnsCache)
	expiredEntries := 0
	now := time.Now()

	for _, entry := range c.dnsCache {
		if now.After(entry.ExpiresAt) {
			expiredEntries++
		}
	}

	return map[string]interface{}{
		"total_entries":   totalEntries,
		"expired_entries": expiredEntries,
		"active_entries":  totalEntries - expiredEntries,
	}
}

// Очистка DNS кэша принудительно
func (c *VPNClient) ClearDNSCache() {
	c.dnsCacheMu.Lock()
	defer c.dnsCacheMu.Unlock()

	c.dnsCache = make(map[string]*DNSCacheEntry)
	c.log("DNS cache cleared")
}

// Получение списка ожидающих запросов
func (c *VPNClient) GetPendingRequests() []map[string]interface{} {
	c.requestsMu.RLock()
	defer c.requestsMu.RUnlock()

	requests := make([]map[string]interface{}, 0, len(c.pendingRequests))
	for _, pending := range c.pendingRequests {
		request := map[string]interface{}{
			"id":          pending.ID,
			"type":        pending.Type,
			"description": pending.Description,
			"sent_at":     pending.SentAt,
			"age":         time.Since(pending.SentAt),
		}
		requests = append(requests, request)
	}

	return requests
}

// === УТИЛИТЫ ===

// Парсинг целого числа
func parseInt(s string) int {
	var result int
	for _, c := range s {
		if c >= '0' && c <= '9' {
			result = result*10 + int(c-'0')
		} else {
			return 0
		}
	}
	return result
}

// Форматирование байтов
func formatBytes(bytes uint64) string {
	const unit = 1024
	if bytes < unit {
		return fmt.Sprintf("%d B", bytes)
	}
	div, exp := uint64(unit), 0
	for n := bytes / unit; n >= unit; n /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.1f %cB", float64(bytes)/float64(div), "KMGTPE"[exp])
}

// Форматирование времени
func formatDuration(d time.Duration) string {
	if d < time.Minute {
		return fmt.Sprintf("%.0fs", d.Seconds())
	}
	if d < time.Hour {
		return fmt.Sprintf("%.0fm%.0fs", d.Minutes(), d.Seconds()-60*d.Minutes())
	}
	if d < 24*time.Hour {
		return fmt.Sprintf("%.0fh%.0fm", d.Hours(), d.Minutes()-60*d.Hours())
	}
	return fmt.Sprintf("%.0fd%.0fh", d.Hours()/24, d.Hours()-24*(d.Hours()/24))
}

// === ТОЧКА ВХОДА ===

// Основная функция
func main() {
	// Создаем VPN клиент
	client, err := NewVPNClient()
	if err != nil {
		log.Fatalf("Failed to create VPN client: %v", err)
	}

	// Создаем и отображаем GUI
	window := client.CreateGUI()

	client.log("VPN Relay Client started")
	client.log(fmt.Sprintf("Client ID: %x", client.clientID))
	client.log("Use 'Connect to Server' to discover and connect to VPN relay")
	client.log("Configure HTTP proxy and DNS server ports in settings")

	// Запускаем приложение
	window.ShowAndRun()
}
