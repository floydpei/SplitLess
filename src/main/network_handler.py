import socket
import threading
import json
from enum import Enum, auto
import sys, threading

print_lock = threading.Lock()


class MessageType(Enum):
    REPLICA_UPDATE = auto()
    REQUEST_REPLICA = auto()


class NetworkMessage:
    def __init__(self, msg_type: MessageType, payload: dict):
        self.type = msg_type
        self.payload = payload

    def to_json(self) -> str:
        return json.dumps({
            "type": self.type.name,
            "payload": self.payload
        })

    @staticmethod
    def from_json(data: str):
        obj = json.loads(data)
        msg_type = MessageType[obj["type"]]
        return NetworkMessage(msg_type, obj["payload"])


class UDPNetworkHandler:

    def __init__(self, host="127.0.0.1", port=0, on_message=None):
        #If port=0, the OS will choose a free port.

        self.host = host
        self.port = port
        self.on_message = on_message
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.running = False

    def start(self):
        # start listening for incoming UDP messages
        self.socket.bind((self.host, self.port))
        self.port = self.socket.getsockname()[1]
        self.running = True
        #self.safe_print(f"[UDP] Listening on {self.host}:{self.port}")
        threading.Thread(target=self.listen_loop, daemon=True).start()

    def listen_loop(self):
        # receive messages
        while self.running:
            try:
                data, addr = self.socket.recvfrom(8192)
                msg = NetworkMessage.from_json(data.decode())
                if self.on_message:
                    try:
                        self.on_message(msg, addr)
                    except Exception as e:
                        if self.running:
                            self.safe_print(f"[UDP] Error handeling message {msg.type.name}: {e}")
                            
                else:
                    self.safe_print(f"[UDP] Received {msg.type.name} from {addr}")#: {msg.payload}")
            except Exception as e:
                if self.running:
                    self.safe_print(f"[UDP] Error receiving message: {e}")

    def send_message(self, msg: NetworkMessage, target_host: str, target_port: int):
        try:
            #self.safe_print("Send message of type: " + msg.type.name)
            self.socket.sendto(msg.to_json().encode(), (target_host, target_port))
        except Exception as e:
            self.safe_print(f"[UDP] Failed to send message: {e}")

    def address(self):
        return (self.host, self.port)
    
    def stop(self):
        self.running = False
        self.socket.close()
        #self.safe_print("[UDP] Listener stopped.")

    def safe_print(*args, **kwargs):
        with print_lock:
            print(*args, **kwargs)
            sys.stdout.write("splitless> ")
            sys.stdout.flush()
