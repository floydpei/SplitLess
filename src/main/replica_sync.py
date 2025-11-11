import json
from network_handler import UDPNetworkHandler, NetworkMessage, MessageType
from data_handler import DataHandler
import sys, threading

print_lock = threading.Lock()


class ReplicaSync:
    network_handler: UDPNetworkHandler = None
    user_id: str = None

    @staticmethod
    def start_listener(user_id: str, host="127.0.0.1", port=0):

        if ReplicaSync.network_handler:
            ReplicaSync.safe_print("[ReplicaSync] Listener already running.")
            return

        ReplicaSync.user_id = user_id
        ReplicaSync.network_handler = UDPNetworkHandler(
            host=host,
            port=port,
            on_message=ReplicaSync._handle_message
        )
        ReplicaSync.network_handler.start()

    @staticmethod
    def stop_listener():
        if not ReplicaSync.network_handler:
            ReplicaSync.safe_print("[ReplicaSync] Listener not active.")
            return
        ReplicaSync.network_handler.stop()
        ReplicaSync.network_handler = None
        ReplicaSync.safe_print("[ReplicaSync] Listener stopped.")


    @staticmethod
    def address():
        if ReplicaSync.network_handler:
            return ReplicaSync.network_handler.address()
        return None

    @staticmethod
    def _handle_message(msg: NetworkMessage, addr):
        ReplicaSync.safe_print(f"[ReplicaSync] Received {msg.type.name} from {addr}")

        if msg.type == MessageType.REPLICA_UPDATE:
            ReplicaSync._handle_replica_update(msg, addr)
        elif msg.type == MessageType.REQUEST_REPLICA:
            ReplicaSync._handle_replica_request(addr)
        else:
            ReplicaSync.safe_print(f"[ReplicaSync] Unhandled message type: {msg.type.name}")

    @staticmethod
    def _handle_replica_update(msg: NetworkMessage, addr):
        """Handle an incoming full replica update."""
        payload = msg.payload
        replica_data = payload.get("replica_data")
        sender = payload.get("sender_id")

        if not replica_data or not sender:
            ReplicaSync.safe_print("[ReplicaSync] Invalid REPLICA_UPDATE message.")
            return

        # Later call DataHandler.merge_replica(replica_data)

    @staticmethod
    def _handle_replica_request(addr):
        ReplicaSync.safe_print(f"[ReplicaSync] Peer at {addr} requested our replica.")
        ReplicaSync.send_full_replica(addr[0], addr[1])


    @staticmethod
    def send_full_replica(target_host: str, target_port: int):
        if not ReplicaSync.network_handler:
            ReplicaSync.safe_print("[ReplicaSync] Listener not running — cannot send.")
            return

        replica = DataHandler.get_user_replica(ReplicaSync.user_id)
        msg = NetworkMessage(
            MessageType.REPLICA_UPDATE,
            {
                "sender_id": ReplicaSync.user_id,
                "replica_data": replica
            }
        )
        ReplicaSync.network_handler.send_message(msg, target_host, target_port)
        ReplicaSync.safe_print(f"[ReplicaSync] Sent replica to {target_host}:{target_port}")

    @staticmethod
    def request_replica(target_host: str, target_port: int):
        if not ReplicaSync.network_handler:
            ReplicaSync.safe_print("[ReplicaSync] Listener not running — cannot request.")
            return

        msg = NetworkMessage(
            MessageType.REQUEST_REPLICA,
            {"sender_id": ReplicaSync.user_id}
        )
        ReplicaSync.network_handler.send_message(msg, target_host, target_port)
        ReplicaSync.safe_print(f"[ReplicaSync] Requested replica from {target_host}:{target_port}")

    @staticmethod
    def safe_print(*args, **kwargs):
        with print_lock:
            print(*args, **kwargs)
            sys.stdout.write("splitless> ")
            sys.stdout.flush()