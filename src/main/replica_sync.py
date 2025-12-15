import json
from network_handler import UDPNetworkHandler, NetworkMessage, MessageType
from data_handler import DataHandler
from balance_handler import BalanceHandler
import sys, threading
from storage_provider import get_backend

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
        payload = msg.payload
        replica_data = payload.get("replica_data")
        sender = payload.get("sender_id")

        if not replica_data or not sender:
            ReplicaSync.safe_print("[ReplicaSync] Invalid REPLICA_UPDATE message.")
            return -1

        ReplicaSync.safe_print("[ReplicaSync] Merging replicas...")
        ReplicaSync._merge_replica(other_replica=replica_data)
        ReplicaSync.safe_print("[ReplicaSync] Finished merging replicas.")


    @staticmethod
    def _merge_replica(other_replica):
        backend = get_backend()
        own_replica = backend.get_full_replica(ReplicaSync.user_id)
        own_expenses = own_replica.get("recorded_expenses")
        own_groups = own_replica.get("groups")
        own_users = own_replica.get("known_users")

        other_expenses = other_replica.get("recorded_expenses")
        other_groups = other_replica.get("groups")
        other_users = other_replica.get("known_users")

        merged_expenses = ReplicaSync._merge_expenses(own_expenses=own_expenses, other_expenses=other_expenses)
        merged_groups = ReplicaSync._merge_groups(own_groups=own_groups, other_groups=other_groups)
        merged_users = ReplicaSync._merge_known_users(own_users=own_users, other_users=other_users)

        #print("merged expenses: ")
        #print(merged_expenses)
        #print("merged groups: ")
        #print(merged_groups)
        #print("merged users: ")
        #print(merged_users)

        merged_replica = {
            **own_replica,
            "recorded_expenses": merged_expenses,
            "groups": merged_groups,
            "known_users": merged_users
        }

        backend.write_full_replica(ReplicaSync.user_id, merged_replica)
        for gid in set(merged_replica.get("groups").keys()):
            BalanceHandler.recalculate_gifts(ReplicaSync.user_id, gid=gid, write_to_replica=True)
        return 0



    @staticmethod
    def _merge_expenses(own_expenses, other_expenses):
        if not own_expenses: 
            return other_expenses or {}
        if not other_expenses:
            return own_expenses or {}
        
        merged_expenses = {}
        all_eids = set(own_expenses.keys()) | set(other_expenses.keys())

        for eid in all_eids:
            exp_own = own_expenses.get(eid)
            exp_other = other_expenses.get(eid)

            if exp_own and not exp_other:
                merged_expenses[eid] = exp_own
                continue
            if not exp_own and exp_other:
                merged_expenses[eid] = exp_other
                continue
            
            own_version = exp_own.get("version", 0)
            other_version = exp_other.get("version", 0)
        
            if own_version > other_version:
                merged_expenses[eid] = exp_own
            elif own_version < other_version:
                merged_expenses[eid] = exp_other
            else:
                merged_expenses[eid] = exp_own
                merged_acknowleged_shares = {}
                postive_user_shares = [user for user in exp_own.get("shares", {}) if exp_own.get("shares")[user] > 0]
                for uid in exp_own.get("shares", {}):#postive_user_shares:
                    #merged_acknowleged_shares[uid] = (
                     #   exp_own.get("acknowledged_shares", {}).get(uid, False) or 
                      #  exp_other.get("acknowledged_shares", {}).get(uid, False)
                    #)
                    if exp_own.get("acknowledged_shares", {}).get(uid, False) or exp_other.get("acknowledged_shares", {}).get(uid, False):
                        merged_acknowleged_shares[uid] = True
                    else:
                        merged_acknowleged_shares[uid] = False
                merged_expenses[eid]["acknowledged_shares"] = merged_acknowleged_shares
        
        return merged_expenses

    @staticmethod
    def _merge_groups(own_groups, other_groups):
        if not own_groups:
            return other_groups or {}
        if not other_groups:
            return own_groups or {}
        
        merged_groups = {}
        all_gids = set(own_groups.keys()) | set(other_groups.keys())

        for gid in all_gids:
            group_own = own_groups.get(gid)
            group_other = other_groups.get(gid)

            if group_own and not group_other:
                merged_groups[gid] = group_own
                continue
            if group_other and not group_own:
                merged_groups[gid] = group_other
                continue

            own_members = group_own.get("members")
            other_members = group_other.get("members")
            merged_members = {}
            all_uids = set(own_members.keys()) | set(other_members.keys())

            for uid in all_uids:
                merged_members[uid] = max(own_members.get(uid, 0), other_members.get(uid, 0))

            own_invited_members = group_own.get("invited_members")
            other_invited_members = group_other.get("invited_members")
            merged_invited_members = {}
            all_uids = set(own_invited_members.keys()) | set(other_invited_members.keys())

            for uid in all_uids:
                merged_invited_members[uid] = max(own_invited_members.get(uid, 0), other_invited_members.get(uid, 0))

            merged_group = {
                **group_own,
                "members": merged_members,
                "invited_members": merged_invited_members
            }
            merged_groups[gid] = merged_group

        return merged_groups
    
    @staticmethod
    def _merge_known_users(own_users, other_users):
        if not own_users:
            return other_users or {}
        if not other_users:
            return own_users or {}

        merged_users = {}
        all_uids = set(own_users.keys()) | set(other_users.keys())

        for uid in all_uids:
            own_name = own_users.get(uid)
            other_name = other_users.get(uid)

            if own_name and not other_name:
                merged_users[uid] = own_name
            elif other_name and not own_name:
                merged_users[uid] = other_name
            else:
                # Conflict: choose lexicographically larger name, should not be possible to occur
                merged_users[uid] = max(own_name, other_name)

        return merged_users


    @staticmethod
    def _handle_replica_request(addr):
        ReplicaSync.safe_print(f"[ReplicaSync] Peer at {addr} requested our replica.")
        ReplicaSync.send_full_replica(addr[0], addr[1])


    @staticmethod
    def send_full_replica(target_host: str, target_port: int):
        backend = get_backend()
        if not ReplicaSync.network_handler:
            ReplicaSync.safe_print("[ReplicaSync] Listener not running — cannot send.")
            return

        replica = backend.get_full_replica(ReplicaSync.user_id)
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