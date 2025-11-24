import sys
import os
from data_handler import DataHandler
from user_manager import UserManager
from group_handler import GroupHandler, Group
from expense_handler import ExpenseHandler, Expense
from balance_handler import BalanceHandler
from replica_sync import ReplicaSync
import time


class CLIInterface:
    def __init__(self, user_id):
        self.user_id = user_id

        # Automatically start networking when CLI is created
        print("[ReplicaSync] Starting listener...")
        ReplicaSync.start_listener(self.user_id)
        addr = ReplicaSync.address()
        if addr:
            print(f"[ReplicaSync] Listening at {addr}")
        else:
            print("[ReplicaSync] Failed to start listener.")

    def _resolve_entity(self, entity_type: str, name_or_id: str):
        replica = DataHandler.get_user_replica(self.user_id)
        entities = {}

        if entity_type == "user":
            entities = replica.get("known_users", {})
        elif entity_type == "group":
            entities = replica.get("groups", {})
        elif entity_type == "expense":
            entities = replica.get("recorded_expenses", {})
        else:
            raise ValueError("Invalid entity_type")

        # exact ID match
        if name_or_id in entities:
            return name_or_id

        # name match
        matches = []
        if entity_type == "user":
            matches = [uid for uid, uname in entities.items() if uname == name_or_id]
        else:
            matches = [eid for eid, data in entities.items() if data.get("name") == name_or_id]

        if not matches:
            print(f"No {entity_type} found with name or id '{name_or_id}'.")
            return None

        if len(matches) == 1:
            return matches[0]

        # ambiguity handling
        print(f"Multiple {entity_type}s found with that name:")
        for eid in matches:
            if entity_type == "user":
                print(f"  - {entities[eid]} (id: {eid})")
            elif entity_type == "group":
                print(f"  - {entities[eid]['name']} (id: {eid})")
            elif entity_type == "expense":
                e = entities[eid]
                print(f"  - {e['name']} (id: {eid}, amount={e.get('amount', 0)})")
        chosen = input("Enter the id to use: ").strip()
        if chosen in matches:
            return chosen
        print("Invalid choice.")
        return None


    def run(self):
        print("\nType 'help' to see available commands.\n")
        try:
            while True:
                sys.stdout.write("\r\033[K") #clear current line
                sys.stdout.flush()              
                cmd_input = input("splitless> ").strip()
                if not cmd_input:
                    continue
                parts = cmd_input.split()
                cmd, args = parts[0], parts[1:]

                if cmd in ("exit", "quit"):
                    print("Exiting SplitLess CLI.")
                    break
                elif cmd == "help":
                    self.print_help()
                elif cmd == "show":
                    self.cmd_show(args)
                elif cmd == "group-create":
                    self.cmd_group_create(args)
                elif cmd == "group-add-member":
                    print("Command unavailable")
                    # self.cmd_group_add_member(args)
                elif cmd == "group-invite":
                    self.cmd_group_invite(args)
                elif cmd == "group-accept":
                    self.cmd_group_accept(args)
                elif cmd == "group-invitations":
                    self.cmd_group_invitations()
                elif cmd == "group-leave":
                    self.cmd_group_leave(args)
                elif cmd == "group-suggest-payer":
                    self.cmd_group_suggest_payer(args)
                elif cmd == "expense-create":
                    self.cmd_expense_create(args)
                elif cmd == "expense-delete":
                    self.cmd_expense_delete(args)
                elif cmd == "expense-modify":
                    self.cmd_expense_modify(args)
                elif cmd == "expense-add-to-group":
                    self.cmd_expense_add_to_group(args)
                elif cmd == "expense-remove-from-group":
                    self.cmd_expense_remove_from_group(args)
                elif cmd == "group-balance":
                    self.cmd_group_balance(args)
                elif cmd == "clear":
                    self.cmd_clear()
                elif cmd == "sync-address":
                    self.cmd_sync_address()
                elif cmd == "sync-send":
                    self.cmd_sync_send(args)
                elif cmd == "sync-request":
                    self.cmd_sync_request(args)
                else:
                    print("Unknown command. Type 'help' for available commands.")
        except KeyboardInterrupt:
            print("\nUse 'exit' or 'quit' to leave.")
        finally:
            # Automatically stop the listener when CLI exits
            ReplicaSync.stop_listener()

    def print_help(self):
        print("""
Available commands:
  show all                          - Show full replica
  show groups                       - Show all groups
  show expenses                     - Show all expenses
  show users                        - Show all known users
  group-create <name>               - Create a new group
  group-add-member <group> <user>   - Add user to group (name or id)
  group-invite <group> <user>       - Invite a user into a group
  group-accept <group>              - Accept an invitation
  group-invitations                 - List your open invitations

  group-leave <group>               - Leave a group
  group-suggest-payer <group>       - Suggest the next payer (lowest balance)
  group-balance <group> <user>      - Show your balance with a user in a group

  expense-create <name> <payer_share>:<amount> [<other_share>:<amount> ...]
                                    - Create a new expense
  expense-delete <expense>          - Delete an expense
  expense-modify <expense> <user>:<share> ...
                                    - Modify expense shares
  expense-add-to-group <expense> <group>
                                    - Add expense to a group
  expense-remove-from-group <expense>
                                    - Remove expense from its group

  --- Replica Sync Commands ---
  sync-start [port]                 - Start listening for replica sync
  sync-stop                         - Stop the replica sync listener
  sync-address                      - Show this replica's address
  sync-send <host> <port>           - Send your full replica to a peer
  sync-request <host> <port>        - Request a replica from a peer

  exit / quit                       - Exit CLI
""")

    def cmd_sync_address(self):
        addr = ReplicaSync.address()
        if addr:
            print(f"[ReplicaSync] Current address: {addr}")
        else:
            print("[ReplicaSync] Not running.")

    def cmd_sync_send(self, args):
        if len(args) != 2:
            print("Usage: sync-send <host> <port>")
            return
        ReplicaSync.send_full_replica(args[0], int(args[1]))

    def cmd_sync_request(self, args):
        if len(args) != 2:
            print("Usage: sync-request <host> <port>")
            return
        ReplicaSync.request_replica(args[0], int(args[1]))



    def cmd_show(self, args):
        replica = DataHandler.get_user_replica(self.user_id)
        if not args or args[0] == "all":
            print(replica)
        elif args[0] == "groups":
            for g in replica.get("groups", {}).values():
                print(Group.from_dict(g))
        elif args[0] == "expenses":
            for e in replica.get("recorded_expenses", {}).values():
                print(Expense.from_dict(e))
        elif args[0] == "users":
            for uid, uname in replica.get("known_users", {}).items():
                print(f"{uname} (id: {uid})")
        else:
            print("Usage: show [all|groups|expenses|users]")

    def cmd_group_create(self, args):
        if not args:
            print("Usage: group-create <name>")
            return
        name = " ".join(args)
        gid = GroupHandler.create_group(self.user_id, name)
        print(f"Created group '{name}' with id {gid}")

    def cmd_group_add_member(self, args):
        if len(args) < 2:
            print("Usage: group-add-member <group> <user>")
            return
        gid = self._resolve_entity("group", args[0])
        uid = self._resolve_entity("user", args[1])
        if gid and uid:
            GroupHandler.add_member(self.user_id, uid, gid)

    def cmd_group_invite(self, args):
        if len(args) < 2:
            print("Usage: group-invite <group> <user>")
            return
        gid = self._resolve_entity("group", args[0])
        uid = self._resolve_entity("user", args[1])
        if gid and uid:
            GroupHandler.invite_member(self.user_id, uid, gid)

    def cmd_group_accept(self, args):
        if len(args) < 1:
            print("Usage: group-accept <group>")
            return
        gid = self._resolve_entity("group", args[0])
        if gid:
            GroupHandler.accept_invitation(self.user_id, gid)

    def cmd_group_invitations(self):
        replica = DataHandler.get_user_replica(self.user_id)
        groups = replica.get("groups", {})
        print("Pending invitations:")
        for gid, g in groups.items():
            persumed = g.get("persumed_members", {})
            if persumed.get(self.user_id, 0) % 2 == 1:  # contender
                print(f"  - {g['name']} (id: {gid})")


    def cmd_group_leave(self, args):
        if len(args) < 1:
            print("Usage: group-leave <group>")
            return
        gid = self._resolve_entity("group", args[0])
        if gid:
            GroupHandler.leave_group(self.user_id, gid)

    def cmd_group_suggest_payer(self, args):
        if len(args) < 1:
            print("Usage: suggest-payer <group>")
            return

        gid = self._resolve_entity("group", args[0])
        if not gid:
            print("Group " + gid + " does not exist.")
            return

        result = GroupHandler.get_lowest_balance_in_group(self.user_id, gid)
        if not result:
            print("Could not calculate balance or group is empty.")
            return

        uid, bal = result
        replica = DataHandler.get_user_replica(self.user_id)
        name = replica.get("known_users", {}).get(uid, uid)

        print(f"Suggested next payer: {name} (id: {uid}) with current balance {bal}")



    def cmd_expense_create(self, args):
        if len(args) < 2:
            print("Usage: expense-create <name> <user>:<share> ...")
            return
        name = args[0]
        shares = {}
        for share_part in args[1:]:
            if ":" not in share_part:
                print(f"Invalid share: {share_part}")
                return
            uname, val = share_part.split(":")
            uid = self._resolve_entity("user", uname)
            if not uid:
                return
            shares[uid] = float(val)
        eid = ExpenseHandler.create_expense(self.user_id, name, shares)
        if eid != -1:
            print(f"Created expense '{name}' with id {eid}")

    def cmd_expense_delete(self, args):
        if len(args) < 1:
            print("Usage: expense-delete <expense>")
            return
        eid = self._resolve_entity("expense", args[0])
        if eid:
            ExpenseHandler.delete_expense(self.user_id, eid)

    def cmd_expense_modify(self, args):
        if len(args) < 2:
            print("Usage: expense-modify <expense> <user>:<share> ...")
            return
        eid = self._resolve_entity("expense", args[0])
        shares = {}
        for s in args[1:]:
            uname, val = s.split(":")
            uid = self._resolve_entity("user", uname)
            if not uid:
                return
            shares[uid] = float(val)
        if eid:
            ExpenseHandler.modify_expense_parameters(self.user_id, eid, shares)

    def cmd_expense_add_to_group(self, args):
        if len(args) < 2:
            print("Usage: expense-add-to-group <expense> <group>")
            return
        eid = self._resolve_entity("expense", args[0])
        gid = self._resolve_entity("group", args[1])
        if eid and gid:
            ExpenseHandler.add_expense_to_group(self.user_id, eid, gid)

    def cmd_expense_remove_from_group(self, args):
        if len(args) < 1:
            print("Usage: expense-remove-from-group <expense>")
            return
        eid = self._resolve_entity("expense", args[0])
        if eid:
            ExpenseHandler.remove_expense_from_group(self.user_id, eid)

    def cmd_group_balance(self, args):
        if len(args) < 2:
            print("Usage: balance <group> <user>")
            return
        gid = self._resolve_entity("group", args[0])
        uid = self._resolve_entity("user", args[1])
        if gid and uid:
            balance = BalanceHandler.get_balance(self.user_id, uid, gid)
            if balance == None:
                return
            print(f"Balance of user {args[1]} (id: {uid}) in group {args[0]} (id: {gid}): {balance}")

    def cmd_clear(self):
        os.system('cls' if os.name == 'nt' else 'clear')
