import os
import json
import copy
import hashlib

from storage_base import ReplicaStorageBackend

BASE_DIR = os.path.dirname(os.path.abspath(__file__))          # src/main/
DATA_DIR = os.path.abspath(os.path.join(BASE_DIR, "../data"))

os.makedirs(DATA_DIR, exist_ok=True)


class DiskReplicaBackend(ReplicaStorageBackend):

    def _read_json(self, path):
        if not os.path.exists(path):
            return {}
        try:
            with open(path, "r") as f:
                return json.load(f)
        except json.JSONDecodeError:
            return {}

    def _write_json(self, path, data):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            json.dump(data, f, indent=2)

    def _replica_path(self, user_id):
        return os.path.join(DATA_DIR, "replicas", user_id, "replica.json")


    def get_full_replica(self, user_id: str) -> dict:
        data = self._read_json(self._replica_path(user_id))
        return copy.deepcopy(data)

    def write_full_replica(self, user_id: str, replica: dict) -> None:
        self._write_json(self._replica_path(user_id), replica)


    def get_expenses(self, user_id: str) -> dict:
        rep = self._read_json(self._replica_path(user_id))
        return copy.deepcopy(rep.get("recorded_expenses", {}))

    def write_expenses(self, user_id: str, expenses: dict) -> None:
        rep = self._read_json(self._replica_path(user_id))
        rep["recorded_expenses"] = expenses
        self._write_json(self._replica_path(user_id), rep)


    def get_groups(self, user_id: str) -> dict:
        rep = self._read_json(self._replica_path(user_id))
        return copy.deepcopy(rep.get("groups", {}))

    def write_groups(self, user_id: str, groups: dict) -> None:
        rep = self._read_json(self._replica_path(user_id))
        rep["groups"] = groups
        self._write_json(self._replica_path(user_id), rep)


    def get_expense(self, user_id: str, eid: str) -> dict:
        rep = self._read_json(self._replica_path(user_id))
        return copy.deepcopy(rep.get("recorded_expenses", {}).get(eid, {}))

    def write_expense(self, user_id: str, expense: dict) -> None:
        rep = self._read_json(self._replica_path(user_id))
        rep.setdefault("recorded_expenses", {})
        rep["recorded_expenses"][expense["eid"]] = expense
        self._write_json(self._replica_path(user_id), rep)


    def get_group(self, user_id: str, gid: str) -> dict:
        rep = self._read_json(self._replica_path(user_id))
        return copy.deepcopy(rep.get("groups", {}).get(gid, {}))

    def write_group(self, user_id: str, group: dict) -> None:
        rep = self._read_json(self._replica_path(user_id))
        rep.setdefault("groups", {})
        rep["groups"][group["gid"]] = group
        self._write_json(self._replica_path(user_id), rep)

    def get_known_users(self, user_id) -> dict:
        user_replica = self.get_full_replica(user_id)
        return copy.deepcopy(user_replica.get("known_users", {}))

    def write_known_users(self, user_id, known_id, known_name):
        user_replica = self.get_full_replica(user_id)
        known = user_replica.get("known_users", {})
        known[known_id] = known_name
        user_replica["known_users"] = known
        self.write_full_replica(user_id, user_replica)

    def get_local_users(self):
        """Return all locally stored users"""
        path = os.path.join(DATA_DIR, "local_users.json")
        return self._read_json(path)

    def write_local_users(self, local_users):
        """Write all local users to disk"""
        path = os.path.join(DATA_DIR, "local_users.json")
        self._write_json(path, local_users)

    def get_user_password_hash(self, user_id):
        users = self.get_local_users()
        if user_id not in users:
            print(f"[DiskBackend] User {user_id} not found")
            return None
        return users[user_id]["password_hash"]

    @staticmethod
    def hash_password(password):
        return hashlib.sha256(password.encode()).hexdigest()
