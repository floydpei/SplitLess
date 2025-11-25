import copy
from storage_base import ReplicaStorageBackend


class MemoryReplicaBackend(ReplicaStorageBackend):

    def __init__(self):
        self._replicas = {}  # user_id -> replica_dict

    def _ensure_replica(self, user_id):
        if user_id not in self._replicas:
            self._replicas[user_id] = {
                "recorded_expenses": {},
                "groups": {},
                "known_users": {}
            }


    def get_full_replica(self, user_id: str) -> dict:
        self._ensure_replica(user_id)
        return copy.deepcopy(self._replicas[user_id])

    def write_full_replica(self, user_id: str, replica: dict) -> None:
        self._ensure_replica(user_id)
        self._replicas[user_id] = replica


    def get_expenses(self, user_id: str) -> dict:
        self._ensure_replica(user_id)
        return copy.deepcopy(self._replicas[user_id]["recorded_expenses"])

    def write_expenses(self, user_id: str, expenses: dict) -> None:
        self._ensure_replica(user_id)
        self._replicas[user_id]["recorded_expenses"] = expenses


    def get_groups(self, user_id: str) -> dict:
        self._ensure_replica(user_id)
        return copy.deepcopy(self._replicas[user_id]["groups"])

    def write_groups(self, user_id: str, groups: dict) -> None:
        self._ensure_replica(user_id)
        self._replicas[user_id]["groups"] = groups


    def get_expense(self, user_id: str, eid: str) -> dict:
        self._ensure_replica(user_id)
        return copy.deepcopy(self._replicas[user_id]["recorded_expenses"].get(eid, {}))

    def write_expense(self, user_id: str, expense: dict) -> None:
        self._ensure_replica(user_id)
        self._replicas[user_id]["recorded_expenses"][expense["eid"]] = expense


    def get_group(self, user_id: str, gid: str) -> dict:
        self._ensure_replica(user_id)
        return copy.deepcopy(self._replicas[user_id]["groups"].get(gid, {}))

    def write_group(self, user_id: str, group: dict) -> None:
        self._ensure_replica(user_id)
        self._replicas[user_id]["groups"][group["gid"]] = group
