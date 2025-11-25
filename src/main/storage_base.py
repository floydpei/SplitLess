from abc import ABC, abstractmethod

class ReplicaStorageBackend(ABC):

    @abstractmethod
    def get_full_replica(self, user_id: str) -> dict:
        pass

    @abstractmethod
    def write_full_replica(self, user_id: str, replica: dict) -> None:
        pass

    @abstractmethod
    def get_expenses(self, user_id: str) -> dict:
        pass

    @abstractmethod
    def write_expenses(self, user_id: str, expenses: dict) -> None:
        pass

    @abstractmethod
    def get_groups(self, user_id: str) -> dict:
        pass

    @abstractmethod
    def write_groups(self, user_id: str, groups: dict) -> None:
        pass

    @abstractmethod
    def get_expense(self, user_id: str, eid: str) -> dict:
        pass

    @abstractmethod
    def write_expense(self, user_id: str, expense: dict) -> None:
        pass

    @abstractmethod
    def get_group(self, user_id: str, gid: str) -> dict:
        pass

    @abstractmethod
    def write_group(self, user_id: str, group: dict) -> None:
        pass
