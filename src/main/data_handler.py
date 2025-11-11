import os
import json
import hashlib

BASE_DIR = os.path.dirname(os.path.abspath(__file__))          # src/main/
DATA_DIR = os.path.abspath(os.path.join(BASE_DIR, "../data"))  # src/data/

# Ensure base folder exists
os.makedirs(DATA_DIR, exist_ok=True)

class DataHandler:
    """
    Handles reading and writing user and replica data to disk.
    """

    @staticmethod
    def read_json(path):
        if not os.path.exists(path):
            return {}
        with open(path, "r") as f:
            try:
                return json.load(f)
            except json.JSONDecodeError:
                return {}

    @staticmethod
    def write_json(path, data):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            json.dump(data, f, indent=2)

    @staticmethod
    def get_user_replica(user_id):
        path = os.path.join(DATA_DIR, "replicas", f"{user_id}", "replica.json")
        return DataHandler.read_json(path)
    
    @staticmethod
    def write_user_replica(user_id, replica):
        path = os.path.join(DATA_DIR, "replicas", f"{user_id}", "replica.json")
        DataHandler.write_json(path, replica)

    @staticmethod
    def get_local_users():
        path = os.path.join(DATA_DIR, "local_users.json")
        return DataHandler.read_json(path)
    
    @staticmethod
    def write_local_users(local_users):
        path = os.path.join(DATA_DIR, "local_users.json")
        DataHandler.write_json(path, local_users)
    
    @staticmethod
    def write_expense(user_id, expense):
        user_replica = DataHandler.get_user_replica(user_id)
        eid = expense["eid"]
        user_replica["recorded_expenses"][eid] = expense
        DataHandler.write_user_replica(user_id, user_replica)

    @staticmethod
    def get_expense(user_id, eid):
        user_replica = DataHandler.get_user_replica(user_id)
        expense = user_replica["recorded_expenses"][eid]
        return expense

    @staticmethod
    def write_group(user_id, new_group):
        user_replica = DataHandler.get_user_replica(user_id)
        gid = new_group["gid"]
        user_replica["groups"][gid] = new_group
        DataHandler.write_user_replica(user_id, user_replica)

    @staticmethod
    def get_group(user_id, gid):
        user_replica = DataHandler.get_user_replica(user_id)
        group = user_replica["groups"][gid]
        return group
    
    @staticmethod
    def get_known_users(user_id) -> list[str]:
        user_replica = DataHandler.get_user_replica(user_id)
        known_users = user_replica.get("known_users", {})
        return known_users
    
    @staticmethod
    def write_known_users(user_id, known_id, known_name):
        user_replica = DataHandler.get_user_replica(user_id)
        known = user_replica.get("known_users", {})
        known[known_id] = known_name
        user_replica["known_users"] = known
        DataHandler.write_user_replica(user_id, user_replica)

    @staticmethod
    def get_user_password_hash(user_id):
        user_data = DataHandler.get_local_users

        # user could be created and working on a different machiene
        if not user_data[user_id]:
            print("[DataHandler] User with id " + user_id + " does not exist or resides at a different location")
            return

        return user_data[user_id]["password_hash"] 
    
    @staticmethod
    def hash_password(password):
        """Hashes a password for simple storage."""
        return hashlib.sha256(password.encode()).hexdigest()