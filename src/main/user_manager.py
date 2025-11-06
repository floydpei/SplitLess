from data_handler import DataHandler
import os
import uuid
import getpass

USERS_FILE = os.path.abspath(os.path.join(os.path.dirname(__file__), "../data/local_users.json"))

class UserManager:
    """
    Handles user creation and login
    """

    @staticmethod
    def name_exists_locally(new_name, local_users):
        return any(
            user_details.get('name') == new_name
            for user_details in local_users.values()
        )

    @staticmethod
    def get_id_from_name(username, local_users):
        for user_id, user_details in local_users.items():
            if user_details.get('name') == username:
                return user_id 
        return None

    @classmethod
    def create_user(cls):
        local_users = DataHandler.get_local_users()

        while True:
            username = input("Enter a new username: ").strip()
            if not username:
                print("Username cannot be empty.")
                continue
            if UserManager.name_exists_locally(username, local_users):
                print("Username already exists on this instance, choose another.")
                continue
            break

        while True:
            password = getpass.getpass("Enter a password: ")
            password_confirm = getpass.getpass("Confirm password: ")
            if password == password_confirm:
                break
            else:
                print("Passwords do not match. Try again.")

        user_id = str(uuid.uuid4())[:8]
        local_users[user_id] = {
            "name": username,
            "password_hash": DataHandler.hash_password(password)
        }

        DataHandler.write_local_users(local_users)
        print(f"User '{username}' created successfully with id {user_id}.")

        # Initialize empty replica for the user
        DataHandler.write_user_replica(user_id, {
            "recorded_expenses": {},
            "groups": {},
            "known_users": [user_id]
        })

        return username, user_id
    
    @classmethod
    def login_user(cls):
        local_users = DataHandler.get_local_users()

        username = input("Enter your username: ").strip()
        if not UserManager.name_exists_locally(username, local_users):
            print("Username not found.")
            return None
        
        user_id = UserManager.get_id_from_name(username, local_users)

        password = getpass.getpass("Enter your password: ")
        hashed = DataHandler.hash_password(password)
        if hashed != local_users[user_id]["password_hash"]:
            print("Incorrect password.")
            return None

        print(f"Logged in as {username} (id: {user_id})")

        return username, user_id