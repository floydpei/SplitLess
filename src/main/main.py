import os
from data_handler import DataHandler
from user_manager import UserManager
from expense_handler import Expense, ExpenseHandler
from group_handler import GroupHandler, Group
from balance_handler import BalanceHandler
from cli_interface import CLIInterface
from storage_provider import get_backend

def handle_startup():
    backend = get_backend()
    os.system('cls' if os.name == 'nt' else 'clear')
    print("Welcome to SplitLess CLI")
    user_id = ""

    while True:
        print("\nOptions: \n1. Login\n2. Register\n3. Exit")
        choice = input("Choose an option: ").strip()
        if choice == "1" or choice == "login" or choice == "Login":
            result = UserManager.login_user()
            if result:
                username, user_id = result
                break
        elif choice == "2" or choice == "register" or choice == "Register":
            result = UserManager.create_user()
            if result:
                username, user_id = result
                break
        elif choice == "3" or choice == "exit" or choice == "quit":
            print("Exiting...")
            return
        else:
            print("Invalid option. Try again.")
    
    replica_data = backend.get_full_replica(user_id)

    if not replica_data:
        replica_data = {
            "recorded_expenses": {},
            "groups": {},
            "known_users" : {user_id: username}
        }
        backend.write_full_replica(user_id, replica_data)

    print(f"Replica loaded for {username}. You can now start using the app.")
    return user_id


if __name__ == "__main__":
    user_id = handle_startup()
    if user_id:
        CLIInterface(user_id).run()
