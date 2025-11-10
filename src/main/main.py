import os
from data_handler import DataHandler
from user_manager import UserManager
from expense_handler import Expense, ExpenseHandler
from group_handler import GroupHandler, Group
from balance_handler import BalanceHandler
from cli_interface import CLIInterface

def handle_startup():
    print("Welcome to SplitLess CLI")

    while True:
        print("\nOptions: \n1. Login\n2. Register\n3. Exit")
        choice = input("Choose an option: ").strip()
        if choice == "1":
            result = UserManager.login_user()
            if result:
                username, user_id = result
                break
        elif choice == "2":
            result = UserManager.create_user()
            if result:
                username, user_id = result
                break
        elif choice == "3":
            print("Exiting...")
            return
        else:
            print("Invalid option. Try again.")
    
    replica_data = DataHandler.get_user_replica(user_id)

    if not replica_data:
        replica_data = {
            "recorded_expenses": {},
            "groups": {}
        }
        DataHandler.write_user_replica(replica_data)

    print(f"Replica loaded for {username}. You can now start using the app.")
    return user_id


if __name__ == "__main__":
    user_id = handle_startup()
    print(user_id)
    if user_id:
        CLIInterface(user_id).run()
