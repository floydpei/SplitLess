import os
from data_handler import DataHandler
from user_manager import UserManager
from expense_handler import Expense, ExpenseHandler
from group_handler import GroupHandler, Group
from balance_handler import BalanceHandler

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
    gid = "4c902135"
    shares = {user_id: 20, "e42c27ce": 5}
    #eid = ExpenseHandler.create_expense(user_id, "e1", shares)
    #GroupHandler.add_member(user_id, "e42c27ce", gid)
    #ExpenseHandler.add_expense_to_group(user_id, eid, gid)

    group_dict = DataHandler.get_group(user_id, gid)
    group = Group.from_dict(group_dict)
    #print(group_dict)
    #print(group)

    GroupHandler.leave_group(user_id, gid)
    group_dict = DataHandler.get_group(user_id, gid)
    group = Group.from_dict(group_dict)
    #print(group_dict)
    print(group)

    expense_dict = DataHandler.get_expense(user_id, "6485e6f0")
    expense = Expense.from_dict(expense_dict)

    #print(expense_dict)
    print(expense)

    ExpenseHandler.remove_expense_from_group(user_id, "6485e6f0")

    group_dict = DataHandler.get_group(user_id, gid)
    group = Group.from_dict(group_dict)
    #print(group_dict)
    print(group)
    expense_dict = DataHandler.get_expense(user_id, "6485e6f0")
    expense = Expense.from_dict(expense_dict)
    #print(expense_dict)
    print(expense)
