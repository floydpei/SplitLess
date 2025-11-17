import uuid
from dataclasses import dataclass, field, asdict
from typing import Dict
from data_handler import DataHandler
from group_handler import GroupHandler
from balance_handler import BalanceHandler

@dataclass
class Expense:
    eid: str
    name: str
    group: str
    version : int
    payer: str
    amount: float
    deleted: bool
    shares: Dict[str, float] = field(default_factory=dict)

    def __str__(self):
        shares_str = ", ".join([f"{uid}: {share:.2f}" for uid, share in self.shares.items()]) or "None"
        deleted_str = "Yes" if self.deleted else "No"
        return (
            f"Expense '{self.name}' (id={self.eid})\n"
            f"  Group: {self.group}\n"
            f"  Version: {self.version}\n"
            f"  Payer: {self.payer}\n"
            f"  Amount: {self.amount:.2f}\n"
            f"  Deleted: {deleted_str}\n"
            f"  Shares: {shares_str}"
        )

    @classmethod
    def from_dict(cls, data: dict):
        return cls(**data)

class ExpenseHandler:
    """
    Handles Expense creation, and modification.
    """

    @staticmethod
    def create_expense(payer: str, name: str, shares: Dict[str, float]):
        eid = str(uuid.uuid4())[:8]
        group = None
        version = 0
        amount = sum(shares.values())
        deleted = False

        for share in shares.values():
            if share < 0:
                print("[ExpenseHandler] The shares of an expense have to be non negative.")
                return -1
        if amount == 0:
            print("[ExpenseHandler] The amount of an expense has to be greater than 0.")
            return -1
        
        new_expense = Expense(eid, name, group, version, payer, amount, deleted, shares)
        expense_as_dict = asdict(new_expense)
        #print(expense_as_dict)
        DataHandler.write_expense(payer, expense_as_dict)
        print("[ExpenseHandler] Succesfully created new expense with id " + eid)
        return eid

    @staticmethod
    def delete_expense(actor: str, eid: str):
        expense = DataHandler.get_expense(actor, eid)
        if not expense:
            print("[ExpenseHandler] The expense with id " + eid + " does not exist on user " + actor + " replica.")
            return -1
        if not actor == expense["payer"]:
            print("[ExpenseHandler] The user with id " + actor + " did not pay for the expense and cannot delete it.")
            return -1
        if expense["deleted"]:
            print("[ExpenseHandler] The expense with id " + eid + " is already deleted.")
            return -1
        
        gid = expense.get("group")
        if gid:
            group = group = DataHandler.get_group(actor, gid)
            if not GroupHandler.is_member(actor, group):
                print("[ExpenseHandler] User " + actor + " is not member of the group " + gid + " and cannot delete the expense " + eid)
                return -1
        
        expense["deleted"] = True
        expense["version"] += 1
        DataHandler.write_expense(actor, expense)
        if not expense.get("group") == None:
            BalanceHandler.recalculate_gifts(actor, expense.get("group"), write_to_replica=True)
        print("[ExpenseHandler] Succesfully deleted expense " + eid)
        return 1

    @staticmethod
    def add_expense_to_group(actor: str, eid: str, gid: str):
        expense = DataHandler.get_expense(actor, eid)
        group = DataHandler.get_group(actor, gid)

        if not group:
            print("[ExpenseHandler] The group with id " + gid + " does not exist on user " + actor + " replica.")
            return -1
        if not expense:
            print("[ExpenseHandler] The expense with id " + eid + " does not exist on user " + actor + " replica.")
            return -1
        if not GroupHandler.is_member(actor, group):
            print("[ExpenseHandler] The user " + actor + " is not a member of the group " + group + "and cannot add it to this group.")   
            return -1
        if not actor == expense["payer"]:
            print("[ExpenseHandler] The user with id " + actor + " did not pay for the expense and cannot add it to a group.")
            return -1
        if not expense["group"] == None:
            print("[ExpenseHandler] The expense with id " + eid + " is already in a group.")
            return -1
        
        shares = expense["shares"]
        for user in shares.keys():
            if not GroupHandler.is_member(user, group):
                print("[ExpenseHandler] User with id " + user + " has shares in expense " + eid + " and is not in group " + gid + ", so the expense cannot be added to this goup.")
        
        expense["group"] = gid
        expense["version"] += 1
        DataHandler.write_expense(actor, expense)
        print("[ExpenseHandler] Succesfully added expense " + eid + " to group " + gid)
        return 1

    @staticmethod
    def remove_expense_from_group(actor: str, eid: str):
        expense = DataHandler.get_expense(actor, eid)
        if not expense:
            print("[ExpenseHandler] The expense with id " + eid + " does not exist on user " + actor + " replica.")
            return -1
        gid = expense.get("group")
        if not gid:
            print("[ExpenseHandler] The expense with id " + eid + " is in no group on users " + actor + " replica.")
            return -1
        
        group = DataHandler.get_group(actor, gid)

        if not actor == expense["payer"]:
            print("[ExpenseHandler] The user with id " + actor + " did not pay for the expense and cannot add it to a group.")
            return -1
        if not GroupHandler.is_member(actor, group):
            print("[ExpenseHandler] User " + actor + " is not member of the group " + gid)
            return -1
        
        expense["group"] = None
        expense["version"] += 1
        DataHandler.write_expense(actor, expense)
        BalanceHandler.recalculate_gifts(actor, gid, write_to_replica=True)
        print("[ExpenseHandler] Succesfully removed expense " + eid + " from group " + gid)
        return 1

    @staticmethod
    def modify_expense_parameters(actor: str, eid: str, shares):
        expense = DataHandler.get_expense(actor, eid)
        if not expense:
            print("[ExpenseHandler] The expense with id " + eid + " does not exist on user " + actor + " replica.")
            return -1
        if not actor == expense["payer"]:
            print("[ExpenseHandler] The user with id " + actor + " did not pay for the expense and cannot modify it.")
            return -1
        if expense["deleted"]:
            print("[ExpenseHandler] The expense " + eid + " is deleted and can no longer be modified.")
        
        for share in shares.values():
            if share < 0:
                print("[ExpenseHandler] The shares of an expense have to be non negative.")
                return -1
        amount = sum(shares.values())
        if amount == 0:
            print("[ExpenseHandler] The amount of an expense has to be greater than 0.")
            return -1
        
        gid = expense.get("group")
        if gid:
            group = group = DataHandler.get_group(actor, gid)
            if not GroupHandler.is_member(actor, group):
                print("[ExpenseHandler] User " + actor + " is not member of the group " + gid)
                return -1
            for user in shares.keys():
                if not GroupHandler.is_member(user, group):
                    print("[ExpenseHandler] User with id " + user + " has shares in expense " + eid + " and is not in group " + gid + ", so the expense cannot be modified.")
                    return -1
        expense["shares"] = shares
        expense["amount"] = amount
        expense["version"] += 1
        DataHandler.write_expense(actor, expense)
        if gid:
            BalanceHandler.recalculate_gifts(actor, gid, write_to_replica=True)
        print("[ExpenseHandler] Succesfully modified expense " + eid)
        return 1
        