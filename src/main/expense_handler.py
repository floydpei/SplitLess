import uuid
from dataclasses import dataclass, field, asdict
from typing import Dict
from data_handler import DataHandler
from group_handler import GroupHandler
from balance_handler import BalanceHandler
from storage_provider import get_backend

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
    acknowledged_shares: Dict[str, float] = field(default_factory=dict)

    def __str__(self):
        shares_str = ", ".join([f"{uid}: {share:.2f}" for uid, share in self.shares.items()]) or "None"
        acknowledged_shares_str = ", ".join([f"{uid}: {share:.2f}" for uid, share in self.acknowledged_shares.items()]) or "None"
        deleted_str = "Yes" if self.deleted else "No"
        return (
            f"Expense '{self.name}' (id={self.eid})\n"
            f"  Group: {self.group}\n"
            f"  Version: {self.version}\n"
            f"  Payer: {self.payer}\n"
            f"  Amount: {self.amount:.2f}\n"
            f"  Deleted: {deleted_str}\n"
            f"  Shares: {shares_str}\n"
            f"  Acknowledged shares: {acknowledged_shares_str}"
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
        backend = get_backend()
        eid = str(uuid.uuid4())
        group = None
        version = 0
        amount = sum(shares.values())
        deleted = False
        acknowledged_shares = {user: False for user, share in shares.items()}#if share > 0.0}
        if payer not in shares: shares[payer] = 0
        if shares[payer] >= 0: acknowledged_shares[payer] = True 
        for share in shares.values():
            if share < 0:
                return (-1, "[ExpenseHandler] The shares of an expense have to be non negative.")
        if amount == 0:
            return (-1 , "[ExpenseHandler] The amount of an expense has to be greater than 0.")
        
        new_expense = Expense(eid, name, group, version, payer, amount, deleted, shares, acknowledged_shares)
        expense_as_dict = asdict(new_expense)
        #print(expense_as_dict)
        backend.write_expense(payer, expense_as_dict)
        return (eid, "[ExpenseHandler] Succesfully created new expense with id " + eid)

    @staticmethod
    def delete_expense(actor: str, eid: str):
        backend = get_backend()
        expense = backend.get_expense(actor, eid)
        if not expense:
            return (-1, "[ExpenseHandler] The expense with id " + eid + " does not exist on user " + actor + " replica.")
        if not actor == expense["payer"]:
            return (-1, "[ExpenseHandler] The user with id " + actor + " did not pay for the expense and cannot delete it.")
        if expense["deleted"]:
            return (-1, "[ExpenseHandler] The expense with id " + eid + " is already deleted.")
        
        gid = expense.get("group")
        if gid:
            group = group = backend.get_group(actor, gid)
            if not GroupHandler.is_member(actor, group):
                return (-1, "[ExpenseHandler] User " + actor + " is not member of the group " + gid + " and cannot delete the expense " + eid)
        
        expense["deleted"] = True
        expense["version"] += 1
        backend.write_expense(actor, expense)
        if not expense.get("group") == None:
            BalanceHandler.recalculate_gifts(actor, expense.get("group"), write_to_replica=True)
        return (1, "[ExpenseHandler] Succesfully deleted expense " + eid)

    @staticmethod
    def add_expense_to_group(actor: str, eid: str, gid: str):
        backend = get_backend()
        expense = backend.get_expense(actor, eid)
        group = backend.get_group(actor, gid)

        if not group:
            return (-1, "[ExpenseHandler] The group with id " + gid + " does not exist on user " + actor + " replica.")
        if not expense:
            return (-1, "[ExpenseHandler] The expense with id " + eid + " does not exist on user " + actor + " replica.")
        if not GroupHandler.is_member(actor, group):
            return (-1, "[ExpenseHandler] The user " + actor + " is not a member of the group " + gid + "and cannot add it to this group.")
        if not actor == expense["payer"]:
            return (-1, "[ExpenseHandler] The user with id " + actor + " did not pay for the expense and cannot add it to a group.")
        if not expense["group"] == None:
            return (-1, "[ExpenseHandler] The expense with id " + eid + " is already in a group.")
        
        shares = expense["shares"]
        for user in shares.keys():
            if not GroupHandler.is_member(user, group):
                return (-1, "[ExpenseHandler] User with id " + user + " has shares in expense " + eid + " and is not in group " + gid + ", so the expense cannot be added to this goup.")
        
        expense["group"] = gid
        expense["version"] += 1
        backend.write_expense(actor, expense)
        return (1, "[ExpenseHandler] Succesfully added expense " + eid + " to group " + gid)

    @staticmethod
    def remove_expense_from_group(actor: str, eid: str):
        backend = get_backend()
        expense = backend.get_expense(actor, eid)
        if not expense:
            return (-1, "[ExpenseHandler] The expense with id " + eid + " does not exist on user " + actor + " replica.")
        gid = expense.get("group")
        if not gid:
            return (-1, "[ExpenseHandler] The expense with id " + eid + " is in no group on users " + actor + " replica.")
        
        group = backend.get_group(actor, gid)

        if not actor == expense["payer"]:
            return (-1, "[ExpenseHandler] The user with id " + actor + " did not pay for the expense and cannot add it to a group.")
        if not GroupHandler.is_member(actor, group):
            return (-1, "[ExpenseHandler] User " + actor + " is not member of the group " + gid)
        
        expense["group"] = None
        expense["version"] += 1
        expense["acknowledged_shares"] = {user : False for user in expense.get("shares")}# if expense.get("shares")[user] > 0.0}
        backend.write_expense(actor, expense)
        BalanceHandler.recalculate_gifts(actor, gid, write_to_replica=True)
        return (1, "[ExpenseHandler] Succesfully removed expense " + eid + " from group " + gid)

    @staticmethod
    def modify_expense_parameters(actor: str, eid: str, shares):
        backend = get_backend()
        expense = backend.get_expense(actor, eid)
        if not expense:
            return (-1, "[ExpenseHandler] The expense with id " + eid + " does not exist on user " + actor + " replica.")
        if not actor == expense["payer"]:
            return (-1, "[ExpenseHandler] The user with id " + actor + " did not pay for the expense and cannot modify it.")
        if expense["deleted"]:
            return (-1, "[ExpenseHandler] The expense " + eid + " is deleted and can no longer be modified.")
        for share in shares.values():
            if share < 0:
                return (-1, "[ExpenseHandler] The shares of an expense have to be non negative.")
        amount = sum(shares.values())
        if amount == 0:
            return (-1, "[ExpenseHandler] The amount of an expense has to be greater than 0.")
        
        gid = expense.get("group")
        if gid:
            group = group = backend.get_group(actor, gid)
            if not GroupHandler.is_member(actor, group):
                return (-1, "[ExpenseHandler] User " + actor + " is not member of the group " + gid)
            for user in shares.keys():
                if not GroupHandler.is_member(user, group):
                    return (-1, "[ExpenseHandler] User with id " + user + " has shares in expense " + eid + " and is not in group " + gid + ", so the expense cannot be modified.")
        expense["shares"] = shares
        expense["amount"] = amount
        expense["version"] += 1
        expense["acknowledged_shares"] = {user : False for user in shares}# if shares[user] > 0.0}
        expense["acknowledged_shares"][actor] = True
        backend.write_expense(actor, expense)
        if gid:
            BalanceHandler.recalculate_gifts(actor, gid, write_to_replica=True)
        return (1, "[ExpenseHandler] Succesfully modified expense " + eid)
    
    @staticmethod
    def acknowledge_share(actor: str, eid: str,):
        backend = get_backend()
        expense = backend.get_expense(actor, eid)
        if not expense:
            return (-1, "[ExpenseHandler] The expense with id " + eid + " does not exist on user " + actor + " replica.")
        if expense["deleted"]:
            return (-1, "[ExpenseHandler] The expense " + eid + " is deleted and you can no longer acknowledge you shares.")
        gid = expense.get("group")
        if not gid:
            return (-1, "[ExpenseHandler] The expense with id " + eid + " is not in a group and therefore the user " + actor + " cannot acknowledge their shares")
        group = backend.get_group(actor, gid)
        if not GroupHandler.is_member(actor, group):
            return (-1, "[ExpenseHandler] User " + actor + " is not member of the group " + gid)
        if expense["acknowledged_shares"].get(actor, False):
            return (-1, "[ExpenseHandler] User " + actor + " already acknowledged their share.")
        if not expense["shares"].get(actor, 0) > 0:
            return (-1, "[ExpenseHandler] User " + actor + " does not have any positive shares in the expense " + eid)

        expense["acknowledged_shares"][actor] = True
        #expense["version"] += 1
        backend.write_expense(actor, expense)
        BalanceHandler.recalculate_gifts(actor, gid, write_to_replica=True)
        return (1, "[ExpenseHandler] Succesfully acknowledged share of user " + actor)
    
    @staticmethod
    def payer_absorbs_left_member_share(actor: str, eid: str, left_member: str):
        backend = get_backend()
        expense = backend.get_expense(actor, eid)
        
        if not expense:
            return (-1, "[ExpenseHandler] The expense with id " + eid + " does not exist on user " + actor + " replica.")
        if expense["deleted"]:
            return (-1, "[ExpenseHandler] The expense " + eid + " is deleted.")
        if not actor == expense["payer"]:
            return (-1, "[ExpenseHandler] User " + actor + " is not the payer of expense " + eid + ".")
        if actor == left_member:
            return (-1, "[ExpenseHandler] Payer cannot absorb their own share.")
        
        gid = expense.get("group")
        if not gid:
            return (-1, "[ExpenseHandler] The expense " + eid + " is not in a group.")
        
        group = backend.get_group(actor, gid)
        if not group:
            return (-1, "[ExpenseHandler] Group " + gid + " does not exist on user " + actor + " replica.")
        if not GroupHandler.is_member(actor, group):
            return (-1, "[ExpenseHandler] User " + actor + " is not a member of group " + gid + ".")
        
        if GroupHandler.is_member(left_member, group):
            return (-1, "[ExpenseHandler] User " + left_member + " is still a member of group " + gid + ". They should acknowledge themselves.")
        if not GroupHandler.was_ever_member(left_member, group):
            return (-1, "[ExpenseHandler] User " + left_member + " was never a member of group " + gid + ".")
        
        left_share = expense.get("shares", {}).get(left_member, 0)
        if left_share == 0:
            return (-1, "[ExpenseHandler] User " + left_member + " has no positive share in expense " + eid + ".")
        if expense.get("acknowledged_shares", {}).get(left_member, False):
            return (-1, "[ExpenseHandler] User " + left_member + " already acknowledged their share.")
        
        shares = expense["shares"].copy()
        shares[actor] = shares.get(actor, 0) + left_share
        shares[left_member] = 0

        #expense["shares"][actor] += left_share
        #expense["shares"][left_member] = 0
        
        expense["shares"] = shares
        expense["version"] += 1
        
        backend.write_expense(actor, expense)
        BalanceHandler.recalculate_gifts(actor, gid, write_to_replica=True)
        return (1, "[ExpenseHandler] Successfully absorbed " + f"{left_share:.2f}" + " from " + left_member + " into payer's share for expense " + eid + ".")
        