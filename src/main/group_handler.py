import uuid
from dataclasses import dataclass, field, asdict
from typing import Dict
from data_handler import DataHandler
from balance_handler import BalanceHandler

@dataclass
class Group:
    gid: str
    name: str
    gifts_received: int
    members: Dict[str, int] = field(default_factory=dict) # cls
    gifts_sent: Dict[str, float] = field(default_factory=dict)

    def __str__(self):
        members_str = ", ".join([f"{uid}:{cls}" for uid, cls in self.members.items()]) or "None"
        gifts_sent_str = ", ".join([f"{uid}:{amt:.2f}" for uid, amt in self.gifts_sent.items()]) or "None"
        return (
            f"Group '{self.name}' (id={self.gid})\n"
            f"  Gifts received: {self.gifts_received}\n"
            f"  Members (cls): {members_str}\n"
            f"  Gifts sent: {gifts_sent_str}"
        )
    
    @classmethod
    def from_dict(cls, data: dict):
        return cls(**data)

class GroupHandler:

    @staticmethod
    def is_member(actor, group):
        if actor not in group["members"]: return False
        return group["members"][actor] % 2 == 1
    
    @staticmethod
    def was_ever_member(actor, group):
        if actor not in group["members"]: return False
        return group["members"][actor] > 0
    
    @staticmethod
    def get_members(actor: str, group: Group): 
        members = []
        for user in group.get("members"):
            if GroupHandler.is_member(user, group): members.append(user)
        return members
    
    @staticmethod
    def get_amount_members(actor: str, group: Group):
        return GroupHandler.get_members(actor, group).length
    
    @staticmethod
    def get_balances_in_group(actor: str, gid: str):
        replica = DataHandler.get_user_replica(actor)
        if not replica:
            print("User " + actor + " replica does not exist on local storage.")
            return
        group = replica.get("groups").get(gid)
        if not group: 
            print("Group " + gid + " does not exist on users " + actor + " replica.")
            return
        
        group_members = GroupHandler.get_members(actor, group)
        balances = {}
        for member in group_members:
            balances[member] = BalanceHandler.get_balance(actor, member, gid)

        return balances

    @staticmethod
    def get_lowest_balance_in_group(actor: str, gid: str):
        balances = GroupHandler.get_balances_in_group(actor, gid)
        if not balances:
            return -1
        min_item = min(balances.items(), key=lambda item: item[1])
        return min_item
        

    
    @staticmethod
    def create_group(creator: str, name : str):
        gid = str(uuid.uuid4())[:8]
        members = {creator: 1}
        gifts_received = 0

        new_group = Group(gid=gid, name=name, members=members, gifts_received=gifts_received)
        group_as_dict = asdict(new_group)
        #print(group_as_dict)
        DataHandler.write_group(creator, group_as_dict)
        return gid

    @staticmethod
    def add_member(actor: str, new_member: str, gid: str):
        group = DataHandler.get_group(actor, gid)
        if not group:
            print("Group with " + gid + " does not exist on users " + actor + " replica")
            return
        if not GroupHandler.is_member(actor, group):
            print("User with id " + actor + " is not in the group with id " + gid + ", and cannot add a user to it.")
            return
        known_users = DataHandler.get_known_users(actor).keys()
        if not new_member in known_users: 
            print("The user with id " + new_member + " is not known, so it cannot be added to the group.")
            return
        if GroupHandler.is_member(new_member, group):
            print("User with id " + new_member + " is already in the group")
            return

        
        group.get("members")[new_member] = group["members"].get(new_member, 0) + 1
        DataHandler.write_group(actor, group)
        print("Added user " + new_member + " to the group " + gid + ".")

    @staticmethod
    def leave_group(actor: str, gid: str):
        group = DataHandler.get_group(actor, gid)
        if not group:
            print("Group with " + gid + " does not exist on users " + actor + " replica")
            return
        
        if not GroupHandler.is_member(actor, group):
            print("User with id " + actor + " is not a member of group " + gid)
            return
        
        user_balance = BalanceHandler.get_balance(actor, actor, gid)
        if user_balance < 0:
            print("User " + actor + " has a negative balance of " + user_balance + " and can not leave the group.")
        
        group["members"][actor] += 1
        DataHandler.write_group(actor, group)
        updated_group = BalanceHandler.recalculate_gifts(actor, gid, write_to_replica=False)
        DataHandler.write_group(actor, updated_group)


