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
    def is_member(user_id, group):
        if user_id not in group["members"]: return False
        return group["members"][user_id] % 2 == 1
    
    @staticmethod
    def was_ever_member(user_id, group):
        if user_id not in group["members"]: return False
        return group["members"][user_id] > 0
    
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
        known_users = DataHandler.get_known_users(actor)
        if not new_member in known_users: 
            print("The user with id " + new_member + " is not known, so it cannot be added to the group.")
            return
        if GroupHandler.is_member(new_member, group):
            print("User with id " + new_member + " is already in the group")
            return


        if not GroupHandler.is_member(actor, group):
            print("User with id " + new_member + " is not known by adding user")
            return
        
        group["members"][new_member] = group["members"].get(new_member, 0) + 1
        DataHandler.write_group(actor, group)

    @staticmethod
    def leave_group(actor: str, gid: str):
        group = DataHandler.get_group(actor, gid)
        if not group:
            print("Group with " + gid + " does not exist on users " + actor + " replica")
            return
        
        if not GroupHandler.is_member(actor, group):
            print("User with id " + actor + " is not a member of group " + gid)
            return
        
        group["members"][actor] += 1
        updated_group = BalanceHandler.recalculate_gifts(actor, gid, write_to_replica=False)
        DataHandler.write_group(actor, updated_group)