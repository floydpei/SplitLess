import uuid
from dataclasses import dataclass, field, asdict
from typing import Dict
from data_handler import DataHandler
from balance_handler import BalanceHandler
from storage_provider import get_backend, get_backend_type

@dataclass
class Group:
    gid: str
    name: str
    gifts_received: int
    members: Dict[str, int] = field(default_factory=dict) # cls
    invited_members: Dict[str, int] = field(default_factory=dict) # cls
    gifts_sent: Dict[str, float] = field(default_factory=dict)

    def __str__(self):
        members_str = ", ".join([f"{uid}:{cls}" for uid, cls in self.members.items()]) or "None"
        invited_members_str = ", ".join([f"{uid}:{cls}" for uid, cls in self.invited_members.items()]) or "None"
        gifts_sent_str = ", ".join([f"{uid}:{amt:.2f}" for uid, amt in self.gifts_sent.items()]) or "None"
        return (
            f"Group '{self.name}' (id={self.gid})\n"
            f"  Gifts received: {self.gifts_received}\n"
            f"  Members (cls): {members_str}\n"
            f"  Persumed members (cls): {invited_members_str}\n"
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
    def is_member_contender(actor, group):
        if actor not in group.get("invited_members"): return False
        return group.get("invited_members").get(actor) % 2 == 1
    
    @staticmethod
    def get_members(actor: str, group: Group): 
        members = []
        for user in group.get("members"):
            if GroupHandler.is_member(user, group): members.append(user)
        return members
    
    @staticmethod
    def get_members_including_left(actor: str, group: Group):
        members = []
        for user in group.get("members"):
            members.append(user)
        return members

    @staticmethod
    def get_amount_members(actor: str, group: Group):
        return GroupHandler.get_members(actor, group).length
    
    @staticmethod
    def get_balances_in_group(actor: str, gid: str):
        backend = get_backend()
        replica = backend.get_full_replica(actor)
        return_str = ""
        if not replica:
            return (None, "[GroupHandler] User " + actor + " replica does not exist on local storage.")
        group = replica.get("groups").get(gid)
        if not group: 
            return (None, "[GroupHandler] Group " + gid + " does not exist on users " + actor + " replica.")
        
        group_members = GroupHandler.get_members(actor, group)
        balances = {}
        for member in group_members:
            balances[member] = BalanceHandler.get_balance(actor, member, gid)

        return (balances, return_str)

    @staticmethod
    def get_lowest_balance_in_group(actor: str, gid: str):
        balances, msg = GroupHandler.get_balances_in_group(actor, gid)
        if not balances:
            return (None, msg)
        min_item = min(balances.items(), key=lambda item: item[1])
        return (min_item, msg)
        

    
    @staticmethod
    def create_group(creator: str, name : str):
        backend = get_backend()
        gid = str(uuid.uuid4())
        members = {creator: 1}
        invited_members = {creator: 2}
        gifts_received = 0

        new_group = Group(gid=gid, name=name, members=members, invited_members=invited_members, gifts_received=gifts_received)
        group_as_dict = asdict(new_group)
        #print(group_as_dict)
        backend.write_group(creator, group_as_dict)
        return (gid, "[GroupHandler] Succesfully created a group with id " + gid)

    """
    @staticmethod
    def add_member(actor: str, new_member: str, gid: str):
        group = DataHandler.get_group(actor, gid)
        if not group:
            print("[GroupHandler] Group with " + gid + " does not exist on users " + actor + " replica")
            return -1
        if not GroupHandler.is_member(actor, group):
            print("[GroupHandler] User with id " + actor + " is not in the group with id " + gid + ", and cannot invite a user to it.")
            return -1
        known_users = DataHandler.get_known_users(actor).keys()
        if not new_member in known_users: 
            print("[GroupHandler] The user with id " + new_member + " is not known, so it cannot be added to the group.")
            return -1
        if GroupHandler.is_member(new_member, group):
            print("[GroupHandler] User with id " + new_member + " is already in the group")
            return -1
        
        group.get("members")[new_member] = group["members"].get(new_member, 0) + 1
        DataHandler.write_group(actor, group)
        if group.get("members")[new_member] > 1:
            BalanceHandler.recalculate_gifts(actor, gid, write_to_replica=True)
        print("[GroupHandler] Succesfully added user " + new_member + " to the group " + gid + ".")
        return 1
        """
    
    @staticmethod
    def invite_member(actor: str, new_member: str, gid: str):
        backend = get_backend()
        group = backend.get_group(actor, gid)
        if not group:
            return (-1, "[GroupHandler] Group with " + gid + " does not exist on users " + actor + " replica")
        if not GroupHandler.is_member(actor, group):
            return (-1, "[GroupHandler] User with id " + actor + " is not in the group with id " + gid + ", and cannot add a user to it.")
        known_users = backend.get_known_users(actor).keys()
        if not new_member in known_users: 
            return (-1, "[GroupHandler] The user with id " + new_member + " is not known, so it cannot be added to the group.")
        if GroupHandler.is_member(new_member, group):
            return (-1, "[GroupHandler] User with id " + new_member + " is already in the group")
        if GroupHandler.is_member_contender(new_member, group):
            return (-1, "[GroupHandler] User with id " + new_member + " is already invided to the group")
        
        group.get("invited_members")[new_member] = group.get("invited_members").get(new_member, 0) + 1
        backend.write_group(actor, group)
        return (1, "[GroupHandler] Succesfully invited user " + new_member + " to the group " + gid + ".")
    
    @staticmethod
    def accept_invitation(actor: str, gid: str):
        backend = get_backend()
        group = backend.get_group(actor, gid)
        if not group:
            return (-1 , "[GroupHandler] Group with " + gid + " does not exist on users " + actor + " replica")
        members = group.get("members")
        invited_members = group.get("invited_members")
        if GroupHandler.is_member(actor, group):
            return (-1, "[GroupHandler] User " + actor + " is already a member of the group " + gid)
        if not GroupHandler.is_member_contender(actor, group):
            return (-1, "[GroupHandler] User " + actor + " has no active invitation to the group " + gid)
        members[actor] = members.get(actor, 0) + 1
        invited_members[actor] = invited_members.get(actor, 0) + 1
        backend.write_group(actor, group)
        return (1, "[GroupHandler] User " + actor + " has is now a member of the group " + gid)


    @staticmethod
    def leave_group(actor: str, gid: str):
        backend = get_backend()
        group = backend.get_group(actor, gid)
        if not group:
            return (-1, "[GroupHandler] Group with " + gid + " does not exist on users " + actor + " replica")
        
        if not GroupHandler.is_member(actor, group):
            return (-1 ,"[GroupHandler] User with id " + actor + " is not a member of group " + gid)
        
        user_balance, _ = BalanceHandler.get_balance(actor, actor, gid)
        if user_balance < 0:
            return (-1, f"[GroupHandler] User {actor} has a negative balance of {user_balance} and can not leave the group.")
        
        group["members"][actor] += 1
        backend.write_group(actor, group)
        updated_group = BalanceHandler.recalculate_gifts(actor, gid, write_to_replica=False)
        backend.write_group(actor, updated_group)
        return (1, "[GroupHandler] User" + actor + " left the group " + gid + ".")


