from collections import defaultdict
import random
import math
import pprint
from typing import Tuple, List
import time
import argparse

from group_handler import GroupHandler
from expense_handler import ExpenseHandler
from replica_sync import ReplicaSync
from storage_provider import get_backend, use_memory_backend
from balance_handler import BalanceHandler

NUM_USERS = 5
MAX_STEPS = 1000
MAX_TEST_RUNS = 10000
EPS = 1e-6  # float comparisons

backend = None

ACTIONS = [
    "invite",
    "accept",
    "leave",
    "create_group",
    "create_expense",
    "add_expense_to_group",
    "remove_expense_from_group",
    "edit_expense",
    "delete_expense",
    "acknowledge_share",
    "payer_absorbs_left_member"
]

def get_action_weights(step, max_steps):
    progress = step / max_steps
    
    if progress < 0.02: #group creation
        return {
            "create_group": 0.35,
            "invite":       0.28,
            "accept":       0.28,
            "leave":        0.01,
            "create_expense":       0.02,
            "add_expense_to_group": 0.01,
            "remove_expense_from_group": 0.01,
            "edit_expense":         0.02,
            "delete_expense":       0.01,
            "acknowledge_share":     0.01,
            "payer_absorbs_left_member":    0.00
        }
    elif progress < 0.10:  # group membership
        return {
            "create_group": 0.02,
            "invite":       0.30,
            "accept":       0.30,
            "leave":        0.03,
            "create_expense":       0.10,
            "add_expense_to_group": 0.06,
            "remove_expense_from_group": 0.06,
            "edit_expense":         0.05,
            "delete_expense":       0.03,
            "acknowledge_share":     0.05,
            "payer_absorbs_left_member":    0.00
        }
    else:  # expense heavy
        return {
            "create_group": 0.01,
            "invite":       0.05,
            "accept":       0.05,
            "leave":        0.05,
            "create_expense":       0.09,
            "add_expense_to_group": 0.19,
            "remove_expense_from_group": 0.02,
            "edit_expense":         0.09,
            "delete_expense":       0.09,
            "acknowledge_share":     0.24,
            "payer_absorbs_left_member":    0.03
        }

users = []
action_counter = defaultdict(lambda: {"Passed": 0, "Failed": 0})

ACTION_MAP = {}


def _setup():
    global users, backend
    use_memory_backend()
    backend = get_backend()

    clear_replics(users)

def clear_replics(users: list):
    all_user_ids = [f"user{i}" for i in range(NUM_USERS)]
    for i in range(NUM_USERS):
        user_id = f"user{i}"
        users.append(user_id)
        replica = {
            "recorded_expenses": {},
            "groups": {},
            "known_users": {
                uid: uid for uid in all_user_ids
            }
        }
        backend.write_full_replica(user_id, replica)


def invariant_conservation_of_amount(replica: dict) -> Tuple[bool, str]:
    expenses = replica.get("recorded_expenses", {})
    for eid, e in expenses.items():
        if not e:
            continue
        shares = e.get("shares", {})
        sum_shares = sum(shares.values())
        amount = float(e.get("amount", 0.0))
        if not math.isclose(amount, sum_shares, rel_tol=0.0, abs_tol=EPS):
            return False, f"Conservation violated for expense {eid}: amount={amount} != sum(shares)={sum_shares}"
    return True, ""

def invariant_expense_group_exists(replica: dict) -> Tuple[bool, str]:
    expenses = replica.get("recorded_expenses", {})
    groups = replica.get("groups", {})
    for eid, e in expenses.items():
        if not e:
            continue
        gid = e.get("group")
        if gid is None:
            continue
        if gid not in groups:
            return False, f"Expense {eid} references missing group {gid}"
    return True, ""

def invariant_group_balance_zero(replica: dict) -> Tuple[bool, str]:
    groups = replica.get("groups", {})
    expenses = replica.get("recorded_expenses", {})
    for gid, group in groups.items():
        if not group:
            continue

        group_expenses = [
            e for e in expenses.values() 
            if e["group"] == gid 
            and not e.get("deleted") 
            and all(e.get("shares", {}).get(u, 0) <= 0 or e.get("acknowledged_shares", {}).get(u, False) 
                    for u in e.get("shares", {}))
        ]
        group_balance = 0.0
        member_balances = {}
        for member in GroupHandler.get_members_including_left("not_used_string", group):
            member_balance, _ = BalanceHandler.get_balance_test(user=member, group=group, group_expenses=group_expenses)
            member_balances[member] = member_balance
            if member_balance:
                group_balance += member_balance

        if not math.isclose(group_balance, 0.0, rel_tol=0.0, abs_tol=EPS):
            return False, f"Group balance non-zero for {gid}: sum(balances)={group_balance}\n{member_balances}"
    return True, ""

def check_invariants(replica: dict) -> Tuple[bool, List[str]]:
    checks = [
        invariant_conservation_of_amount,
        invariant_expense_group_exists,
        invariant_group_balance_zero
    ]
    errors = []
    for check in checks:
        ok, msg = check(replica)
        if not ok:
            errors.append(msg)
    return (len(errors) == 0), errors


def temporal_no_decrease_expense_version(old_state: dict, new_state: dict) -> Tuple[bool, str]:
    old_expenses = old_state.get("recorded_expenses", {})
    new_expenses = new_state.get("recorded_expenses", {})
    
    for eid, old_expense in old_expenses.items():   
        new_expense = new_expenses.get(eid)
        
        if not new_expense:
            return False, f"Expense {eid} existed but was removed (version decreased from {old_expense.get('version')} to None)"
        
        old_version = old_expense.get("version", 0)
        new_version = new_expense.get("version", 0)
        
        if new_version < old_version:
            return False, f"Expense {eid} version decreased from {old_version} to {new_version}"
    
    return True, ""

def temporal_no_decrease_group_members_counter(old_state: dict, new_state: dict) -> Tuple[bool, str]:
    old_groups = old_state.get("groups", {})
    new_groups = new_state.get("groups", {})
    
    for gid, old_group in old_groups.items():     
        new_group = new_groups.get(gid)

        if not new_group:
            return False, f"Group {gid} existed but was removed"
        
        old_members = old_group.get("invited_members", {})
        new_members = new_group.get("invited_members", {})

        for user, old_counter in old_members.items():
            new_counter = new_members.get(user, 0)

            if new_counter < old_counter:
                return False, f"Group {gid} member counter for {user} decreased from {old_counter} to {new_counter}"
    
    return True, ""

def check_temporal_properties(old_state: dict, new_state: dict) -> Tuple[bool, List[str]]:
    checks = [
        temporal_no_decrease_expense_version,
        temporal_no_decrease_group_members_counter,
    ]
    errors = []
    for check in checks:
        ok, msg = check(old_state, new_state)
        if not ok:
            errors.append(msg)
    return (len(errors) == 0), errors


def do_final_merges():
    #all users merge into user0
    user0 = users[0]
    ReplicaSync.user_id = user0
    for user in users:
        if user == user0: continue
        to_merge_replica = backend.get_full_replica_deep(user)
        ReplicaSync._merge_replica(to_merge_replica)

    #user0 merges into all users
    user0_replica = backend.get_full_replica_deep(user0)
    for user in users:
        if user == user0: continue
        ReplicaSync.user_id = user
        ReplicaSync._merge_replica(user0_replica)

def check_all_replicas_the_same():
    first = backend.get_full_replica(users[0])
    for i, u in enumerate(users[1:], start=1):
        replica = backend.get_full_replica(u)
        if replica != first:
            return False, f"Users {users[0]} replica differs from users {users[i]}s replica"
    return True, ""


# final liveness:

def has_unacknowledged_shares_in_active_groups():   # Check if there are any unacked shares in non-empty groups
    for user in users:
        replica = backend.get_full_replica(user)
        expenses = replica.get("recorded_expenses", {})
        groups = replica.get("groups", {})
        
        for eid, expense in expenses.items():
            if not expense or expense.get("deleted"):
                continue
            
            gid = expense.get("group")
            if not gid:
                continue
            
            group = groups.get(gid)
            if not group:
                continue
            
            has_active_member = any(GroupHandler.is_member(u, group) for u in users)
            if not has_active_member:
                continue
            
            for uid in users:
                share = expense.get("shares", {}).get(uid, 0)
                if share > 0 and not expense.get("acknowledged_shares", {}).get(uid, False):
                    return True

    return False

#3 Options to ack share

#1 If uid is a member, they can acknowledge
def option_acknowledge_by_member(uid, eid, group):
    if GroupHandler.is_member(uid, group):
        status, _ = ExpenseHandler.acknowledge_share(uid, eid)
        if status == 1:
            return True
    return False

#2 If uid left, payer can absorb
def option_payer_absorbs_left_member(uid, eid, payer, group, users):
    if GroupHandler.was_ever_member(uid, group) and not GroupHandler.is_member(uid, group):
        if payer and GroupHandler.is_member(payer, group):
            # Find a replica where payer is the user
            for payer_user in users:
                if payer_user == payer:
                    status, _ = ExpenseHandler.payer_absorbs_left_member_share(payer, eid, uid)
                    if status == 1:
                        return True
                    break
    return False

#3 If uid left but was a member, rejoin to acknowledge
def option_rejoin_and_acknowledge(uid, eid, gid, group, users):
    if GroupHandler.was_ever_member(uid, group) and not GroupHandler.is_member(uid, group):
        #print("GROUP:\n\n")
        #print(group)
        status, _ = GroupHandler.accept_invitation(uid, gid)
        if status == 1:
         #   print("was already invited\n")
            status, _ = ExpenseHandler.acknowledge_share(uid, eid)
            if status == 1:
                return True

        # Find a current member to invite uid back
        inviter = None
        for potential_inviter in users:
            if potential_inviter == uid: continue
            inviter_replica = backend.get_full_replica(potential_inviter)
            inviter_group = inviter_replica.get("groups", {}).get(gid)
            if inviter_group and GroupHandler.is_member(potential_inviter, inviter_group):
                inviter = potential_inviter
                break

        if inviter:
            #1 Inviter invites uid
            status, msg = GroupHandler.invite_member(inviter, uid, gid)
            #if status != 1:
          #      print("invite failed on inveriters " + inviter + " replica \n " + msg + "\n" )
           #     print(inviter_group)
             #   return False

            #2 Merge inviter's replica to uid's replica
            ReplicaSync.user_id = uid
            inviter_replica = backend.get_full_replica_deep(inviter)
            ReplicaSync._merge_replica(inviter_replica)

            #3 uid accepts invitation
            status, msg = GroupHandler.accept_invitation(uid, gid)
            #if status == 1:
             #   print("invitation accept failed for " + uid + " inviter " + inviter + " " + msg)
              #  print(backend.get_group(uid, gid))
               # print(backend.get_expense(uid, eid))
                #return False

            #4 uid acknowledges share
            status, _ = ExpenseHandler.acknowledge_share(uid, eid)
            if status == 1:
                return True

    return False

# try to resolve unack share for user
def resolve_unacknowledged_share_for_user(user):
    replica = backend.get_full_replica(user)
    expenses = replica.get("recorded_expenses", {})
    groups = replica.get("groups", {})
    
    for eid, expense in expenses.items():
        if not expense or expense.get("deleted"):
            continue
        
        gid = expense.get("group")
        if not gid:
            continue
        
        group = groups.get(gid)
        if not group:
            continue
        
        has_active_member = any(GroupHandler.is_member(u, group) for u in users)
        if not has_active_member:
            continue
        
        # find unacknowledged share for this user
        for uid in users:
            share = expense.get("shares", {}).get(uid, 0)
            if share <= 0:
                continue
            if expense.get("acknowledged_shares", {}).get(uid, False):
                continue
            
            payer = expense.get("payer")
            
            # option 1
            if option_acknowledge_by_member(uid, eid, group):
                #print("option_1")
                return True
            # option 2
            elif option_payer_absorbs_left_member(uid, eid, payer, group, users):
                #print("option_2")
                return True
            # option 3
            elif option_rejoin_and_acknowledge(uid, eid, gid, group, users):
                #print("option_3")
                return True
    
    return False



def resolve_all_unacknowledged_shares(max_iterations=MAX_STEPS):    
    for iteration in range(max_iterations):
        # check if there are any unacknowledged shares left
        if not has_unacknowledged_shares_in_active_groups():
            return True
                
        progress_made = False
        # Try to resolve one unacknowledged share for each user
        for user in users:
            progress_made = resolve_unacknowledged_share_for_user(user)
        #if progress_made: print("progress")
        
        do_final_merges()

    print(f"[Liveness] WARNING: Failed to resolve all shares after {max_iterations} iterations")
    return False


def check_liveness_all_pos_shares_acked():
    for user in users:
        replica = backend.get_full_replica(user)
        expenses = replica.get("recorded_expenses", {})
        groups = replica.get("groups", {})
        
        for eid, expense in expenses.items():
            if not expense or expense.get("deleted"):
                continue
            
            gid = expense.get("group")
            if not gid:
                continue
            
            group = groups.get(gid)
            if not group:
                continue
            
            # Check if group has at least one active member
            has_active_member = any(GroupHandler.is_member(u, group) for u in users)
            if not has_active_member:
                continue
            
            # Check that all positive shares are acknowledged
            for uid in users:
                share = expense.get("shares", {}).get(uid, 0)
                if share > 0 and not expense.get("acknowledged_shares", {}).get(uid, False):
                    return False, f"Expense {eid} has unacknowledged share for user {uid} \n {group} \n {expense}"
    
    return True, ""


def run_test(seed: int, do_temp_cheks=False):
    global users
    rdm = random.Random(seed)

    for step in range(MAX_STEPS):
        if rdm.randint(0, 99) < 20 and len(users) > 1:
            user1, user2 = rdm.sample(users, 2)
            action_name = "merge"
            affected_users = [user1, user2]
            action_args = (user1, user2)
        else:
            current_weights = get_action_weights(step, MAX_STEPS)
            action_name = rdm.choices(population=list(current_weights.keys()), weights=list(current_weights.values()), k=1)[0]
            if action_name == "invite":
                inviter, invitee = rdm.sample(users, 2)
                affected_users = [inviter, invitee]
                action_args = (inviter, invitee)
            else:
                actor = rdm.choice(users)
                affected_users = [actor]
                action_args = (actor,)

        if do_temp_cheks: old_state = {uid: backend.get_full_replica_deep(uid) for uid in affected_users}

        status = ""
        if action_name == "merge":
            merge_action(*action_args)
            action_counter[action_name]["Passed"] += 1
        else:
            status = ACTION_MAP[action_name](rdm, *action_args)

        if status == 1:
            action_counter[action_name]["Passed"] += 1
        elif status == -1:
            action_counter[action_name]["Failed"] += 1

        new_state = {uid: backend.get_full_replica(uid) for uid in affected_users}

        for uid in affected_users:
            #invariants
            ok, errs = check_invariants(new_state[uid])
            if not ok:
                print(f"[ERROR] Invariant violation for {uid} at step {step}, action {action_name}")
                print(errs)
                print(f"Affected users: {affected_users}")
                print("State:")
                pprint.pprint(new_state[uid])
                return -1, errs
            #safety
            if do_temp_cheks:
                ok, errs = check_temporal_properties(old_state[uid], new_state[uid])
                if not ok:
                    print(f"[ERROR] Temporal property violation for {uid} at step {step}, action {action_name}")
                    print(errs)
                    print("Old state:")
                    pprint.pprint(old_state[uid])
                    print("New state:")
                    pprint.pprint(new_state[uid])
                    return -1, errs

    # final liveness
    do_final_merges()
    resolve_all_unacknowledged_shares()
    all_replicas_the_same, err = check_all_replicas_the_same()
    all_pos_shares_acked, err2 = check_liveness_all_pos_shares_acked()
    if not all_replicas_the_same:
        print(f"[ERROR] Not all replicas are the same after the final merges")
        print(err)
        return -1, err
    if not all_pos_shares_acked:
        print(f"[ERROR] Not all postivie shares got acknowleged")
        print(err2)
        return -1, err2
    
    return True, ""


def merge_action(user1, user2):
    ReplicaSync.user_id = user1
    user2_replica = backend.get_full_replica_deep(user2)
    ReplicaSync._merge_replica(user2_replica)


def create_group_action(rdm, creator):
    group_name = f"group_{rdm.randint(0, 1000000)}"
    status, _ = GroupHandler.create_group(creator, group_name)
    return status

def invite_action(rdm, inviter, invitee):
    user_groups = list(backend.get_full_replica(inviter).get("groups", {}).keys())
    if not user_groups:
        return
    gid = rdm.choice(user_groups)
    status, _ = GroupHandler.invite_member(inviter, invitee, gid)
    return status

def accept_action(rdm, invitee):
    invite_groups = []
    for uid in users:
        for gid, group in backend.get_groups(uid).items():
            if invitee in group.get("invited_members", {}) and group["invited_members"][invitee] % 2 == 1:
                invite_groups.append((uid, gid))
    if not invite_groups:
        return
    _, gid = rdm.choice(invite_groups)
    status, _ = GroupHandler.accept_invitation(invitee, gid)
    return status

def leave_action(rdm, actor):
    actor_groups = [gid for gid in backend.get_groups(actor).keys()]
    if not actor_groups:
        return
    gid = rdm.choice(actor_groups)
    status, _ = GroupHandler.leave_group(actor, gid)
    return status


def create_expense_action(rdm, actor, zero_share_chance=0.5, addable_chance=0.8):
    if rdm.random() < addable_chance:
        return create_addable_expense_action(rdm, actor, zero_share_chance=zero_share_chance)
    else:
        return create_random_expense_action(rdm, actor, zero_share_chance=zero_share_chance)

def create_random_expense_action(rdm, actor, zero_share_chance=0.8):
    expense_name = f"expense_{rdm.randint(0, 1000000)}"
    shares = {}
    positive_share_exists = False
    
    for uid in users:
        if rdm.random() < zero_share_chance:
            shares[uid] = 0
        else:
            shares[uid] = rdm.uniform(1, 100)
            positive_share_exists = True

    if not positive_share_exists and users:
        user_to_force_positive = rdm.choice(list(users))
        shares[user_to_force_positive] = rdm.uniform(1, 100)

    status, _ = ExpenseHandler.create_expense(actor, expense_name, shares)
    return status

def create_addable_expense_action(rdm, actor, zero_share_chance):
    replica = backend.get_full_replica(actor)
    groups = replica.get("groups", {})

    member_groups = [gid for gid, g in groups.items() if GroupHandler.is_member(actor, g)]
    if not member_groups:
        return create_random_expense_action(rdm, actor, zero_share_chance=zero_share_chance)

    gid = rdm.choice(member_groups)
    group = groups[gid]

    members = list(GroupHandler.get_members("not_used_string", group))

    if not members:
        return create_random_expense_action(rdm, actor, zero_share_chance=zero_share_chance)

    expense_name = f"exp_addable_{rdm.randint(0, 10_000_000)}"
    shares = {uid: rdm.uniform(1, 100) for uid in members}

    status, _ = ExpenseHandler.create_expense(actor, expense_name, shares)
    return status
     
def add_expense_to_group_action(rdm, actor, smart_chance=0.8):
    if rdm.random() < smart_chance:
        return add_expense_to_group_smart_action(rdm, actor)
    else:
        return add_expense_to_group_random_action(rdm, actor)

def add_expense_to_group_random_action(rdm, actor):
    replica = backend.get_full_replica(actor)
    expenses = replica.get("recorded_expenses", {})
    groups = replica.get("groups", {})
    if not expenses or not groups:
        return
    eid = rdm.choice(list(expenses.keys()))
    gid = rdm.choice(list(groups.keys()))

    status, _ = ExpenseHandler.add_expense_to_group(actor, eid, gid)
    return status

def add_expense_to_group_smart_action(rdm, actor):
    replica = backend.get_full_replica(actor)
    expenses = replica.get("recorded_expenses", {})
    groups = replica.get("groups", {})
    
    if not expenses or not groups:
        return -1
    
    member_groups = {gid: g for gid, g in groups.items() if GroupHandler.is_member(actor, g)}
    
    if not member_groups:
        return -1

    actor_expenses = {eid: e for eid, e in expenses.items() 
                     if e and e.get("payer") == actor}
    
    if not actor_expenses:
        return -1

    valid_pairs = []
    for eid, expense in actor_expenses.items():
        shares = expense.get("shares", {})
        users_with_positive_shares = {uid for uid, share in shares.items() if share > 0}
        for gid, group in member_groups.items():
            group_members = set(GroupHandler.get_members("not_used", group))
            
            if users_with_positive_shares.issubset(group_members):
                valid_pairs.append((eid, gid))
    
    if not valid_pairs:
        return -1
    
    eid, gid = rdm.choice(valid_pairs)
    status, _ = ExpenseHandler.add_expense_to_group(actor, eid, gid)
    return status

def remove_expense_from_group_action(rdm, actor, smart_chance=0.8):
    if rdm.random() < smart_chance:
        return remove_expense_from_group_smart_action(rdm, actor)
    else:
        return remove_expense_from_group_random_action(rdm, actor)


def remove_expense_from_group_random_action(rdm, actor):
    expenses = backend.get_expenses(actor)
    if not expenses:
        return -1
    eid = rdm.choice(list(expenses.keys()))
    
    status, _ = ExpenseHandler.remove_expense_from_group(actor, eid)
    return status


def remove_expense_from_group_smart_action(rdm, actor):
    replica = backend.get_full_replica(actor)
    expenses = replica.get("recorded_expenses", {})
    groups = replica.get("groups", {})
    
    if not expenses or not groups:
        return -1
    
    removable_expenses = []
    
    for eid, expense in expenses.items():
        if not expense or expense.get("deleted"):
            continue
        if expense.get("payer") != actor:
            continue
        
        gid = expense.get("group")
        if not gid:
            continue
        
        group = groups.get(gid)
        if not group or not GroupHandler.is_member(actor, group):
            continue
        
        removable_expenses.append(eid)
    
    if not removable_expenses:
        return -1
    
    eid = rdm.choice(removable_expenses)
    status, _ = ExpenseHandler.remove_expense_from_group(actor, eid)
    return status

def edit_expense_action(rdm, actor, zero_share_chance=0.8):
    expenses = backend.get_expenses(actor)
    if not expenses:
        return
    eid = rdm.choice(list(expenses.keys()))

    shares = {}
    positive_share_exists = False
    
    for uid in users:
        if rdm.random() < zero_share_chance:
            shares[uid] = 0
        else:
            shares[uid] = rdm.uniform(1, 20)
            positive_share_exists = True
    
    if not positive_share_exists and users:
        user_to_force_positive = rdm.choice(list(users))
        shares[user_to_force_positive] = rdm.uniform(1, 20)

    status, _ = ExpenseHandler.modify_expense_parameters(actor, eid, shares)
    return status

def delete_expense_action(rdm, actor):
    expenses = backend.get_expenses(actor)
    if not expenses:
        return
    eid = rdm.choice(list(expenses.keys()))

    status, _ = ExpenseHandler.delete_expense(actor, eid)
    return status

def acknowledge_expense_action(rdm, actor, smart_chance=0.8):
    if rdm.random() < smart_chance:
        return acknowledge_expense_smart_action(rdm, actor)
    else:
        return acknowledge_expense_random_action(rdm, actor)


def acknowledge_expense_random_action(rdm, actor):
    expenses = backend.get_expenses(actor)
    if not expenses:
        return
    eid = rdm.choice(list(expenses.keys()))

    status, _ = ExpenseHandler.acknowledge_share(actor, eid)
    return status


def acknowledge_expense_smart_action(rdm, actor):
    replica = backend.get_full_replica(actor)
    expenses = replica.get("recorded_expenses", {})
    groups = replica.get("groups", {})
    
    if not expenses or not groups:
        return acknowledge_expense_random_action(rdm, actor)
    
    for eid, expense in expenses.items():
        if not expense:
            continue
        gid = expense.get("group")
        if not gid:
            continue
        group = groups.get(gid)
        if not group or not GroupHandler.is_member(actor, group):
            continue
        if expense.get("shares", {}).get(actor, 0) <= 0:
            continue
        if expense.get("acknowledged_shares", {}).get(actor, False):
            continue
        if expense.get("deleted", False):
            continue
        
        status, _ = ExpenseHandler.acknowledge_share(actor, eid)
        return status
    
    return acknowledge_expense_random_action(rdm, actor)

def payer_absorbs_left_member_action(rdm, actor, smart_chance=0.9):
    if rdm.random() < smart_chance:
        return payer_absorbs_left_member_smart_action(rdm, actor)
    else:
        return payer_absorbs_left_member_random_action(rdm, actor)


def payer_absorbs_left_member_random_action(rdm, actor):
    expenses = backend.get_expenses(actor)
    if not expenses:
        return -1
    eid = rdm.choice(list(expenses.keys()))
    
    # Pick random user
    left_member = rdm.choice(users)
    
    status, _ = ExpenseHandler.payer_absorbs_left_member_share(actor, eid, left_member)
    return status


def payer_absorbs_left_member_smart_action(rdm, actor):
    replica = backend.get_full_replica(actor)
    expenses = replica.get("recorded_expenses", {})
    groups = replica.get("groups", {})
    
    if not expenses or not groups:
        return -1
    
    valid_pairs = []
    
    for eid, expense in expenses.items():
        if not expense or expense.get("deleted"):
            continue
        if expense.get("payer") != actor:
            continue
        
        gid = expense.get("group")
        if not gid:
            continue
        
        group = groups.get(gid)
        if not group or not GroupHandler.is_member(actor, group):
            continue
        
        for user in users:
            if user == actor:
                continue
            if GroupHandler.is_member(user, group):
                continue
            if not GroupHandler.was_ever_member(user, group):
                continue
            if expense.get("shares", {}).get(user, 0) <= 0:
                continue
            if expense.get("acknowledged_shares", {}).get(user, False):
                continue
            
            valid_pairs.append((eid, user))
    
    if not valid_pairs:
        return -1
    
    eid, left_member = rdm.choice(valid_pairs)
    status, _ = ExpenseHandler.payer_absorbs_left_member_share(actor, eid, left_member)
    return status


ACTION_MAP = {
    "invite": invite_action,
    "accept": accept_action,
    "leave": leave_action,
    "create_group": create_group_action,
    "create_expense": create_expense_action,
    "add_expense_to_group": add_expense_to_group_action,
    "remove_expense_from_group": remove_expense_from_group_action,
    "edit_expense": edit_expense_action,
    "delete_expense": delete_expense_action,
    "acknowledge_share": acknowledge_expense_action,
    "payer_absorbs_left_member": payer_absorbs_left_member_action
}

def format_hms(seconds):
    h = int(seconds // 3600)
    m = int((seconds % 3600) // 60)
    s = int(seconds % 60)
    return f"{h:02d}H_{m:02d}M_{s:02d}S"

def log_print(*args, **kwargs):
            print(*args, **kwargs)             # to console
            print(*args, file=f, **kwargs)     # to file


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Run probabilistic tests on expense sharing app')
    parser.add_argument('--do_temp_check', action='store_true', 
                        help='Enable temporal property checks (slower but more thorough)')
    args = parser.parse_args()
    if args.do_temp_check:
        print("Running with temporal property checks enabled")
    else:
        print("Running without temporal property checks (faster)")

    _setup()

    total_expenses = 0
    total_groups = 0
    total_time = 0.0

    start_seed = random.randint(0,1000000000)
    error_found = False
    error_seed = None

    aggregated_actions = defaultdict(lambda: {"Passed": 0, "Failed": 0})

    for i in range(MAX_TEST_RUNS):
        seed = start_seed + i
        start = time.perf_counter()

        print(f"Running test {i+1}/{MAX_TEST_RUNS}... with seed {seed} ", end="\r")
        result, errs = run_test(seed=seed, do_temp_cheks=args.do_temp_check)
        if result == -1:
            error_found = True
            error_seed = seed
            print(f"\n{'='*70}")
            print(f"ERROR DETECTED IN TEST RUN {i+1} (seed={seed})")
            print(f"{'='*70}")
            #break

        run_time = time.perf_counter() - start
        total_time += run_time
        elapsed_time = format_hms(total_time)
        print(f"Running test {i+1}/{MAX_TEST_RUNS}... with seed {seed}   Elapsed time: {elapsed_time}   ", end="\r")

        #collect results
        last_state = backend.get_full_replica("user1")
        total_expenses += len(last_state.get("recorded_expenses"))
        total_groups += len(last_state.get("groups"))
        
        for action_name, counts in action_counter.items():
            aggregated_actions[action_name]["Passed"] += counts["Passed"]
            aggregated_actions[action_name]["Failed"] += counts["Failed"]
        
        clear_replics([])
    
    filename = f"Testlog_Users{NUM_USERS}_Steps{MAX_STEPS}_Runs{MAX_TEST_RUNS}_Temp_check{args.do_temp_check}.txt"

    if error_found:
        with open(filename, "w") as f:
            log_print(f"\nTests stopped due to error in seed {error_seed}")
            log_print(f"Errors found: {errs}")
            log_print(f"To reproduce: run with seed={error_seed}")
            log_print(f"Completed {i}/{MAX_TEST_RUNS} tests before error")

    with open(filename, "w") as f:

        log_print(f"\n{'='*70}")
        log_print(f"  Average Results over {MAX_TEST_RUNS} test runs with temporal checks: {args.do_temp_check}")
        log_print(f"{'='*70}")
        
        log_print(f"\n Summary:")
        log_print(f"  Average expenses created: {total_expenses / MAX_TEST_RUNS:.1f}")
        log_print(f"  Average groups created:   {total_groups / MAX_TEST_RUNS:.1f}")

        avg_time = total_time / MAX_TEST_RUNS
        log_print(f"\n Timing:")
        log_print(f"  Total time:   {format_hms(total_time)}")
        log_print(f"  Average/test: {avg_time:.3f}s")

        log_print(f"\n Action Results (Total across all runs):")
        log_print(f"  {'Action':<30} {'Passed':>14} {'Failed':>14} {'Total':>14} {'Pass Rate':>14}")
        log_print(f"  {'-'*30} {'-'*14} {'-'*14} {'-'*14} {'-'*14}")
        
        for action_name in sorted(aggregated_actions.keys()):
            passed = aggregated_actions[action_name]["Passed"]
            failed = aggregated_actions[action_name]["Failed"]
            total = passed + failed
            pass_rate = (passed / total * 100) if total > 0 else 0
            log_print(f"  {action_name:<30} {passed:>14} {failed:>14} {total:>14} {pass_rate:>13.1f}%")
        
        log_print(f"\n{'='*70}")
        log_print(" All test runs finished.")
        log_print(f"{'='*70}")

