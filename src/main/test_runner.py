import random
import copy

from group_handler import GroupHandler
from user_manager import UserManager
from expense_handler import ExpenseHandler
from replica_sync import ReplicaSync
from storage_provider import get_backend, use_memory_backend

NUM_USERS = 3
MAX_STEPS = 1000
MAX_TEST_RUNS = 1

backend = None

ACTIONS = [
    "invite",
    "accept",
    "leave",
    "add_expense",
    "edit_expense",
    "delete_expense",
]

users = []

ACTION_MAP = {}


def _setup():
    global users, backend
    use_memory_backend()
    backend = get_backend()

    clear_replics(users)

def clear_replics(users: list):
    for i in range(NUM_USERS):
        user_id = f"user{i}"
        username = f"user{i}"
        users.append(user_id)

        # Create empty replica with all known users
        replica = {
            "recorded_expenses": {},
            "groups": {},
            "known_users": {uid: f"user{idx}" for idx, uid in enumerate(range(NUM_USERS)) if uid != user_id}
        }

        backend.write_full_replica(user_id, replica)


def run_test(seed: int):
    global users
    rdm = random.Random(seed)

    for i in range(MAX_STEPS):
        #10% chance to trigger a merge between two distinct users
        if rdm.randint(0, 99) < 10 and len(users) > 1:
            user1, user2 = rdm.sample(users, 2)
            merge_action(user1, user2)
            continue
        
        #90% chance to trigger a different action
        next_action = rdm.choice(ACTIONS)
        #call the corresponding function dynamically
        ACTION_MAP[next_action](rdm)

        #TODO Add invarinat checks


def merge_action(user1, user2):
    ReplicaSync.user_id = user1
    user2_replica = backend.get_full_replica(user2)
    ReplicaSync._merge_replica(user2_replica)
    #print(f"Merged replicas of {user1} and {user2}")


def invite_action(rdm):
    inviter, invitee = rdm.sample(users, 2)
    # Pick a random group of inviter if any
    user_groups = list(backend.get_full_replica(inviter).get("groups", {}).keys())
    if not user_groups:
        return
    group_id = rdm.choice(user_groups)
    GroupHandler.invite_member(inviter, invitee, group_id)
    #print(f"{inviter} invited {invitee} to group {group_id}")


def accept_action(rdm):
    invitee = rdm.choice(users)
    #find a group where this user has an invitation
    invite_groups = []
    for uid in users:
        for gid, group in backend.get_groups(uid).items():
            if invitee in group.get("persumed_members", {}) and group["persumed_members"][invitee] % 2 == 1:
                invite_groups.append((uid, gid))
    if not invite_groups:
        return
    _, group_id = rdm.choice(invite_groups)
    GroupHandler.accept_invitation(invitee, group_id)
    #print(f"{invitee} accepted invitation to group {group_id}")


def leave_action(rdm):
    actor = rdm.choice(users)
    actor_groups = [gid for gid, group in backend.get_groups(actor).items()]
    if not actor_groups:
        return
    group_id = rdm.choice(actor_groups)
    GroupHandler.leave_group(actor, group_id)
    #print(f"{actor} left group {group_id}")


def add_expense_action(rdm):
    payer = rdm.choice(users)
    expense_name = f"expense_{rdm.randint(0, 1000000)}"
    shares = {uid: rdm.uniform(1, 100) for uid in users}
    ExpenseHandler.create_expense(payer, expense_name, shares)
    #print(f"{payer} created expense '{expense_name}' with shares {shares}")


def edit_expense_action(rdm):
    actor = rdm.choice(users)
    expenses = backend.get_expenses(actor)
    if not expenses:
        return
    eid = rdm.choice(list(expenses.keys()))
    expense = backend.get_expense(actor, eid)
    shares = {uid: rdm.uniform(1, 20) for uid in users}
    #print(f"{actor} edited expense {eid}, new shares {shares}")



def delete_expense_action(rdm):
    actor = rdm.choice(users)
    expenses = backend.get_expenses(actor)
    if not expenses:
        return
    eid = rdm.choice(list(expenses.keys()))
    ExpenseHandler.delete_expense(actor, eid)
    #print(f"{actor} deleted expense {eid}")


# Populate the action map
ACTION_MAP = {
    "invite": invite_action,
    "accept": accept_action,
    "leave": leave_action,
    "add_expense": add_expense_action,
    "edit_expense": edit_expense_action,
    "delete_expense": delete_expense_action,
}


if __name__ == "__main__":
    _setup()

    for i in range(MAX_TEST_RUNS):
        print(f"=== Test run {i} ===")
        run_test(seed=i)
        clear_replics([])

    print("All test runs finished.")
