from data_handler import DataHandler

class BalanceHandler:

    @staticmethod
    def get_balance(actor: str, user: str, gid: str):
        replica = DataHandler.get_user_replica(actor)
        if not replica:
            return (None, "User " + actor + " replica does not exist on local storage.")
        group = replica.get("groups").get(gid)
        if not group: 
            return (None, "Group " + gid + " does not exist on users " + actor + " replica.")
        if not group.get("members")[user]: #and group.get("members")[user] % 2 == 0:
            #print("User " + user + " is not a member in the group " + gid)
            #print("User " + user + " was never a member of the group " + gid)
            return (None, "User " + user + " was never a member of the group " + gid)
        
        expenses = replica["recorded_expenses"]
        group_expenses = [
            e for e in expenses.values() if e["group"] == gid and not e.get("deleted")
        ]
        pays = sum(expense["amount"] for expense in group_expenses if expense["payer"] == user)
        owes = sum(expense["shares"].get(user, 0.0) for expense in group_expenses)
        gifts_sent = group["gifts_sent"].get(user, 0.0)
        
        group_member_cardinality = sum(value % 2 == 1 for value in group.get("members").values())

        balance = pays - owes - gifts_sent
        if not group_member_cardinality == 0:
            gifts_received = group.get("gifts_received") / group_member_cardinality
            balance += gifts_received
        else :
            return (None, "There is no user left in the group. The total amount gifted to the group is " + str(group.get("gifts_received")) + ".")

        #balance = pays - owes - gifts_sent + gifts_received
        return (balance, "")


    @staticmethod
    def compute_balance_group_expenses(user, group, group_expenses):
        pays = sum(expense["amount"] for expense in group_expenses if expense["payer"] == user)
        owes = sum(expense["shares"].get(user, 0.0) for expense in group_expenses)

        balance = pays - owes
        return balance


    @staticmethod
    def compute_balances(group, expenses):
        balances = {}
        gid = group.get("gid")
        members = group.get("members").keys()
        group_expenses = [
            e for e in expenses.values() if e["group"] == gid and not e.get("deleted")
        ]
        for member in members:
            balances[member] = BalanceHandler.compute_balance_group_expenses(member, group, group_expenses)
        
        return balances
    
    @staticmethod
    def compute_gifts(group, balances):
        gifting_users = [
            user for user, bal in balances.items()
            if group.get("members").get(user) % 2 == 0 and group.get("members").get(user) > 0 and bal > 0
        ]
        total_gifted = sum(balances[u] for u in gifting_users)

        individual_gifts_sent = {
            user: (balances[user] if user in gifting_users else 0.0)
            for user in group["members"].keys()
        }
        group["gifts_received"] = total_gifted
        group["gifts_sent"] = individual_gifts_sent

        return group



    @staticmethod
    def recalculate_gifts(user_id: str, gid: str, write_to_replica: bool):
        replica = DataHandler.get_user_replica(user_id)
        if not replica:
            return (-1, "[BalanceHandler] Users " + user_id + " replica does not exist on local storage.")
        group = replica.get("groups").get(gid)
        expenses = replica.get("recorded_expenses")
        
        if not group:
            return (-1, "[BalanceHandler]  Group " + gid + " does not exist on user " + user_id + " replica.")
        
        balances = BalanceHandler.compute_balances(group, expenses)
        updated_group = BalanceHandler.compute_gifts(group, balances)

        if write_to_replica: DataHandler.write_group(user_id, updated_group)
        return updated_group
        
