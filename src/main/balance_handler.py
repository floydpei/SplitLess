from data_handler import DataHandler

class BalanceHandler:

    @staticmethod
    def get_balance(actor: str, gid: str):
        replica = DataHandler.get_user_replica(actor)
        group = replica["groups"].get(gid)
        if not group: 
            print("Group " + gid + " does not exist on users " + actor + " replica.")
            return
        
        expenses = replica["recorded_expenses"]
        group_expenses = [
            e for e in expenses.values() if e["group"] == gid and not e.get("deleted")
        ]
        pays = sum(expense["amount"] for expense in group_expenses if expense["payer"] == actor)
        owes = sum(expense["shares"].get(actor, 0.0) for expense in group_expenses)
        gifts_sent = group["gifts_sent"].get(actor, 0.0)

        balance = pays - owes - gifts_sent
        return balance


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
        #("called")
        gifting_users = [
            user for user, bal in balances.items()
            if group["members"].get(user, 0) % 2 == 1 and bal > 0
            #if GroupHandler.is_member(user, group) and bal > 0
        ]

        total_gifted = sum(balances[u] for u in gifting_users)

        individual_gifts_sent = {
            user: (balances[user] if user in gifting_users else 0.0)
            for user in group["members"].keys()
        }

        # Update the group fields
        group["gifts_received"] = total_gifted
        group["gifts_sent"] = individual_gifts_sent

        return group



    @staticmethod
    def recalculate_gifts(user_id: str, gid: str, write_to_replica: bool):
        replica = DataHandler.get_user_replica(user_id)
        group = replica.get("groups").get(gid)
        expenses = replica.get("recorded_expenses")
        
        if not group:
            print("Group " + gid + " does not exist on user " + user_id + " replica.")
            return
        
        balances = BalanceHandler.compute_balances(group, expenses)
        updated_group = BalanceHandler.compute_gifts(group, balances)

        if write_to_replica: DataHandler.write_group(user_id, updated_group)
        return updated_group
        
