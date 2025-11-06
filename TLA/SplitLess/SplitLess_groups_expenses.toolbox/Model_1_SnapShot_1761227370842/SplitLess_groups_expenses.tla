---------------------- MODULE SplitLess_groups_expenses ----------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS USERS, POSSIBLE_SHARES, POSSIBLE_EXPENSE_IDs, POSSIBLE_GROUP_IDs, NO_EXPENSE, NO_GROUP

VARIABLES  recordedExpenses, groups
          
          
Expense == [id : POSSIBLE_EXPENSE_IDs, group : POSSIBLE_GROUP_IDs \cup {NO_GROUP}, payer : USERS, amount : Nat, shares : POSSIBLE_SHARES, deleted : BOOLEAN]
Group == [id: POSSIBLE_GROUP_IDs, creator : USERS, members : [USERS -> BOOLEAN], expenseids : SUBSET POSSIBLE_EXPENSE_IDs, totalGifted : Nat, individualGiftsSent : [USERS -> Nat], passiveMembers : [USERS -> BOOLEAN]]
\* Groups just have totalGifted counter, as TLC cant handle rational numbers, so we loose the individual gifts received for each user

\* ----------------------------
\* Initialization
\* ----------------------------
Init ==
    /\ recordedExpenses = [ eid \in POSSIBLE_EXPENSE_IDs |-> NO_EXPENSE ]
    /\ groups = [ gid \in POSSIBLE_GROUP_IDs |-> NO_GROUP]

\* ----------------------------
\* Helper functions
\* ----------------------------
RECURSIVE SumFunction(_)
SumFunction(F) ==
  IF DOMAIN F = {} THEN 0
  ELSE LET d == CHOOSE x \in DOMAIN F: TRUE
       IN F[d] + SumFunction([y \in DOMAIN F \ {d} |-> F[y]])

Balance(u, gid) ==
    LET
        groupExpenses == { eid \in groups[gid].expenseids :
                            /\ recordedExpenses[eid] # NO_EXPENSE
                            /\ recordedExpenses[eid].deleted = FALSE }
    IN
        SumFunction([ eid \in groupExpenses |-> IF recordedExpenses[eid].payer = u THEN recordedExpenses[eid].amount ELSE 0 ])
      - SumFunction([ eid \in groupExpenses |-> recordedExpenses[eid].shares[u]])
      - groups[gid].individualGiftsSent[u]

\* ----------------------------
\* Recalculate gifts helper
\* ----------------------------

\* Calculate balance of users in a group without any gifts given
ComputeBalances(grp, recordedExpensesIn) ==
  [ u \in USERS |-> 
      LET groupExpenses == { eid \in grp.expenseids : recordedExpensesIn[eid] # NO_EXPENSE /\ recordedExpensesIn[eid].deleted = FALSE }
      IN SumFunction([eid \in groupExpenses |-> IF recordedExpensesIn[eid].payer = u THEN recordedExpensesIn[eid].amount ELSE 0])
         - SumFunction([eid \in groupExpenses |-> recordedExpensesIn[eid].shares[u]])
  ]

\* Computes gifts wihtin a group by looking at members not in the group with positive balance
\* This also removes gifts where a modified expense removes the funding for the gift
ComputeGifts(grp, balances) ==
  LET giftedUsers == { u \in USERS : grp.members[u] = FALSE /\ balances[u] > 0 } \* all users not in group with positive balance (they gift sth)
      newTotalGifted == SumFunction([u \in giftedUsers |-> balances[u]])
      newIndividualGifts == [u \in USERS |-> IF u \in giftedUsers THEN balances[u] ELSE 0]
  IN [ grp EXCEPT !.totalGifted = newTotalGifted, !.individualGiftsSent = newIndividualGifts
     ]

RecalcGifts(groupsIn, recordedExpensesIn) ==
  [ gid \in POSSIBLE_GROUP_IDs |-> 
      IF groupsIn[gid] = NO_GROUP THEN NO_GROUP
      ELSE LET grp == groupsIn[gid]
               balances == ComputeBalances(grp, recordedExpensesIn)
           IN ComputeGifts(grp, balances)
  ]


\* ----------------------------
\* Group Operations
\* ----------------------------
CreateGroup ==
    \E actor \in USERS :
    \E gid \in POSSIBLE_GROUP_IDs :
        /\ groups[gid] = NO_GROUP
        /\ LET newGroup == [ id |-> gid, creator |-> actor,
                             members |-> [u \in USERS |-> IF u = actor THEN TRUE ELSE FALSE],
                             expenseids |-> {}, totalGifted |-> 0,
                             individualGiftsSent |-> [u \in USERS |-> 0],
                             passiveMembers |-> [u \in USERS |-> FALSE]]
           IN groups' = [groups EXCEPT ![gid] = newGroup]
        /\ UNCHANGED <<recordedExpenses>>

AddMember ==
    \E actor, newMember \in USERS :
    \E gid \in POSSIBLE_GROUP_IDs :
        /\ groups[gid] # NO_GROUP
        /\ groups[gid].members[actor] = TRUE
        /\ groups[gid].members[newMember] = FALSE
        /\ groups' = [groups EXCEPT ![gid].members[newMember] = TRUE, ![gid].passiveMembers[newMember] = FALSE]
        /\ UNCHANGED <<recordedExpenses>>

LeaveGroup ==
    \E actor \in USERS :
    \E gid \in POSSIBLE_GROUP_IDs :
        /\ groups[gid] # NO_GROUP
        /\ groups[gid].members[actor] = TRUE
        /\ Balance(actor, gid) >= 0
        /\ LET updatedGroups == [ groups EXCEPT ![gid].members[actor] = FALSE, ![gid].passiveMembers[actor] = TRUE ]
           IN /\ groups' = RecalcGifts(updatedGroups, recordedExpenses)
              /\ UNCHANGED <<recordedExpenses>>


\* ----------------------------
\* Expense Operations
\* ----------------------------
CreateExpense ==
        \E actor \in USERS :
        \E payer \in USERS :
        \E shares \in POSSIBLE_SHARES :
        \E eid \in POSSIBLE_EXPENSE_IDs  :
            /\ SumFunction(shares) > 0
            /\ recordedExpenses[eid] = NO_EXPENSE
            /\ LET newExpense == [ id |-> eid, group |-> NO_GROUP, payer |-> payer, amount |-> SumFunction(shares), shares |-> shares, deleted |-> FALSE]
               IN /\ recordedExpenses' = [ recordedExpenses EXCEPT ![eid] = newExpense]
                  /\ UNCHANGED <<groups>>
               
AddExpenseToGroup ==
        \E actor \in USERS :
        \E eid \in POSSIBLE_EXPENSE_IDs :
        \E gid \in POSSIBLE_GROUP_IDs :
            /\ groups[gid] # NO_GROUP
            /\ recordedExpenses[eid] # NO_EXPENSE
            /\ groups[gid].members[actor] = TRUE
            /\ recordedExpenses[eid].group = NO_GROUP
            /\ groups[gid].members[recordedExpenses[eid].payer] = TRUE \* payer has shares 0
            /\ {u \in USERS : recordedExpenses[eid].shares[u] > 0} \subseteq {u \in USERS : groups[gid].members[u] = TRUE}
            /\ LET newExpense == [ recordedExpenses[eid] EXCEPT !.group = gid]
               IN /\ recordedExpenses' = [ recordedExpenses EXCEPT ![eid] = newExpense]
                  /\ groups' = [ groups EXCEPT ![gid].expenseids = @ \cup {eid}]
                  
RemoveExpenseFromGroup ==
        \E actor \in USERS :
        \E eid \in POSSIBLE_EXPENSE_IDs :
        \E gid \in POSSIBLE_GROUP_IDs :
            /\ groups[gid] # NO_GROUP
            /\ recordedExpenses[eid] # NO_EXPENSE
            /\ groups[gid].members[actor] = TRUE
            /\ recordedExpenses[eid] # NO_EXPENSE
            /\ recordedExpenses[eid].group = gid
            /\ recordedExpenses[eid].payer = actor
            \*/\ groups[gid].members[recordedExpenses[eid].payer] = TRUE
            /\ LET newExpense == [ recordedExpenses[eid] EXCEPT !.group = NO_GROUP ]
                   newExpenses == [ recordedExpenses EXCEPT ![eid] = newExpense ]
                   groupsWithout == [ groups EXCEPT ![gid].expenseids = @ \ {eid} ]
               IN /\ recordedExpenses' = newExpenses
                  /\ groups' = RecalcGifts(groupsWithout, newExpenses)

                  
ModifyExpenseParameters ==
        \E actor \in USERS :
        \E shares \in POSSIBLE_SHARES :
        \E eid \in POSSIBLE_EXPENSE_IDs  :
            /\ recordedExpenses[eid] # NO_EXPENSE
            /\ recordedExpenses[eid].payer = actor
            /\ SumFunction(shares) > 0
            /\ IF recordedExpenses[eid].group # NO_GROUP
               \* If an expense is in a group, only group members can have positive shares
               THEN {u \in USERS : shares[u] > 0} \subseteq {u \in USERS : groups[recordedExpenses[eid].group].members[u] = TRUE} 
               ELSE TRUE
            /\ IF recordedExpenses[eid].group = NO_GROUP
               THEN 
                    /\ recordedExpenses' = [ recordedExpenses EXCEPT ![eid].shares = shares, ![eid].amount = SumFunction(shares)]
                    /\ UNCHANGED <<groups>>
               ELSE LET newExpenses == [recordedExpenses EXCEPT ![eid].shares = shares, ![eid].amount = SumFunction(shares)]
                    IN 
                        /\ groups' = RecalcGifts(groups, newExpenses) 
                        /\ recordedExpenses' = newExpenses
                        
DeleteExpense ==
        \E actor \in USERS :
        \E eid \in POSSIBLE_EXPENSE_IDs :
            /\ recordedExpenses[eid] # NO_EXPENSE
            /\ recordedExpenses[eid].payer = actor
            /\ recordedExpenses[eid].deleted = FALSE
            /\ IF recordedExpenses[eid].group # NO_GROUP
               THEN /\ groups[recordedExpenses[eid].group].members[actor] = TRUE
               ELSE TRUE
            /\ LET newExpenses == [ recordedExpenses EXCEPT ![eid].deleted = TRUE]
               IN /\ recordedExpenses' = newExpenses
                  /\ groups' = RecalcGifts(groups, newExpenses)
            
(*
AddExpense  ==
       \E actor \in USERS : 
       \E shares \in POSSIBLE_SHARES :
       \E eid \in POSSIBLE_EXPENSE_IDs  : 
       \E gid \in POSSIBLE_GROUP_IDs :
          /\ groups[gid] # NO_GROUP
          /\ groups[gid].members[actor] = TRUE
          /\ {u \in USERS : shares[u] > 0} \subseteq {u \in USERS : groups[gid].members[u] = TRUE}
          /\ SumFunction(shares) > 0
          /\ recordedExpenses[eid] = NO_EXPENSE
          /\ LET newExpense == [ id |-> eid, group |-> gid, creator |-> actor, amount |-> SumFunction(shares), shares |-> shares, deleted |-> FALSE ]
             IN /\ recordedExpenses' = [ recordedExpenses EXCEPT ![eid] = newExpense]
                /\ groups' = [groups EXCEPT ![gid].expenseids = @ \cup {eid}]
                *)

(*DeleteExpense ==
    \E actor \in USERS :
    \E eid \in POSSIBLE_EXPENSE_IDs :
        /\ recordedExpenses[eid] # NO_EXPENSE
        /\ recordedExpenses[eid].creator = actor
        /\ recordedExpenses[eid].deleted = FALSE
        /\ groups[recordedExpenses[eid].group].members[actor] = TRUE
        /\ LET newExpenses == [recordedExpenses EXCEPT ![eid].deleted = TRUE]
           IN /\ recordedExpenses' = newExpenses
              /\ groups' = RecalcGifts(groups, newExpenses)
              *)
(*
ModifyExpense ==
    \E actor \in USERS :
    \E eid \in POSSIBLE_EXPENSE_IDs :
    \E shares \in POSSIBLE_SHARES :
        /\ recordedExpenses[eid] # NO_EXPENSE
        /\ recordedExpenses[eid].creator = actor
        /\ recordedExpenses[eid].deleted = FALSE
        /\ {u \in USERS : shares[u] > 0} \subseteq {u \in USERS : groups[recordedExpenses[eid].group].members[u] = TRUE}
        /\ SumFunction(shares) > 0
        /\ LET gid == recordedExpenses[eid].group
               newExpenses == [recordedExpenses EXCEPT ![eid].shares = shares, ![eid].amount = SumFunction(shares)]
           IN groups' = RecalcGifts(groups, newExpenses) /\ recordedExpenses' = newExpenses
           *)

\* ----------------------------
\* Next Relation
\* ----------------------------
Next ==
    \/ CreateGroup
    \/ AddMember
    \/ LeaveGroup
    \/ CreateExpense
    \/ AddExpenseToGroup
    \/ RemoveExpenseFromGroup
    \/ ModifyExpenseParameters
    \/ DeleteExpense
    \/ UNCHANGED <<recordedExpenses, groups>>

\* ----------------------------
\* Specification
\* ----------------------------
Spec == Init /\ [][Next]_<<recordedExpenses, groups>> 

\* ----------------------------
\* Invariants
\* ----------------------------
TypeOK ==
  /\ recordedExpenses \in [POSSIBLE_EXPENSE_IDs -> (Expense \cup {NO_EXPENSE})]
  /\ groups \in [POSSIBLE_GROUP_IDs -> (Group \cup {NO_GROUP})]

\* 1) The sum of all shares of each expense should equal the amount of the expense      
Inv_Conservertaion_of_amount ==
  \A eid \in DOMAIN recordedExpenses :
    recordedExpenses[eid] # NO_EXPENSE =>
      LET e == recordedExpenses[eid]
      IN e.amount = SumFunction(e.shares)

\* 2) Expense -> group consistency (if expense exists, the group referenced must exist)
\* Redundant now, from old model with expenses fixed in group
Inv_ExpenseRefersExistingGroup ==
  \A eid \in POSSIBLE_EXPENSE_IDs :
    recordedExpenses[eid] # NO_EXPENSE =>
      LET e == recordedExpenses[eid] IN
         /\ groups[e.group] # NO_GROUP

\* 3) Group listing consistency (if gid lists an eid, then recordedExpenses[eid] exists and points back)         
Inv_GroupContainsConsistentEids ==
  \A gid \in POSSIBLE_GROUP_IDs :
    groups[gid] # NO_GROUP =>
      \A eid \in groups[gid].expenseids :
         /\ recordedExpenses[eid].group = gid
         
\* 5) The sum of all balances in a group is always 0
Inv_GroupBalanceZero ==
  \A gid \in POSSIBLE_GROUP_IDs :
    groups[gid] # NO_GROUP =>
      LET allUsers == { u \in USERS : groups[gid].members[u] = TRUE }\*\/ groups[gid].passiveMembers[u] = TRUE}
          total == SumFunction([ u \in allUsers |-> Balance(u, gid) ])
      IN total + groups[gid].totalGifted = 0

Inv ==
  /\ TypeOK
  /\ Inv_Conservertaion_of_amount
  \*/\ Inv_ExpenseRefersExistingGroup
  /\ Inv_GroupContainsConsistentEids
  /\ Inv_GroupBalanceZero
=============================================================================
\* Modification History
\* Last modified Thu Oct 23 15:49:04 CEST 2025 by floyd
\* Last modified Fri Oct 17 10:13:37 CEST 2025 by floydpeiszan
\* Created Sat Oct 12 11:22:13 CEST 2025 by floy