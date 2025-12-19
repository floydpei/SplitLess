---------------------- MODULE SplitLess_replica_group_expenses ----------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    USERS,
    POSSIBLE_SHARES,
    POSSIBLE_EXPENSE_IDs,
    POSSIBLE_GROUP_IDs,
    NO_EXPENSE,
    NO_GROUP,
    POSSIBLE_REPLICA_IDs,
    ASSIGNED_REPLICA

VARIABLES replicas, actionCounter

\* ----------------------------
\* Records
\* ----------------------------

Expense ==
        [ id : POSSIBLE_EXPENSE_IDs,
          group : POSSIBLE_GROUP_IDs \cup {NO_GROUP},
          version : Nat,  \* current version of expense, only payer can edit expense and each user only works on at most one replica, a simple grow only counter is sufficient
          payer : USERS,
          amount : Nat,
          \*shares : POSSIBLE_SHARES,
          shares : [USERS -> Nat], \* if payer absorbs the share of a left member, their share can be higher than the max in POSSIBLE_SHARES
          acknowledged_shares : [USERS -> BOOLEAN],
          deleted : BOOLEAN ]

Group ==
        [ id : POSSIBLE_GROUP_IDs,
          members : [USERS -> Nat], \* Casul length counter for each user
          totalGifted : Nat,
          individualGiftsSent : [USERS -> Nat] ]

Replica ==
        [ id : POSSIBLE_REPLICA_IDs,
          recordedExpenses : [POSSIBLE_EXPENSE_IDs -> (Expense \cup {NO_EXPENSE})],
          groups : [POSSIBLE_GROUP_IDs -> (Group \cup {NO_GROUP})]
        ]

\* ----------------------------
\* Initialization
\* ----------------------------
Init ==
       /\ replicas =
            [ rid \in POSSIBLE_REPLICA_IDs |->
                [ id |-> rid,
                  recordedExpenses |-> [eid \in POSSIBLE_EXPENSE_IDs |-> NO_EXPENSE],
                  groups |-> [gid \in POSSIBLE_GROUP_IDs |-> NO_GROUP]
                ]
            ]
       /\ actionCounter = 0

\* ----------------------------
\* Helper Functions
\* ----------------------------

\* Get expenseIds that are added to a specific group
GroupExpenseIds(gid, recordedExpensesIn) ==
  { eid \in POSSIBLE_EXPENSE_IDs :
      /\ recordedExpensesIn[eid] # NO_EXPENSE
      /\ recordedExpensesIn[eid].deleted = FALSE
      /\ recordedExpensesIn[eid].group = gid 
      /\ \A u \in DOMAIN recordedExpensesIn[eid].shares :
           (recordedExpensesIn[eid].shares[u] > 0)
             => recordedExpensesIn[eid].acknowledged_shares[u] = TRUE}
      
IsMember(memberCounter) ==
  memberCounter % 2 = 1

WasEverMember(memberCounter) ==
  memberCounter > 0

RECURSIVE SumFunction(_)
SumFunction(F) ==
      IF DOMAIN F = {} THEN 0
      ELSE LET d == CHOOSE x \in DOMAIN F : TRUE
           IN F[d] + SumFunction([y \in DOMAIN F \ {d} |-> F[y]])


Balance(u, gid, replica) ==
        LET groupExpenses == GroupExpenseIds(gid, replica.recordedExpenses)
        IN SumFunction([ eid \in groupExpenses |-> 
                            IF replica.recordedExpenses[eid].payer = u 
                            THEN replica.recordedExpenses[eid].amount ELSE 0 ])
           - SumFunction([ eid \in groupExpenses |-> replica.recordedExpenses[eid].shares[u] ])
           - replica.groups[gid].individualGiftsSent[u]


ComputeBalances(grp, recordedExpensesIn) ==
      [ u \in USERS |->
          LET groupExpenses == GroupExpenseIds(grp.id, recordedExpensesIn)
          IN SumFunction([eid \in groupExpenses |-> 
                            IF recordedExpensesIn[eid].payer = u 
                            THEN recordedExpensesIn[eid].amount ELSE 0])
             - SumFunction([eid \in groupExpenses |-> recordedExpensesIn[eid].shares[u]])
      ]


ComputeGifts(grp, balances) ==
      LET giftingUsers ==
            { u \in USERS : ~IsMember(grp.members[u]) /\ balances[u] > 0 }
          newTotalGifted == SumFunction([u \in giftingUsers |-> balances[u]])
          newIndividualGifts == [u \in USERS |-> IF u \in giftingUsers THEN balances[u] ELSE 0]
      IN [ grp EXCEPT !.totalGifted = newTotalGifted,
                      !.individualGiftsSent = newIndividualGifts ]


RecalcGifts(groupsIn, recordedExpensesIn) ==
      [ gid \in POSSIBLE_GROUP_IDs |->
          IF groupsIn[gid] = NO_GROUP THEN NO_GROUP
          ELSE LET grp == groupsIn[gid]
                   balances == ComputeBalances(grp, recordedExpensesIn)
               IN ComputeGifts(grp, balances)
      ]
      

\* ----------------------------
\* Group actions
\* ----------------------------

CreateGroup ==
      \E actor \in USERS :
      \E gid \in POSSIBLE_GROUP_IDs :
      \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        \* Ensure each gid is only used once across replicas, real app use pseudorandom functions or similar
        /\ \A otherRid \in POSSIBLE_REPLICA_IDs : replicas[otherRid].groups[gid] = NO_GROUP
        /\ LET newGroup ==
              [ id |-> gid,
                members |-> [u \in USERS |-> IF u = actor THEN 1 ELSE 0],
                totalGifted |-> 0,
                individualGiftsSent |-> [u \in USERS |-> 0]]
             newReplica ==
              [ replicas[rid] EXCEPT !.groups = [@ EXCEPT ![gid] = newGroup] ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
              /\ actionCounter' = actionCounter + 1
              
AddMember ==
      \E actor, newMember \in USERS :
      \E gid \in POSSIBLE_GROUP_IDs :
      \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ replicas[rid].groups[gid] # NO_GROUP
        /\ IsMember(replicas[rid].groups[gid].members[actor])
        /\ ~IsMember(replicas[rid].groups[gid].members[newMember])
        /\ LET newReplica ==
              [ replicas[rid] EXCEPT !.groups = 
                  [@ EXCEPT ![gid].members[newMember] = @ + 1] ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
              /\ actionCounter' = actionCounter + 1

LeaveGroup ==
      \E actor \in USERS :
      \E gid \in POSSIBLE_GROUP_IDs :
      \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ replicas[rid].groups[gid] # NO_GROUP
        /\ IsMember(replicas[rid].groups[gid].members[actor])
        /\ Balance(actor, gid, replicas[rid]) >= 0
        /\ LET updatedGroups ==
              [ replicas[rid].groups EXCEPT
                  ![gid].members[actor] = @ + 1]
             newGroups == RecalcGifts(updatedGroups, replicas[rid].recordedExpenses)
             newReplica ==
               [ replicas[rid] EXCEPT !.groups = newGroups ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
              /\ actionCounter' = actionCounter + 1


\* ----------------------------
\* Expense actions
\* ----------------------------

CreateExpense ==
      \E actor \in USERS :
      \E shares \in POSSIBLE_SHARES :
      \E eid \in POSSIBLE_EXPENSE_IDs :
      \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ SumFunction(shares) > 0
        /\ \A otherRid \in POSSIBLE_REPLICA_IDs : replicas[otherRid].recordedExpenses[eid] = NO_EXPENSE
        /\ LET newExpense ==
              [ id |-> eid,
                group |-> NO_GROUP,
                version |-> 0,
                payer |-> actor,
                amount |-> SumFunction(shares),
                shares |-> shares,
                acknowledged_shares |-> [u \in USERS |-> IF u = actor /\ shares[u] > 0 THEN TRUE ELSE FALSE],
                deleted |-> FALSE ]
             newReplica ==
               [ replicas[rid] EXCEPT !.recordedExpenses = [@ EXCEPT ![eid] = newExpense] ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
              /\ actionCounter' = actionCounter + 1

AddExpenseToGroup ==
      \E actor \in USERS :
      \E eid \in POSSIBLE_EXPENSE_IDs :
      \E gid \in POSSIBLE_GROUP_IDs :
      \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ replicas[rid].groups[gid] # NO_GROUP
        /\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
        /\ IsMember(replicas[rid].groups[gid].members[actor])
        /\ replicas[rid].recordedExpenses[eid].payer = actor
        /\ replicas[rid].recordedExpenses[eid].group = NO_GROUP
        /\ {u \in USERS : replicas[rid].recordedExpenses[eid].shares[u] > 0}
              \subseteq {u \in USERS : IsMember(replicas[rid].groups[gid].members[u])}
        /\ LET newExpense ==
              [ replicas[rid].recordedExpenses[eid] EXCEPT !.group = gid, !.version = @ + 1 ]
             newExpenses ==
               [ replicas[rid].recordedExpenses EXCEPT ![eid] = newExpense ]
             newReplica ==
               [ replicas[rid] EXCEPT !.recordedExpenses = newExpenses ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
              /\ actionCounter' = actionCounter + 1

RemoveExpenseFromGroup ==
      \E actor \in USERS :
      \E eid \in POSSIBLE_EXPENSE_IDs :
      \E gid \in POSSIBLE_GROUP_IDs :
      \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ replicas[rid].groups[gid] # NO_GROUP
        /\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
        /\ IsMember(replicas[rid].groups[gid].members[actor])
        /\ replicas[rid].recordedExpenses[eid].group = gid
        /\ replicas[rid].recordedExpenses[eid].payer = actor
        /\ LET newExpense == [ replicas[rid].recordedExpenses[eid] EXCEPT !.group = NO_GROUP, !.version = @ + 1, !.acknowledged_shares = [u \in USERS |-> IF u = actor /\ replicas[rid].recordedExpenses[eid].shares[u] > 0 THEN TRUE ELSE FALSE] ]
               newExpenses == [ replicas[rid].recordedExpenses EXCEPT ![eid] = newExpense ]
               newGroups == RecalcGifts(replicas[rid].groups, newExpenses)
               newReplica == [ replicas[rid] EXCEPT !.recordedExpenses = newExpenses,
                                                !.groups = newGroups ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
          /\ actionCounter' = actionCounter + 1

ModifyExpenseParameters ==
      \E actor \in USERS :
      \E shares \in POSSIBLE_SHARES :
      \E eid \in POSSIBLE_EXPENSE_IDs :
      \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
        /\ replicas[rid].recordedExpenses[eid].payer = actor
        /\ SumFunction(shares) > 0
        /\ ~replicas[rid].recordedExpenses[eid].deleted
        /\ IF replicas[rid].recordedExpenses[eid].group # NO_GROUP
           THEN {u \in USERS : shares[u] > 0}
                \subseteq {u \in USERS : IsMember(replicas[rid].groups[replicas[rid].recordedExpenses[eid].group].members[u])}
           ELSE TRUE
        /\ LET newExpenses ==
               [ replicas[rid].recordedExpenses EXCEPT
                  ![eid].shares = shares,
                  ![eid].acknowledged_shares = [u \in USERS |-> IF u = actor /\ shares[u] > 0 THEN TRUE ELSE FALSE],
                  ![eid].amount = SumFunction(shares),
                  ![eid].version = @ + 1 ]
             newGroups ==
               IF replicas[rid].recordedExpenses[eid].group = NO_GROUP
               THEN replicas[rid].groups
               ELSE RecalcGifts(replicas[rid].groups, newExpenses)
             newReplica ==
               [ replicas[rid] EXCEPT !.recordedExpenses = newExpenses,
                                      !.groups = newGroups ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
              /\ actionCounter' = actionCounter + 1

DeleteExpense ==
      \E actor \in USERS :
      \E eid \in POSSIBLE_EXPENSE_IDs :
      \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
        /\ replicas[rid].recordedExpenses[eid].payer = actor
        /\ replicas[rid].recordedExpenses[eid].deleted = FALSE
        /\ IF replicas[rid].recordedExpenses[eid].group # NO_GROUP
           THEN /\ IsMember(replicas[rid].groups[replicas[rid].recordedExpenses[eid].group].members[actor])
           ELSE TRUE
        /\ LET newExpenses ==
               [ replicas[rid].recordedExpenses EXCEPT ![eid].deleted = TRUE, ![eid].version = @ + 1 ]
             newGroups ==
               RecalcGifts(replicas[rid].groups, newExpenses)
             newReplica ==
               [ replicas[rid] EXCEPT !.recordedExpenses = newExpenses,
                                      !.groups = newGroups ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
              /\ actionCounter' = actionCounter + 1
              
AcknowledgeShare ==
    \E actor \in USERS :
    \E eid \in POSSIBLE_EXPENSE_IDs :
    \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
        /\ replicas[rid].recordedExpenses[eid].deleted = FALSE
        /\ replicas[rid].recordedExpenses[eid].group # NO_GROUP
        /\ IsMember(replicas[rid].groups[replicas[rid].recordedExpenses[eid].group].members[actor])
        /\ replicas[rid].recordedExpenses[eid].shares[actor] > 0
        /\ replicas[rid].recordedExpenses[eid].acknowledged_shares[actor] = FALSE
        /\ LET newExpenses ==
               [ replicas[rid].recordedExpenses EXCEPT ![eid].acknowledged_shares[actor] = TRUE ]
             newGroups ==
               RecalcGifts(replicas[rid].groups, newExpenses)
             newReplica ==
               [ replicas[rid] EXCEPT !.recordedExpenses = newExpenses,
                                      !.groups = newGroups ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
              \*/\ actionCounter' = actionCounter + 1
              /\ UNCHANGED actionCounter
                    
              
\* Payer absorbs share of a member who left and never acknowledged
PayerAbsorbsLeftMemberShare ==
    \E actor \in USERS :
    \E eid \in POSSIBLE_EXPENSE_IDs :
    \E leftMember \in USERS :
    \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ actor # leftMember
        /\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
        /\ replicas[rid].recordedExpenses[eid].deleted = FALSE
        /\ replicas[rid].recordedExpenses[eid].payer = actor
        /\ replicas[rid].recordedExpenses[eid].shares[leftMember] > 0
        /\ replicas[rid].recordedExpenses[eid].acknowledged_shares[leftMember] = FALSE
        /\ replicas[rid].recordedExpenses[eid].group # NO_GROUP
        /\ LET gid == replicas[rid].recordedExpenses[eid].group
           IN /\ replicas[rid].groups[gid] # NO_GROUP
              /\ IsMember(replicas[rid].groups[gid].members[actor])
              /\ ~IsMember(replicas[rid].groups[gid].members[leftMember])
              /\ WasEverMember(replicas[rid].groups[gid].members[leftMember])
              /\ LET oldShares == replicas[rid].recordedExpenses[eid].shares
                     leftShare == oldShares[leftMember]
                     newShares == [ u \in USERS |-> 
                         IF u = actor THEN oldShares[u] + leftShare
                         ELSE IF u = leftMember THEN 0
                         ELSE oldShares[u] ]
                     newExpenses ==
                       [ replicas[rid].recordedExpenses EXCEPT
                          ![eid].shares = newShares,
                          \*![eid].acknowledged_shares = [u \in USERS |-> 
                            \*  IF u = leftMember THEN FALSE
                              \*ELSE replicas[rid].recordedExpenses[eid].acknowledged_shares[u]],
                          ![eid].version = @ + 1 ]
                     newGroups == RecalcGifts(replicas[rid].groups, newExpenses)
                     newReplica ==
                       [ replicas[rid] EXCEPT !.recordedExpenses = newExpenses,
                                              !.groups = newGroups ]
                 IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
                    /\ UNCHANGED actionCounter
                    
\* Alternative conflict resolution: member rejoins to acknowledge
\* Follows the add member protocoll by having a group member reentering the rejoining one
RejoinToAcknowledge ==
    \E inviter, rejoiner \in USERS :
    \E gid \in POSSIBLE_GROUP_IDs :
    \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[inviter] = rid
        /\ replicas[rid].groups[gid] # NO_GROUP
        /\ IsMember(replicas[rid].groups[gid].members[inviter])
        /\ ~IsMember(replicas[rid].groups[gid].members[rejoiner])
        /\ WasEverMember(replicas[rid].groups[gid].members[rejoiner])
        /\ \E eid \in POSSIBLE_EXPENSE_IDs :
             /\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
             /\ replicas[rid].recordedExpenses[eid].group = gid
             /\ replicas[rid].recordedExpenses[eid].shares[rejoiner] > 0
             /\ replicas[rid].recordedExpenses[eid].acknowledged_shares[rejoiner] = FALSE
        /\ LET newReplica ==
              [ replicas[rid] EXCEPT !.groups = 
                  [@ EXCEPT ![gid].members[rejoiner] = @ + 1] ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
              /\ UNCHANGED actionCounter
          
          
\* ----------------------------
\* Merge action helpers
\* ----------------------------

MergeExpense(expOwn, expOther) ==
      IF expOwn = NO_EXPENSE /\ expOther = NO_EXPENSE
      THEN NO_EXPENSE
      ELSE IF expOwn # NO_EXPENSE /\ expOther = NO_EXPENSE
      THEN expOwn
      ELSE IF expOwn = NO_EXPENSE /\ expOther # NO_EXPENSE
      THEN expOther
      ELSE IF expOwn.version > expOther.version
      THEN expOwn
      ELSE IF expOwn.version < expOther.version
      THEN expOther
      ELSE 
        LET mergedAcknowledgedShares ==
              [ u \in USERS |-> 
                  expOwn.acknowledged_shares[u] \/ expOther.acknowledged_shares[u] ]
        IN [ expOwn EXCEPT !.acknowledged_shares = mergedAcknowledgedShares ]
        \*LET mergedDeleted == expOwn.deleted \/ expOther.deleted
        \*    useOwnVersion == expOwn.version >= expOther.version
          \*  baseExp == IF useOwnVersion THEN expOwn ELSE expOther
            \*mergedGroup == baseExp.group
              \*IF expOwn.group # NO_GROUP THEN expOwn.group ELSE expOther.group
       \* IN [ baseExp EXCEPT
         \*     !.deleted = mergedDeleted,
           \*   !.group = mergedGroup,
             \* !.version = IF useOwnVersion THEN expOwn.version ELSE expOther.version ]


MergeGroup(grpOwn, grpOther, mergedExpenses, gid) ==
      IF grpOwn = NO_GROUP /\ grpOther = NO_GROUP
      THEN NO_GROUP
      ELSE IF grpOwn # NO_GROUP /\ grpOther = NO_GROUP
      THEN grpOwn
      ELSE IF grpOwn = NO_GROUP /\ grpOther # NO_GROUP
      THEN grpOther
      ELSE
        LET mergedMembers ==
              [ u \in USERS |-> CHOOSE n \in { grpOwn.members[u], grpOther.members[u] } :
                                  n >= grpOwn.members[u] /\ n >= grpOther.members[u] ]
            mergedGroup == [ grpOwn EXCEPT !.members = mergedMembers ]
            balances == ComputeBalances(mergedGroup, mergedExpenses)
        IN ComputeGifts(mergedGroup, balances)

\* ----------------------------
\* Merge action 
\* ----------------------------

MergeReplicas ==
  \E ownRid, otherRid \in POSSIBLE_REPLICA_IDs :
    /\ ownRid # otherRid
    /\ LET
        mergedExpenses ==
          [ eid \in POSSIBLE_EXPENSE_IDs |->
              MergeExpense(replicas[ownRid].recordedExpenses[eid],
                           replicas[otherRid].recordedExpenses[eid]) ]

        mergedGroups ==
          [ gid \in POSSIBLE_GROUP_IDs |->
              MergeGroup(replicas[ownRid].groups[gid],
                         replicas[otherRid].groups[gid],
                         mergedExpenses,
                         gid) ]

        newReplica ==
          [ replicas[ownRid] EXCEPT
              !.groups = mergedGroups,
              !.recordedExpenses = mergedExpenses ]
      IN replicas' = [replicas EXCEPT ![ownRid] = newReplica]
         /\ UNCHANGED actionCounter


\* ----------------------------
\* Next relation
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
    \/ AcknowledgeShare
    \/ PayerAbsorbsLeftMemberShare
    \/ RejoinToAcknowledge
    \/ MergeReplicas
    \/ UNCHANGED <<replicas, actionCounter>>




\* ----------------------------
\* Invariants
\* ----------------------------
TypeOK ==
  \A rid \in POSSIBLE_REPLICA_IDs :
    /\ replicas[rid].recordedExpenses
         \in [POSSIBLE_EXPENSE_IDs -> (Expense \cup {NO_EXPENSE})]
    /\ replicas[rid].groups
         \in [POSSIBLE_GROUP_IDs -> (Group \cup {NO_GROUP})]

Inv_Conservation_of_amount ==
  \A rid \in POSSIBLE_REPLICA_IDs :
    \A eid \in POSSIBLE_EXPENSE_IDs :
      replicas[rid].recordedExpenses[eid] # NO_EXPENSE =>
        LET e == replicas[rid].recordedExpenses[eid]
        IN e.amount = SumFunction(e.shares)

Inv_ExpenseGroupExists ==
  \A rid \in POSSIBLE_REPLICA_IDs :
    \A eid \in POSSIBLE_EXPENSE_IDs :
      /\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
      /\ replicas[rid].recordedExpenses[eid].deleted = FALSE        \* remove this?
      /\ replicas[rid].recordedExpenses[eid].group # NO_GROUP
      =>
         replicas[rid].groups[ replicas[rid].recordedExpenses[eid].group ] # NO_GROUP


Inv_GroupBalanceZero ==
  \A rid \in POSSIBLE_REPLICA_IDs :
    \A gid \in POSSIBLE_GROUP_IDs :
      replicas[rid].groups[gid] # NO_GROUP =>
        LET allUsers ==
              \* include every user that was a member of the group at some part, as they always could accumulate negative balances
              { u \in USERS : WasEverMember(replicas[rid].groups[gid].members[u])}
            total ==
              SumFunction([ u \in allUsers |-> Balance(u, gid, replicas[rid]) ])
        IN total + replicas[rid].groups[gid].totalGifted = 0


Inv ==
  /\ TypeOK
  /\ Inv_Conservation_of_amount
  /\ Inv_ExpenseGroupExists
  /\ Inv_GroupBalanceZero

           
\* ----------------------------
\* Liveness Helper
\* ----------------------------
AllReplicasHaveAtLeastExpenseVersion(eid, version) ==
    \A rid \in POSSIBLE_REPLICA_IDs :
          /\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
          /\ replicas[rid].recordedExpenses[eid].version >= version

AllReplicasHaveAtLeastGroupMemberCounter(gid, user, counter) ==
    \A rid \in POSSIBLE_REPLICA_IDs :
        /\ replicas[rid].groups[gid] # NO_GROUP
        /\ replicas[rid].groups[gid].members[user] >= counter
        
AllPositiveSharesAcknowledged(eid, replica) ==
    replica.recordedExpenses[eid] = NO_EXPENSE
    \/
    \A u \in USERS :
        replica.recordedExpenses[eid].shares[u] > 0 
        => replica.recordedExpenses[eid].acknowledged_shares[u] = TRUE
  
\* ----------------------------
\* Liveness
\* ----------------------------

\* Expense version captures modifications and group membership
Liveness_ExpensePropagates ==
    \A rid \in POSSIBLE_REPLICA_IDs :
        \A eid \in POSSIBLE_EXPENSE_IDs :
            []<>(replicas[rid].recordedExpenses[eid] # NO_EXPENSE
                    => AllReplicasHaveAtLeastExpenseVersion(eid, replicas[rid].recordedExpenses[eid].version) )
            \*/\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
            \*=> []<>(AllReplicasHaveAtLeastExpenseVersion(eid, replicas[rid].recordedExpenses[eid].version))
            
Liveness_GroupMemberShipPropagates ==
    \A rid \in POSSIBLE_REPLICA_IDs :
        \A gid \in POSSIBLE_GROUP_IDs:
            \A user \in USERS:
                []<>(replicas[rid].groups[gid] # NO_GROUP
                        => AllReplicasHaveAtLeastGroupMemberCounter(gid, user, replicas[rid].groups[gid].members[user]) )
                        
\* Expenses in groups eventually resolve acknowledgment status
\* Either all shares are acknowledged or the expense is deleted/removed, or all members leave
Liveness_ExpenseSharesEventuallyAcknowledged ==
    \A rid \in POSSIBLE_REPLICA_IDs :
        \A eid \in POSSIBLE_EXPENSE_IDs :
            []<>(
                LET exp == replicas[rid].recordedExpenses[eid]
                IN /\ exp # NO_EXPENSE
                   /\ exp.group # NO_GROUP
                   /\ ~exp.deleted
                   => ( \/ AllPositiveSharesAcknowledged(eid, replicas[rid])
                        \/ exp.deleted
                        \/ exp.group = NO_GROUP
                        \/ \A u \in USERS : ~IsMember(replicas[rid].groups[exp.group].members[u]) ) )
                        
\*-----------------------------
\* Safety Helper
\*-----------------------------

NoDecreaseExpenseVersion ==
  \A rid \in POSSIBLE_REPLICA_IDs :
  \A eid \in POSSIBLE_EXPENSE_IDs :
    (replicas[rid].recordedExpenses[eid] # NO_EXPENSE)
      =>
      /\ replicas'[rid].recordedExpenses[eid] # NO_EXPENSE
      /\ replicas'[rid].recordedExpenses[eid].version
           >= replicas[rid].recordedExpenses[eid].version

NoDecreaseGroupMembersCounter ==
  \A rid \in POSSIBLE_REPLICA_IDs :
  \A gid \in POSSIBLE_GROUP_IDs :
  \A u \in USERS :
    (replicas[rid].groups[gid] # NO_GROUP)
      =>
      /\ replicas'[rid].groups[gid] # NO_GROUP
      /\ replicas'[rid].groups[gid].members[u]
           >= replicas[rid].groups[gid].members[u]
         
NoDecreaseAcknowledgedSharesSameVersion ==
  \A rid \in POSSIBLE_REPLICA_IDs :
  \A eid \in POSSIBLE_EXPENSE_IDs :
  \A u \in USERS :
    /\ replicas[rid].recordedExpenses[eid] # NO_EXPENSE
    \*/\ replicas'[rid].recordedExpenses[eid] # NO_EXPENSE this always exists by NoDecreaseExpenseVersion property
    /\ replicas[rid].recordedExpenses[eid].version = replicas'[rid].recordedExpenses[eid].version
    /\ replicas[rid].recordedExpenses[eid].acknowledged_shares[u] = TRUE
    =>
      replicas'[rid].recordedExpenses[eid].acknowledged_shares[u] = TRUE
           
\*-----------------------------
\* Safety
\*-----------------------------
Safety_ExpenseVersionsNonDecreasing ==
  [] [ NoDecreaseExpenseVersion ]_{<<replicas, actionCounter>>}
  
Safety_GroupMembersCounterNonDecreasing ==
  [] [ NoDecreaseGroupMembersCounter ]_{<<replicas, actionCounter>>}
  
Safety_AcknowledgedSharesNonDecreasingForSameVersion ==
  [] [ NoDecreaseAcknowledgedSharesSameVersion ]_{<<replicas, actionCounter>>}


\* ----------------------------
\* Specification
\* ----------------------------
Spec == Init /\ [][Next]_<<replicas, actionCounter>> 

FairSpec == 
    /\ Spec 
    /\ WF_<<replicas, actionCounter>>(MergeReplicas)
    /\ WF_<<replicas, actionCounter>>(AcknowledgeShare)
    /\ WF_<<replicas, actionCounter>>(PayerAbsorbsLeftMemberShare)
    /\ WF_<<replicas, actionCounter>>(RejoinToAcknowledge)

=============================================================================
\* Modification History
\* Last modified Sat Dec 13 12:37:29 CET 2025 by floyd
\* Created Fri Oct 24 11:14:17 CEST 2025 by floyd