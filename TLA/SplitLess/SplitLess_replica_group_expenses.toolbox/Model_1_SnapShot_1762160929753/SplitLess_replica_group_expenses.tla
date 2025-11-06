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
          group : POSSIBLE_GROUP_IDs \cup {NO_GROUP},  \* current group for easier access
          version : Nat,  \* current version of expense, only payer can edit expense and each user only works on at most one replica, a simple grow only counter is sufficient
          payer : USERS,
          amount : Nat,
          shares : POSSIBLE_SHARES,
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
      /\ recordedExpensesIn[eid].group = gid }
      
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
            { u \in USERS : IsMember(grp.members[u]) /\ balances[u] > 0 }
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
              \*/\ UNCHANGED<<actionCounter>>

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
        \* Ensure each eid is only used once across replicas, real app use pseudorandom functions or similar
        /\ \A otherRid \in POSSIBLE_REPLICA_IDs : replicas[otherRid].recordedExpenses[eid] = NO_EXPENSE
        /\ LET newExpense ==
              [ id |-> eid,
                group |-> NO_GROUP,
                version |-> 0,
                payer |-> actor,
                amount |-> SumFunction(shares),
                shares |-> shares,
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
              [ replicas[rid].recordedExpenses[eid] EXCEPT !.group = gid ]
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
        /\ LET newExpense == [ replicas[rid].recordedExpenses[eid] EXCEPT !.group = NO_GROUP ]
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
        /\ IF replicas[rid].recordedExpenses[eid].group # NO_GROUP
           THEN {u \in USERS : shares[u] > 0}
                \subseteq {u \in USERS : IsMember(replicas[rid].groups[replicas[rid].recordedExpenses[eid].group].members[u])}
           ELSE TRUE
        /\ LET newExpenses ==
               [ replicas[rid].recordedExpenses EXCEPT
                  ![eid].shares = shares,
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
               [ replicas[rid].recordedExpenses EXCEPT ![eid].deleted = TRUE ]
             newGroups ==
               RecalcGifts(replicas[rid].groups, newExpenses)
             newReplica ==
               [ replicas[rid] EXCEPT !.recordedExpenses = newExpenses,
                                      !.groups = newGroups ]
           IN /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
              /\ actionCounter' = actionCounter + 1
          
          
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
      ELSE
        LET mergedDeleted == expOwn.deleted \/ expOther.deleted
            useOwnVersion == expOwn.version >= expOther.version
            baseExp == IF useOwnVersion THEN expOwn ELSE expOther
            mergedGroup ==
              IF expOwn.group # NO_GROUP THEN expOwn.group ELSE expOther.group
        IN [ baseExp EXCEPT
              !.deleted = mergedDeleted,
              !.group = mergedGroup,
              !.version = IF useOwnVersion THEN expOwn.version ELSE expOther.version ]


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
    \/ MergeReplicas
    \/ UNCHANGED <<replicas, actionCounter>>

\* ----------------------------
\* Specification
\* ----------------------------
Spec == Init /\ [][Next]_<<replicas, actionCounter>> 

FairSpec == Spec /\ WF_<<replicas, actionCounter>>(MergeReplicas)


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
      /\ replicas[rid].recordedExpenses[eid].deleted = FALSE
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
        
Inv_ExpenseOnlyInOneGroup ==
    \A rid \in POSSIBLE_REPLICA_IDs :
        \A eid \in POSSIBLE_EXPENSE_IDs :
            replicas[rid].recordedExpenses[eid] # NO_EXPENSE =>
            LET allCounters ==
              {replicas[rid].recordedExpenses[eid].groupCounter[gid] : gid \in DOMAIN replicas[rid].recordedExpenses[eid].groupCounter}
            IN Cardinality( {evenCounters \in allCounters: evenCounters % 2 = 1} ) <= 1


Inv ==
  /\ TypeOK
  /\ Inv_Conservation_of_amount
  /\ Inv_ExpenseGroupExists
  /\ Inv_GroupBalanceZero


\* ----------------------------
\* Liveness Helper
\* ----------------------------
ReplicasWithExpense(eid) ==
    { r \in POSSIBLE_REPLICA_IDs : replicas[r].recordedExpenses[eid] # NO_EXPENSE }

ExpenseVersions(eid) ==
    LET rs == ReplicasWithExpense(eid)
    IN { replicas[r].recordedExpenses[eid].version : r \in rs }

MaxExpenseVersion(eid) ==
    LET versions == ExpenseVersions(eid)
    IN IF versions = {} THEN 0
       ELSE CHOOSE v \in versions : \A w \in versions : v >= w
     
AllReplicasCaughtUp(eid) ==
    LET v == MaxExpenseVersion(eid)
    IN \A r \in POSSIBLE_REPLICA_IDs :
         replicas[r].recordedExpenses[eid] # NO_EXPENSE =>
            replicas[r].recordedExpenses[eid].version >= v


ReplicasWithGroup(gid) ==
    { r \in POSSIBLE_REPLICA_IDs : replicas[r].groups[gid] # NO_GROUP }
    
MaxGroupMemberCounter(gid, u) ==
    LET rs == ReplicasWithGroup(gid)
        counters == { replicas[r].groups[gid].members[u] : r \in rs }
    IN IF counters = {} THEN 0
       ELSE CHOOSE c \in counters : \A d \in counters : c >= d
       
AllReplicasCaughtUpMember(gid, u) ==
    LET maxC == MaxGroupMemberCounter(gid, u)
    IN \A r \in POSSIBLE_REPLICA_IDs :
         replicas[r].groups[gid] # NO_GROUP =>
           replicas[r].groups[gid].members[u] >= maxC

\* dont do expense to group assignment in version of expense as the version already holds info on modification of expense parameters (like shares)
AllReplicasAgreeOnExpenseGroup(eid) ==
    \A r1, r2 \in POSSIBLE_REPLICA_IDs :
        /\ replicas[r1].recordedExpenses[eid] # NO_EXPENSE
        /\ replicas[r2].recordedExpenses[eid] # NO_EXPENSE
        => replicas[r1].recordedExpenses[eid].group = replicas[r2].recordedExpenses[eid].group

  
\* ----------------------------
\* Liveness
\* ----------------------------

Liveness_ExpenseVersionPropagates ==
    \A eid \in POSSIBLE_EXPENSE_IDs : []<>(AllReplicasCaughtUp(eid))

Liveness_GroupMembershipPropagates ==
    \A gid \in POSSIBLE_GROUP_IDs :
       \A u \in USERS :
          []<>(AllReplicasCaughtUpMember(gid, u))
          
Liveness_ExpenseGroupAssignmentPropagates ==
    \A eid \in POSSIBLE_EXPENSE_IDs : []<>(AllReplicasAgreeOnExpenseGroup(eid))
    
Liveness == /\ Liveness_ExpenseVersionPropagates
            /\ Liveness_GroupMembershipPropagates
            /\ Liveness_ExpenseGroupAssignmentPropagates

=============================================================================
\* Modification History
\* Last modified Mon Nov 03 10:08:23 CET 2025 by floyd
\* Created Fri Oct 24 11:14:17 CEST 2025 by floyd
