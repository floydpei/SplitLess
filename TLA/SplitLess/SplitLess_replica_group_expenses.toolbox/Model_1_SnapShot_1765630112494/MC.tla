---- MODULE MC ----
EXTENDS SplitLess_replica_group_expenses, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
gid1, gid2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
eid1, eid2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions POSSIBLE_REPLICA_IDs
const_1765626787040325000 == 
{r1, r2}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_1765626787040326000 == 
{gid1, gid2}
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_1765626787040327000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions USERS
const_1765626787040328000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:3ASSIGNED_REPLICA
const_1765626787040329000 == 
[u \in USERS |-> IF u = a THEN r1 ELSE r2]
----

\* CONSTANT definitions @modelParameterConstants:5POSSIBLE_SHARES
const_1765626787040330000 == 
[USERS -> 0..1]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1765626787040331000 ==
actionCounter <= 7
----
=============================================================================
\* Modification History
\* Created Sat Dec 13 12:53:07 CET 2025 by floyd
