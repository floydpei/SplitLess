---- MODULE MC ----
EXTENDS SplitLess_replica_group_expenses, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
eid1, eid2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
gid1, gid2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_176216202878824000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_176216202878925000 == 
{gid1, gid2}
----

\* MV CONSTANT definitions POSSIBLE_REPLICA_IDs
const_176216202878926000 == 
{r1, r2}
----

\* MV CONSTANT definitions USERS
const_176216202878927000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2POSSIBLE_SHARES
const_176216202878928000 == 
[USERS -> 0..1]
----

\* CONSTANT definitions @modelParameterConstants:7ASSIGNED_REPLICA
const_176216202878929000 == 
[ u \in USERS |-> IF u = a THEN r1 ELSE r2]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_176216202878930000 ==
actionCounter <= 7
----
=============================================================================
\* Modification History
\* Created Mon Nov 03 10:27:08 CET 2025 by floyd
