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
const_17621607423942000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_17621607423943000 == 
{gid1, gid2}
----

\* MV CONSTANT definitions POSSIBLE_REPLICA_IDs
const_17621607423944000 == 
{r1, r2}
----

\* MV CONSTANT definitions USERS
const_17621607423945000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2POSSIBLE_SHARES
const_17621607423946000 == 
[USERS -> 0..1]
----

\* CONSTANT definitions @modelParameterConstants:7ASSIGNED_REPLICA
const_17621607423947000 == 
[ u \in USERS |-> IF u = a THEN r1 ELSE r2]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_17621607423948000 ==
actionCounter <= 4
----
=============================================================================
\* Modification History
\* Created Mon Nov 03 10:05:42 CET 2025 by floyd
