---- MODULE MC ----
EXTENDS SplitLess_replica_group_expenses, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
gid1
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
const_1765625882766274000 == 
{r1, r2}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_1765625882766275000 == 
{gid1}
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_1765625882766276000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions USERS
const_1765625882766277000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:3ASSIGNED_REPLICA
const_1765625882767278000 == 
[u \in USERS |-> IF u = a THEN r1 ELSE r2]
----

\* CONSTANT definitions @modelParameterConstants:5POSSIBLE_SHARES
const_1765625882767279000 == 
[USERS -> 0..1]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1765625882767280000 ==
actionCounter <= 6
----
=============================================================================
\* Modification History
\* Created Sat Dec 13 12:38:02 CET 2025 by floyd
