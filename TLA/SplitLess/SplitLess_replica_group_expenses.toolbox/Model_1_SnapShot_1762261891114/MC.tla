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
const_17622618868452000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_17622618868453000 == 
{gid1, gid2}
----

\* MV CONSTANT definitions POSSIBLE_REPLICA_IDs
const_17622618868454000 == 
{r1, r2}
----

\* MV CONSTANT definitions USERS
const_17622618868455000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2POSSIBLE_SHARES
const_17622618868456000 == 
[USERS -> 0..1]
----

\* CONSTANT definitions @modelParameterConstants:7ASSIGNED_REPLICA
const_17622618868457000 == 
[ u \in USERS |-> IF u = a THEN r1 ELSE r2]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_17622618868458000 ==
actionCounter <= 7
----
=============================================================================
\* Modification History
\* Created Tue Nov 04 14:11:26 CET 2025 by floyd
