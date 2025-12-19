---- MODULE MC ----
EXTENDS SplitLess_replica_group_expenses, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
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
a, b, c
----

\* MV CONSTANT definitions POSSIBLE_REPLICA_IDs
const_1766154094593137000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_1766154094593138000 == 
{gid1}
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_1766154094593139000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions USERS
const_1766154094593140000 == 
{a, b, c}
----

\* CONSTANT definitions @modelParameterConstants:3ASSIGNED_REPLICA
const_1766154094593141000 == 
[u \in USERS |-> IF u = a THEN r1 ELSE IF u = b THEN r2 ELSE r3]
----

\* CONSTANT definitions @modelParameterConstants:5POSSIBLE_SHARES
const_1766154094593142000 == 
[USERS -> 0..1]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1766154094593143000 ==
actionCounter <= 3
----
=============================================================================
\* Modification History
\* Created Fri Dec 19 15:21:34 CET 2025 by floyd
