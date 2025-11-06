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
const_176226203078813000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_176226203078814000 == 
{gid1, gid2}
----

\* MV CONSTANT definitions POSSIBLE_REPLICA_IDs
const_176226203078815000 == 
{r1, r2}
----

\* MV CONSTANT definitions USERS
const_176226203078816000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2POSSIBLE_SHARES
const_176226203078817000 == 
[USERS -> 0..1]
----

\* CONSTANT definitions @modelParameterConstants:7ASSIGNED_REPLICA
const_176226203078818000 == 
[ u \in USERS |-> IF u = a THEN r1 ELSE r2]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_176226203078819000 ==
actionCounter <= 7
----
=============================================================================
\* Modification History
\* Created Tue Nov 04 14:13:50 CET 2025 by floyd
