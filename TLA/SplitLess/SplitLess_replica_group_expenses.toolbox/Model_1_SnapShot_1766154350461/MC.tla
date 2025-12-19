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
a, b
----

\* MV CONSTANT definitions POSSIBLE_REPLICA_IDs
const_1766154345364205000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_1766154345365206000 == 
{gid1}
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_1766154345365207000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions USERS
const_1766154345365208000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:3ASSIGNED_REPLICA
const_1766154345365209000 == 
[u \in USERS |-> IF u = a THEN r1 ELSE IF u = b THEN r2 ELSE r3]
----

\* CONSTANT definitions @modelParameterConstants:5POSSIBLE_SHARES
const_1766154345365210000 == 
[USERS -> 0..1]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1766154345365211000 ==
actionCounter <= 3
----
=============================================================================
\* Modification History
\* Created Fri Dec 19 15:25:45 CET 2025 by floyd
