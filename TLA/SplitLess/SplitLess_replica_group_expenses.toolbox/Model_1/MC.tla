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
const_176683211577453000 == 
{r1, r2, r3}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_176683211577454000 == 
{gid1}
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_176683211577455000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions USERS
const_176683211577456000 == 
{a, b, c}
----

\* CONSTANT definitions @modelParameterConstants:3ASSIGNED_REPLICA
const_176683211577457000 == 
[u \in USERS |-> IF u = a THEN r1 ELSE IF u = b THEN r2 ELSE r3]
----

\* CONSTANT definitions @modelParameterConstants:5POSSIBLE_SHARES
const_176683211577458000 == 
[USERS -> 0..1]
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_176683211577459000 ==
actionCounter <= 7
----
=============================================================================
\* Modification History
\* Created Sat Dec 27 11:41:55 CET 2025 by lavoie
