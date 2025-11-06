---- MODULE MC ----
EXTENDS SplitLess_groups_expenses, TLC

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
a, b
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_1761228642551288000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_1761228642551289000 == 
{gid1, gid2}
----

\* MV CONSTANT definitions USERS
const_1761228642551290000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2POSSIBLE_SHARES
const_1761228642551291000 == 
[USERS -> 0..1]
----

\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1761228642551294000 ==
/\ Inv_GroupContainsConsistentEids
----
\* INVARIANT definition @modelCorrectnessInvariants:3
inv_1761228642551295000 ==
/\ Inv_GroupBalanceZero
----
=============================================================================
\* Modification History
\* Created Thu Oct 23 16:10:42 CEST 2025 by floyd
