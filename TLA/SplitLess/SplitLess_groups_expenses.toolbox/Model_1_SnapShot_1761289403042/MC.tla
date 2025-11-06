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
const_176128938000318000 == 
{eid1, eid2}
----

\* MV CONSTANT definitions POSSIBLE_GROUP_IDs
const_176128938000319000 == 
{gid1, gid2}
----

\* MV CONSTANT definitions USERS
const_176128938000320000 == 
{a, b}
----

\* CONSTANT definitions @modelParameterConstants:2POSSIBLE_SHARES
const_176128938000321000 == 
[USERS -> 0..1]
----

\* INVARIANT definition @modelCorrectnessInvariants:2
inv_176128938000324000 ==
/\ Inv_GroupContainsConsistentEids
----
\* INVARIANT definition @modelCorrectnessInvariants:3
inv_176128938000325000 ==
/\ Inv_GroupBalanceZero
----
=============================================================================
\* Modification History
\* Created Fri Oct 24 09:03:00 CEST 2025 by floyd
