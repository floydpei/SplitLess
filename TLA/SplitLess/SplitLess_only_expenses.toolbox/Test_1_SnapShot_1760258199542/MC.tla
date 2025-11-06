---- MODULE MC ----
EXTENDS SplitLess_only_expenses, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
eid1, eid2, eid3
----

\* MV CONSTANT definitions USERS
const_176025819751263000 == 
{a, b, c}
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_176025819751264000 == 
{eid1, eid2, eid3}
----

\* CONSTANT definitions @modelParameterConstants:2POSSIBLE_SHARES
const_176025819751265000 == 
[USERS -> 1..2]
----

=============================================================================
\* Modification History
\* Created Sun Oct 12 10:36:37 CEST 2025 by floyd
