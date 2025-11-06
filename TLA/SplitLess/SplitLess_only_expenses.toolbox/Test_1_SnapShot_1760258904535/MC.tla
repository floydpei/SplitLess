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
const_176025889351879000 == 
{a, b, c}
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_176025889351880000 == 
{eid1, eid2, eid3}
----

\* CONSTANT definitions @modelParameterConstants:2POSSIBLE_SHARES
const_176025889351881000 == 
[USERS -> 1..2]
----

=============================================================================
\* Modification History
\* Created Sun Oct 12 10:48:13 CEST 2025 by floyd
