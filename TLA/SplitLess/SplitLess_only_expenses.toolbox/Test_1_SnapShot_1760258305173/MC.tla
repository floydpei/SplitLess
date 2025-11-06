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
const_176025830314367000 == 
{a, b, c}
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_176025830314368000 == 
{eid1, eid2, eid3}
----

\* CONSTANT definitions @modelParameterConstants:2POSSIBLE_SHARES
const_176025830314369000 == 
[USERS -> 1..2]
----

=============================================================================
\* Modification History
\* Created Sun Oct 12 10:38:23 CEST 2025 by floyd
