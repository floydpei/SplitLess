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
const_1760259700811103000 == 
{a, b, c}
----

\* MV CONSTANT definitions POSSIBLE_EXPENSE_IDs
const_1760259700811104000 == 
{eid1, eid2, eid3}
----

\* CONSTANT definitions @modelParameterConstants:2POSSIBLE_SHARES
const_1760259700811105000 == 
[USERS -> 0..1]
----

=============================================================================
\* Modification History
\* Created Sun Oct 12 11:01:40 CEST 2025 by floyd
