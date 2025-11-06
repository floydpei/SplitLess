---------------------- MODULE SplitLess_only_expenses ----------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS USERS, POSSIBLE_SHARES, POSSIBLE_EXPENSE_IDs, NO_EXPENSE

VARIABLES  recordedExpenses
          
          
Expense == [id : POSSIBLE_EXPENSE_IDs, creator : USERS, amount : Nat, shares : POSSIBLE_SHARES, deleted : BOOLEAN]

\* ----------------------------
\* Initialization
\* ----------------------------
Init ==
    /\ recordedExpenses = [ id \in POSSIBLE_EXPENSE_IDs |-> NO_EXPENSE ]
        
\* ----------------------------
\* Helper functions
\* ----------------------------

RECURSIVE SumFunction(_)
SumFunction(F) ==
  IF DOMAIN F = {}
  THEN 0
  ELSE LET d == CHOOSE x \in DOMAIN F: TRUE
       IN  F[d] + SumFunction([y \in DOMAIN F \ {d} |-> F[y]])


\* ----------------------------
\* Expense Operations
\* ----------------------------

AddExpense  ==
       \E actor \in USERS : 
       \E shares \in POSSIBLE_SHARES :
       \*\E deleted \in BOOLEAN : 
       \E eid \in POSSIBLE_EXPENSE_IDs  : 
        \*/\ eid \notin DOMAIN recordedExpenses
        /\ recordedExpenses[eid] = NO_EXPENSE
        /\ LET newExpense == [ id |-> eid, creator |-> actor, amount |-> SumFunction(shares), shares |-> shares, deleted |-> FALSE ]
           IN recordedExpenses' = [ recordedExpenses EXCEPT ![eid] = newExpense]
           
           
DeleteExpense ==
    \E actor \in USERS :
    \E eid \in POSSIBLE_EXPENSE_IDs :
        /\ recordedExpenses[eid] # NO_EXPENSE
        /\ recordedExpenses[eid].creator = actor
        /\ recordedExpenses[eid].deleted = FALSE
        /\ recordedExpenses' = [ recordedExpenses EXCEPT ![eid].deleted = TRUE ]


ModifyExpense ==
    \E actor \in USERS :
    \E eid \in POSSIBLE_EXPENSE_IDs :
    \E shares \in POSSIBLE_SHARES :
        /\ recordedExpenses[eid] # NO_EXPENSE
        /\ recordedExpenses[eid].creator = actor
        /\ recordedExpenses[eid].deleted = FALSE
        /\ recordedExpenses' = [ recordedExpenses EXCEPT ![eid].shares = shares]
        /\ recordedExpenses' = [ recordedExpenses EXCEPT ![eid].amount = SumFunction(shares)]
            
        
        

(**
DeleteExpense(actor, expenseID) ==
    /\ actor \in USERS
    /\ \E e \in recordedExpenses : e.id = expenseID /\ e.creator = actor /\ e.deleted = "false"
    /\ LET oldExpense == CHOOSE e \in recordedExpenses : e.id = expenseID
           newExpense == [oldExpense EXCEPT !.deleted = "true"]
       IN recordedExpenses' = (recordedExpenses \ {oldExpense}) \cup {newExpense}
    /\ UNCHANGED <<>>
    
ModifyExpense(actor, expenseID, newTotal, newSharesOfParticipants) ==
    /\ actor \in USERS
    /\ newTotal > 0
    /\ \E e \in recordedExpenses : e.id = expenseID /\ e.creator = actor /\ e.deleted = "false"
    /\ LET oldExpense == CHOOSE e \in recordedExpenses : e.id = expenseID
           newExpense == [oldExpense EXCEPT !.amount = newTotal, !.shares = newSharesOfParticipants]
       IN recordedExpenses' = (recordedExpenses \ {oldExpense}) \cup {newExpense}
    /\ UNCHANGED <<>>
       **)
       
       
\* ----------------------------
\* Next Relation
\* ----------------------------

Next ==
    \/ AddExpense
    \/ DeleteExpense
    \/ ModifyExpense
                
  
    \/ UNCHANGED <<recordedExpenses>>
            
\* ----------------------------
\* Specification
\* ----------------------------

Spec == Init /\ [][Next]_<<recordedExpenses>>

\* ----------------------------
\* Invariants
\* ----------------------------

TypeOK ==
    /\ recordedExpenses \in [POSSIBLE_EXPENSE_IDs -> (Expense \cup {NO_EXPENSE})]
  \*/\ recordedExpenses \in [POSSIBLE_EXPENSE_IDs -> Expense] \cup {}
        
        
Inv_Conservertaion_of_amount == \A id \in DOMAIN recordedExpenses :
                                    LET e == recordedExpenses[id]
                                    IN e.amount = SumFunction(e.shares)


    
Inv == TypeOK
=============================================================================
\* Modification History
\* Last modified Sun Oct 12 10:46:02 CEST 2025 by floyd
\* Last modified Fri Oct 10 13:19:33 CEST 2025 by floydpeiszan
\* Created Sun Oct 05 13:08:13 CEST 2025 by floyd