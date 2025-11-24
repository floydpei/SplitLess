--------------------- MODULE SplitLess_group_join_leave ---------------------
EXTENDS Naturals

CONSTANTS
    USERS,
    POSSIBLE_REPLICA_IDs,
    ASSIGNED_REPLICA,
    INITIAL_MEMBER
    
VARIABLES
    replicas, actionCounter
    
\* ----------------------------
\* Records
\* ----------------------------
Group == [  members : [USERS -> Nat],
            persumed_members : [USERS -> Nat] ]
            
Replica == [id: POSSIBLE_REPLICA_IDs,
            group: Group]
            
            
\* ----------------------------
\* Initialization
\* ---------------------------
Init ==  
        /\ LET InitialGroup == 
            [members |-> [u \in USERS |-> 0],
             persumed_members |-> [u \in USERS |-> IF u = INITIAL_MEMBER THEN 1 ELSE 0]] 
           IN /\ replicas = [rid \in POSSIBLE_REPLICA_IDs |-> [group |-> InitialGroup] ]
        
        \*replicas = [rid \in POSSIBLE_REPLICA_IDs
          \*               |-> [id |-> rid,
            \*             group |-> INITIAL_GROUP] ]
        /\ actionCounter = 0
        
        
\* ----------------------------
\* Helper Actions
\* ---------------------------    
IsMember(memberCounter) ==
  memberCounter % 2 = 1
  
IsMemberContender(memberCounter) ==
    memberCounter % 2 = 1

        

\* ----------------------------
\* Group Actions
\* ---------------------------
InviteMember ==
    \E actor, newMember \in USERS :
    \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ IsMember(replicas[rid].group.members[actor])
        /\ ~IsMember(replicas[rid].group.members[newMember])
        /\ ~IsMemberContender(replicas[rid].group.persumed_members[newMember])
        /\ LET newReplica ==
            [replicas[rid] EXCEPT !.group.persumed_members[newMember] = @ + 1]
            IN
                /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
                /\ actionCounter' = actionCounter + 1

AcceptInvitation ==
    \E actor \in USERS :
    \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ IsMemberContender(replicas[rid].group.persumed_members[actor])
        /\ LET newReplica ==
            [replicas[rid] EXCEPT 
                !.group.persumed_members[actor] = @ + 1,
                !.group.members[actor] = @ + 1 ]
            IN
                /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
                /\ actionCounter' = actionCounter + 1
                
LeaveGroup ==
    \E actor \in USERS :
    \E rid \in POSSIBLE_REPLICA_IDs :
        /\ ASSIGNED_REPLICA[actor] = rid
        /\ IsMember(replicas[rid].group.members[actor])
        /\ LET newReplica ==
            [replicas[rid] EXCEPT !.group.members[actor] = @ + 1 ]
            IN
                /\ replicas' = [replicas EXCEPT ![rid] = newReplica]
                /\ actionCounter' = actionCounter + 1
                
                
                
\* ----------------------------
\* Merge action 
\* ----------------------------
MergeReplicas ==
    \E ownRid, otherRid \in POSSIBLE_REPLICA_IDs:
        /\ ownRid # otherRid
        /\ LET 
            merged_members ==
                [u \in USERS |-> CHOOSE n \in {replicas[ownRid].group.members[u], replicas[otherRid].group.members[u]} :
                                            n >= replicas[ownRid].group.members[u] /\ n >= replicas[otherRid].group.members[u] ]
            merged_persumed_membrs ==
                [u \in USERS |-> CHOOSE n \in {replicas[ownRid].group.persumed_members[u], replicas[otherRid].group.persumed_members[u]} :
                                            n >= replicas[ownRid].group.persumed_members[u] /\ n >= replicas[otherRid].group.persumed_members[u] ]
            merged_group ==
                [replicas[ownRid].group EXCEPT !.members = merged_members,
                                               !.persumed_members = merged_persumed_membrs]                                
           IN /\ replicas' = [replicas EXCEPT ![ownRid].group = merged_group]
              /\ UNCHANGED actionCounter
                                            
            
\* ----------------------------
\* Next relation
\* ----------------------------
Next == 
    \/ InviteMember
    \/ AcceptInvitation
    \/ LeaveGroup
    \/ MergeReplicas
    \/ UNCHANGED <<replicas, actionCounter>>
    
    
\* ----------------------------
\* Invariants
\* ----------------------------
TypeOK ==
  \A rid \in POSSIBLE_REPLICA_IDs :
    /\ replicas[rid].group
         \in Group

\* ----------------------------
\* Liveness Helper
\* ----------------------------
AllReplicasHaveAtLeastGroupMemberCounter(user, member_counter) ==
    \A rid \in POSSIBLE_REPLICA_IDs :
        /\ replicas[rid].group.members[user] >= member_counter
        
AllReplicasHaveAtLeastGroupPersumedMemberCounter(user, persumend_member_counter) ==
    \A rid \in POSSIBLE_REPLICA_IDs :
        /\ replicas[rid].group.persumed_members[user] >= persumend_member_counter
        
\* ----------------------------
\* Liveness
\* ----------------------------
Liveness_GroupMemberShipPropagates ==
    \A rid \in POSSIBLE_REPLICA_IDs :
        \A user \in USERS:
                []<> AllReplicasHaveAtLeastGroupMemberCounter(user, replicas[rid].group.members[user])
                
Liveness_PersumedGroupMemberShipPropagates ==
    \A rid \in POSSIBLE_REPLICA_IDs :
        \A user \in USERS:
                []<> AllReplicasHaveAtLeastGroupPersumedMemberCounter(user, replicas[rid].group.persumed_members[user])


\*-----------------------------
\* Safety Helper
\*-----------------------------
MemberOnlyAfterInvitation ==
  \A rid \in POSSIBLE_REPLICA_IDs :
  \A u \in USERS :
    /\ ASSIGNED_REPLICA[u] = rid
    /\ ~IsMember(replicas[rid].group.members[u])
    /\ IsMember(replicas'[rid].group.members[u])
    =>
      /\ IsMemberContender(replicas[rid].group.persumed_members[u])
      
NoDecreaseMembershipCounters ==
  \A rid \in POSSIBLE_REPLICA_IDs :
  \A u \in USERS :
       replicas'[rid].group.members[u] 
          >= replicas[rid].group.members[u]
    /\ replicas'[rid].group.persumed_members[u] 
          >= replicas[rid].group.persumed_members[u]

\*-----------------------------
\* Safety
\*-----------------------------
Safety_MemberOnlyAfterInvitation ==
  [] [ MemberOnlyAfterInvitation ]_<<replicas, actionCounter>>
  
Safety_NoDecreaseMembershipCounters ==
  [] [ NoDecreaseMembershipCounters ]_<<replicas, actionCounter>>

    
\* ----------------------------
\* Specification
\* ----------------------------  
Spec == Init /\ [][Next]_<<replicas, actionCounter>> 
FairSpec == Spec /\ WF_<<replicas, actionCounter>>(MergeReplicas)

=============================================================================
\* Modification History
\* Last modified Mon Nov 24 12:25:07 CET 2025 by floyd
\* Created Mon Nov 24 10:30:46 CET 2025 by floyd
