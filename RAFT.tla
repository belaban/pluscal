-------------------------------- MODULE RAFT --------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* global constants, variables*)
CONSTANTS Replica
ASSUME Replica = {1,2,3}
CONSTANTS Value
CONSTANTS Follower, Candidate, Leader
CONSTANTS Nil
CONSTANTS RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse
VARIABLE messages                                                                \* messages is BAG(Message)
VARIABLE elections                                                               \* elections is SET(Election)
VARIABLE allLogs                                                                 \* allLogs is SUBSET Seq(LogEntry) - some set of LogEntry sequences
-----------------------------------------------------------
(* per server variables*)

VARIABLE currentTerm                                                             \* currentTerm \in [Replicas -> Nat]
VARIABLE state                                                                   \* state \in [Replicas -> {Leader, Follower, Candidate}]
VARIABLE votedFor                                                                \* votedFor \in [Replicas -> Replicas \cup {Nil}]  
replicaVars == <<currentTerm, state, votedFor>>

VARIABLE log                                                                     \* log \in [Replicas -> Sequence]
VARIABLE commitIndex                                                             \* commitIndex \in [Replicas -> Nat]
logVars == <<log, commitIndex>>

VARIABLE votesResponded                                                          \* votesResponded \in [Replicas -> SUBSET Replicas] 
VARIABLE votesGranted                                                            \* votesGranted \in [Replicas -> SUBSET Replicas]
VARIABLE voterLog                                                                \* voterLog \in [Replicas -> Seq(Replicas)] 
candidateVars == <<votesResponded, votesGranted, voterLog>>

VARIABLE nextIndex                                                               \* nextIndex \in [Replicas -> Nat]
VARIABLE lastAgreeIndex                                                          \* lastAgreeIndex \in [Replicas -> Nat]
leaderVars == <<nextIndex, lastAgreeIndex, elections>>
---------------------------------------------------------------
vars == <<messages, replicaVars, candidateVars, leaderVars, logVars>>
---------------------------------------------------------------
(* helpers *)

Quorum == {i \in SUBSET Replica : Cardinality(i)*2 > Cardinality(Replica)} 
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

WithMessage(m, msgs) == IF m \in DOMAIN msgs THEN [msgs EXCEPT ![m] = msgs[m]+1] ELSE msgs @@ (m :> 1)
WithoutMessage(m, msgs) == IF m \in DOMAIN msgs THEN [msgs EXCEPT ![m] = msgs[m]-1] ELSE msgs

(* add a message m to the bag of messages *)
Send(m) == messages' = WithMessage(m, messages)
Discard(m) == messages' = WithoutMessage(m, messages)

(* add a message response to the bag, then remove a message request *)
Reply(response, request) == messages' = WithoutMessage(request, WithMessage(response, messages))

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
------------------------------------------------------------------
(* initialization for all variables *)

InitHistoryVars == /\ elections = {}
                   /\ allLogs = {}
                   /\ voterLog = [i \in Replica |-> [j \in {} |-> <<>>]]
              
InitReplicaVars == /\ currentTerm = [i \in Replica |-> 1]
                   /\ state = [i \in Replica |-> Follower]
                   /\ votedFor = [i\in Replica |-> Nil]
                   
InitCandidateVars == /\ votesResponded = [i \in Replica |-> {}]
                     /\ votesGranted = [i \in Replica |-> {}]                   
                   
InitLeaderVars == /\ nextIndex = [i \in Replica |-> [j \in Replica |-> 1]]
                  /\ lastAgreeIndex = [i \in Replica |-> [j \in Replica |-> 0]]
                  
InitLogVars == /\ log = [i \in Replica |-> <<>>]
               /\ commitIndex = [i \in Replica |-> 0]

Init == /\ messages = [m \in {} |-> 0]                      
        /\ InitHistoryVars 
        /\ InitReplicaVars 
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars        
--------------------------------------------------------------------
(* actions *)

(* duplicate an existing message in the bag of messages - should this not be CHOOSE instead of \E ?? *)
DuplicateMessage == /\ \E m \in DOMAIN messages : Send(m)
                    /\ UNCHANGED <<replicaVars, candidateVars, leaderVars, logVars>>

(* drop a message from the bag of messages *)
DropMessage == /\ \E m \in DOMAIN messages : Discard(m)
               /\ UNCHANGED <<replicaVars, candidateVars, leaderVars, logVars>>
          
(* replica i times out - increment term and reset voting variables *)               
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i]+1]
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]               
              /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]               
              /\ voterLog' = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]] 
              /\ UNCHANGED <<messages, leaderVars, logVars>>              

Restart(i) == /\ state' = [state EXCEPT ![i] = Follower]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]               
              /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]               
              /\ voterLog' = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]] 
              /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Replica |-> 1]]
              /\ lastAgreeIndex' = [lastAgreeIndex EXCEPT ![i] = [j \in Replica |-> 0]]
              /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections>>              
                       
 (* use a LET .. IN to separate out the message construction *)                      
RequestVote(i,j) == /\ state[i] = Candidate
                    /\ j \notin votesResponded[i]
                    /\ Send([mtype |-> RequestVoteRequest,
                             mterm |-> currentTerm[i],
                             mlastLogTerm |-> LastTerm(log[i]),
                             mlastLogIndex |-> Len(log[i]),
                             msource |-> i,
                             mdest |-> j])
                    /\ UNCHANGED <<replicaVars, candidateVars, leaderVars, logVars>>                       

AppendEntries(i,j) == /\ (i # j)
                      /\ state[i] = Leader
                      /\ LET prevLogIndex == nextIndex[i][j] - 1
                             prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
                             lastEntry == Min({Len(log[i]), nextIndex[i][j]+1})
                             (* has to add this to account for upper *)
                             upper == 10
                             entries == SubSeq(log[i], nextIndex[i][j], upper)
                         IN Send([mtype |-> AppendEntriesRequest,
                                  mterm |-> currentTerm[i],
                                  mprevLogIndex |-> prevLogIndex,
                                  mprevLogTerm |-> prevLogTerm,
                                  mentries |-> entries,
                                  mcommitIndex |-> Min({commitIndex[i], lastEntry}),
                                  msource |-> i,
                                  mdest |-> j])
                       /\ UNCHANGED <<replicaVars, candidateVars, leaderVars, logVars>>
 
(* on becoming leader, update nextIndex and lastAgreeIndex and record election in hstory variable *)                   
BecomeLeader(i) == /\ state[i] = Candidate 
                   /\ votesGranted[i] \in Quorum
                   /\ state' = [state EXCEPT ![i] = Leader]
                   /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Replica |-> Len(log[i])+1]]
                   /\ lastAgreeIndex' = [lastAgreeIndex EXCEPT ![i] = [j \in Replica |-> 0]]
                   /\ elections' = elections \cup {[eterm |-> currentTerm[i],
                                                    eleader |-> i,
                                                    elog |-> log[i],
                                                    evotes |-> votesGranted[i],
                                                    evoterLog |-> voterLog[i]]}
                   /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>> 
                   
(* update the leader's log with the new entry *)
\* NB: newIndex not used                   
ClientRequest(i,v) == /\ state[i] = Leader
                      /\ LET entry == [term |-> currentTerm[i], value |-> v]
                             newIndex == Len(log[i]) + 1
                             newLog == Append(log[i], entry)
                         IN log' = [log EXCEPT ![i] = newLog]
                      /\ UNCHANGED <<messages, replicaVars, candidateVars, leaderVars, commitIndex>>                   
 -------------------------------------------------------------------
 (* message handlers *)
HandleRequestVoteRequest(i,j,m) == 
         LET logIsCurrent == \/ m.mlastLogTerm > LastTerm(log[i])
                             \/ (/\ m.mlastLogTerm = LastTerm(log[i])
                                 /\ m.mlastLogIndex >= Len(log[i]))
             grant == /\ m.mterm = currentTerm[i]
                      /\ logIsCurrent 
                      /\ votedFor[i] \in {Nil, j}                      
         IN /\ m.mterm <= currentTerm[i]
            /\ \/ grant /\ votedFor' = [votedFor EXCEPT ![i] = j]
               \/ \neg grant /\ UNCHANGED votedFor
            /\ Reply([mtype |-> RequestVoteResponse,
                      mterm |-> currentTerm[i],
                      mvoteGranted |-> grant,
                      mlog |-> log[i],  
                      msource |-> i,
                      mdest |-> j],
                      m)
            /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>
             
HandleRequestVoteResponse(i,j,m) ==
         /\ m.mterm = currentTerm[i]
         /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {j}]
         /\ \/ m.mvoteGranted /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {j}]
                              /\ voterLog' = [voterLog EXCEPT ![i][j] = m.mlog]
            \/ \neg m.mvotesGranted /\ UNCHANGED <<votesGranted, voterLog>>
         /\ Discard(m)
         /\ UNCHANGED <<replicaVars, votedFor, leaderVars, logVars>>

HandleAppendEntriesRequest(i,j,m) == 
         LET accept == /\ m.mterm = currentTerm[i]
                       /\ \/ m.mprevLogIndex = 0
                          \/ /\ m.mprevLogIndex > 0
                             /\ m.mprevLogIndex <= Len(log[i])
                             /\ m.mprevLogTerm = log[i][m.prevLogIndex].term
         IN /\ m.mterm <= currentTerm[i]
            /\ \/ \* reject request
                  /\ \neg accept
                  /\ Reply([mtype |-> AppendEntriesResponse,
                            mterm |-> currentTerm[i],
                            mlastAgreeIndex |-> 0,
                            msource |-> i,
                            mdest |-> j],
                            m)
                  /\ UNCHANGED <<replicaVars, candidateVars, leaderVars, logVars>>
               \/ /\ accept 
                  /\ LET index == m.mPrevLogIndex + 1
                     IN \/ \* already done with request
                           /\ \/ m.mentries = <<>>
                              \/ /\ Len(log[i]) >= index
                                 /\ log[i][index].term = m.mentries[1].term
                           /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
                           /\ Reply([mtype |-> AppendEntriesResponse,
                                     mterm |-> currentTerm[i],
                                     mlastAgreeIndex |-> m.mprevLogIndex + Len(m.mentries),
                                     msource |-> i,
                                     mdest |-> j],
                                     m)
                           /\ UNCHANGED <<logVars>> 
                        \/ \* conflict remove one entry
                          /\ m.mentries # <<>>
                          /\ Len(log[i]) >= index
                          /\ log[i][index].term # m.mentries[1].term
                          /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |-> log[i][index2]]
                             IN  log' = [log EXCEPT ![i] = new]
                          /\ UNCHANGED <<commitIndex, messages>>
                        \/ \* no conflict add entry
                          /\ m.mentries # <<>>
                          /\ Len(log[i]) = m.mprevLogIndex
                          /\ log' = [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
                          /\ UNCHANGED <<commitIndex, messages>>
            /\ UNCHANGED <<replicaVars, candidateVars, leaderVars>>
            
HandleAppendEntriesResponse(i,j,m) == 
          /\ m.mterm = currentTerm[i]
          /\ \/ /\ m.mlastAgreeIndex > 0
                /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.mlastAgreeIndex + 1]
                /\ lastAgreeIndex' = [lastAgreeIndex EXCEPT ![i][j] = m.mlastAgreeIndex]
                /\ LET Agree(index) == {i} \cup {k \in Replica : lastAgreeIndex'[i][k] >= index}
                       agreeIndexes == {index \in 1..Len(log[i]) : Agree(index) \in Quorum}
                       newCommitIndex == IF /\ agreeIndexes # {}
                                            /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
                                         THEN
                                            Max(agreeIndexes)
                                         ELSE
                                            commitIndex[i]
                   IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
             \/ /\ m.mlastAgreeIndex = 0
                /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
                /\ UNCHANGED <<replicaVars, candidateVars, log, elections>>
          /\ Discard(m)
          /\ UNCHANGED <<replicaVars, candidateVars, leaderVars, logVars>>
          
UpdateTerm(i,j,m) == /\ m.mterm > currentTerm[i]
                     /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
                     /\ state' = [state EXCEPT ![i] = Follower]
                     /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                     \* messages is unchanges so m can be processed further
                     /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>
  
DropStaleResponse(i,j,m) == /\ m.mterm < currentTerm[i]
                            /\ Discard(m)
                            /\ UNCHANGED <<replicaVars, candidateVars, leaderVars, logVars>>

(* receive a message *)
Receive == \E m \in DOMAIN messages : 
             LET i == m.mdest 
                 j == m.msource
             IN \* any RPC with a newer term causes the recipient to advance its term first
                 \/ UpdateTerm(i,j,m)
                 \/ m.mtype = RequestVoteRequest /\ HandleRequestVoteRequest(i,j,m)
                 \/ m.mtype = RequestVoteResponse /\ \/ DropStaleResponse(i,j,m)
                                                     \/ HandleRequestVoteRequest(i,j,m)
                 \/ m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i,j,m)
                 \/ m.mtype = AppendEntriesResponse /\ \/ DropStaleResponse(i,j,m)
                                                       \/ HandleAppendEntriesRequest(i,j,m)
                           
---------------------------------------------------------------------------------
Next == /\ \/ DuplicateMessage
           \/ DropMessage
           \/ Receive
           \/ \E i \in Replica : Timeout(i)
           \/ \E i \in Replica : Restart(i)
           \/ \E i \in Replica : BecomeLeader(i)
           \/ \E i \in Replica, v \in Value : ClientRequest(i,v)
           \/ \E i,j \in Replica : RequestVote(i,j)
           \/ \E i,j \in Replica : AppendEntries(i,j)
           \* history variable that tracks every log instance
        /\ allLogs' = allLogs \cup {\A i \in Replica: log[i]}
              
\* the specification must start with the initial state and transition according to Next              
Spec == Init /\ [][Next]_vars   
                        
=============================================================================
\* Modification History
\* Last modified Fri Feb 27 14:13:30 EST 2015 by nrla
\* Created Fri Feb 27 08:15:46 EST 2015 by nrla
