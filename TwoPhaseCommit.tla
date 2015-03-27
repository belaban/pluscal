-------------------------------- MODULE TwoPhaseCommit --------------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC

allInState(parts, states, state) == \A i \in parts: states[i] \in state
anyInState(parts, states, state) == \E i \in parts: states[i] \in state



(*

--fair algorithm TwoPhaseCommit {
  variables participants={"A", "B", "C"},
            valid_states={"started", "proposed", "prepared", "failed", "committed", "aborted"},
            states=[i \in participants |-> "started"]; \* in valid_states
            
  macro setAllTo(state) {
     states := [i \in participants |-> state]
  }
  
       
  process(participant \in participants) {
     p0:
     while(TRUE) {
        await states[self]="proposed";
        \* Randomly reply either with "prepared" or "failed"
        either {
           states[self] := "prepared";
        }
        or {
          states[self] := "failed";
        }
     }
  }
  
  
  process(leader="L") {
     l0:
     while(TRUE) {
        l1:
        if(allInState(participants,states, {"started", "committed", "aborted"})) {
           if(allInState(participants,states, {"committed"}))
              print <<"all committed", states>>;
           setAllTo("proposed");
        }
        else if(anyInState(participants, states, {"failed"})) {
           setAllTo("aborted");
        }
        else if(allInState(participants, states, {"prepared"})) {
           print <<"all prepared", states>>;
           setAllTo("committed");
        }
        \* skip proposed state
     }
  }

 
}

*)




\* BEGIN TRANSLATION
VARIABLES participants, valid_states, states, pc

vars == << participants, valid_states, states, pc >>

ProcSet == (participants) \cup {"L"}

Init == (* Global variables *)
        /\ participants = {"A", "B", "C"}
        /\ valid_states = {"started", "proposed", "prepared", "failed", "committed", "aborted"}
        /\ states = [i \in participants |-> "started"]
        /\ pc = [self \in ProcSet |-> CASE self \in participants -> "p0"
                                        [] self = "L" -> "l0"]

p0(self) == /\ pc[self] = "p0"
            /\ states[self]="proposed"
            /\ \/ /\ states' = [states EXCEPT ![self] = "prepared"]
               \/ /\ states' = [states EXCEPT ![self] = "failed"]
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << participants, valid_states >>

participant(self) == p0(self)

l0 == /\ pc["L"] = "l0"
      /\ pc' = [pc EXCEPT !["L"] = "l1"]
      /\ UNCHANGED << participants, valid_states, states >>

l1 == /\ pc["L"] = "l1"
      /\ IF allInState(participants,states, {"started", "committed", "aborted"})
            THEN /\ IF allInState(participants,states, {"committed"})
                       THEN /\ PrintT(<<"all committed", states>>)
                       ELSE /\ TRUE
                 /\ states' = [i \in participants |-> "proposed"]
            ELSE /\ IF anyInState(participants, states, {"failed"})
                       THEN /\ states' = [i \in participants |-> "aborted"]
                       ELSE /\ IF allInState(participants, states, {"prepared"})
                                  THEN /\ PrintT(<<"all prepared", states>>)
                                       /\ states' = [i \in participants |-> "committed"]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED states
      /\ pc' = [pc EXCEPT !["L"] = "l0"]
      /\ UNCHANGED << participants, valid_states >>

leader == l0 \/ l1

Next == leader
           \/ (\E self \in participants: participant(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION



\* Invariants
ValidStates == \A i \in participants: states[i] \in valid_states


\* Properties
all(state) == \A i \in participants: states[i] = state

AllPrepared  == all("prepared")
AllCommitted == all("committed")
AllAborted   == all("aborted")

\* If all participants are in prepared state, then all of them have to eventually commit
\* IfPrepareThenCommit == [](AllPrepared => <> AllCommitted)
IfPrepareThenCommit == AllPrepared ~> AllCommitted


\* all participants have either all committed or all aborted states
EventuallyCommittedOrAborted ==  <>(AllCommitted \/ AllAborted)


=============================================================================
\* Modification History
\* Last modified Thu Mar 26 18:28:21 CET 2015 by bela
\* Created Wed Mar 25 08:25:16 CET 2015 by bela
