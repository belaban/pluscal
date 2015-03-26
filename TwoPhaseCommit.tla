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
\* Last modified Thu Mar 26 16:59:43 CET 2015 by bela
\* Created Wed Mar 25 08:25:16 CET 2015 by bela
