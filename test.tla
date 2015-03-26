-------------------------------- MODULE test --------------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC




(*
--algorithm test {
     variable members={"A", "B", "C"},
              states=[i \in members |-> "started"];
  
  
 
  {
   print states;
    
   
    
  }
 
 

}

*)

\* BEGIN TRANSLATION
VARIABLES members, states, pc

vars == << members, states, pc >>

Init == (* Global variables *)
        /\ members = {"A", "B", "C"}
        /\ states = [i \in members |-> "started"]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(states)
         /\ pc' = "Done"
         /\ UNCHANGED << members, states >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

setState(mbrs, st, state) == \A i \in mbrs: st[i] = state

\* END TRANSLATION



=============================================================================
