-------------------------------- MODULE 2pc --------------------------------

EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC

(* PlusCal options (-termination) *)


(*

--algorithm 2pc {
  variables participants={"A", "B", "C"},
            states=[i\in participants |-> "start"]; \* states can be "start", "prepared" / "failed", "committed" / "aborted"

  process(name="P") {
    p0: print "hello";
  }

}

*)
\* BEGIN TRANSLATION
VARIABLES participants, states, pc

vars == << participants, states, pc >>

Init == (* Global variables *)
        /\ participants = {"a", "b", "c"}
        /\ states = [i\in participants |-> "start"]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT("start")
         /\ pc' = "Done"
         /\ UNCHANGED << participants, states >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Mar 25 08:41:58 CET 2015 by bela
\* Created Wed Mar 25 08:25:16 CET 2015 by bela
