------------------------------- MODULE Hello -------------------------------
EXTENDS Naturals, TLC

(*
--algorithm HelloWorld
  begin print "Hello, world"
  end algorithm
*)
\* BEGIN TRANSLATION
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT("Hello, world")
         /\ pc' = "Done"

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Fri Feb 13 10:00:32 EST 2015 by nrla
\* Created Wed Feb 11 18:05:23 EST 2015 by nrla
