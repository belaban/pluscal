------------------------------- MODULE Hello -------------------------------

EXTENDS Naturals, TLC, FiniteSets, Sequences


(*
--algorithm HelloWorld {
    variables x = 1..10;
     {
        print <<x, Cardinality(x)>>;
      }
      }
  }
*)
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 1..10
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(<<x, Cardinality(x)>>)
         /\ pc' = "Done"
         /\ x' = x

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Tue Jan 10 14:46:32 CET 2017 by bela
\* Last modified Tue Jan 10 13:26:27 CET 2017 by bela
\* Last modified Fri Feb 13 10:00:32 EST 2015 by nrla
\* Created Wed Feb 11 18:05:23 EST 2015 by nrla
