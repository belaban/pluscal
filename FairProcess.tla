---------------------------- MODULE FairProcess ----------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC
CONSTANT ids

(*

--algorithm FairProcess {
  variable x=0;

  process(id=1) {
     p0:
     while(TRUE) {
        with(m \in ids) {
           x := m;
           print x;
        }
     }
  }
}

*)
\* BEGIN TRANSLATION
VARIABLE x

vars == << x >>

ProcSet == {1}

Init == (* Global variables *)
        /\ x = 0

id == \E m \in ids:
        /\ x' = m
        /\ PrintT(x')

Next == id

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Mar 27 11:41:20 CET 2015 by bela
\* Created Fri Mar 27 11:29:52 CET 2015 by bela
