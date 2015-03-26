-------------------------------- MODULE test --------------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC



\* add[i, j \in Nat] == i+j
\*add == [i, j \in Nat |-> i+j]

(*
--algorithm test {
  variables x=1;
  
  
   {
    l0:
      print "hello";
      
    l1:
      print "almost done";

   }
 

}

*)

\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 1
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ PrintT("hello")
      /\ pc' = "l1"
      /\ x' = x

l1 == /\ pc = "l1"
      /\ PrintT("almost done")
      /\ pc' = "Done"
      /\ x' = x

Next == l0 \/ l1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



=============================================================================
