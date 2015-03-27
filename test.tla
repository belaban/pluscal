-------------------------------- MODULE test --------------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC





Remove(i,seq) == [ j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

tail(seq) == [i \in 1..Len(seq)-1 |-> seq[i+1]]


\* add[i, j \in Nat] == i+j
\*add == [i, j \in Nat |-> i+j]

(*
--algorithm test {
  variable seq = <<10,11,12,13,14,15>>;
  
  
   {
     print <<seq, tail(seq)>>;
   
   }
 

}

*)

\* BEGIN TRANSLATION
VARIABLES seq, pc

vars == << seq, pc >>

Init == (* Global variables *)
        /\ seq = <<10,11,12,13,14,15>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(<<seq, tail(seq)>>)
         /\ pc' = "Done"
         /\ seq' = seq

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



=============================================================================
