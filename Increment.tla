------------------------------- MODULE Increment -------------------------------
EXTENDS Naturals, TLC
CONSTANT N
ASSUME N \in Nat \{0}

Procs == 1..N


\* N processes all increment a shared variable x by (1) reading it, assigning the read value +1 to local variable
\* y and (2) assigning y back to x.
\* Unless the read and write of x is done atomically, the Correctness property below will fail.
\* To make this code incorrect, use a second label l2 in front of the assignment from y to x. 
(*
--algorithm Incr {
    variables x=0;
    
    process (p \in Procs)
       variables y=0; 
    {  
       \* both assignments need to be done atomically; l1 ensures that
       l1:
          y :=x+1;
          x := y;  \* Incorrect: l2: x := y;
       print <<self,pc,x>>;
    }
} 
*)

\* BEGIN TRANSLATION
VARIABLES x, pc, y

vars == << x, pc, y >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ x = 0
        (* Process p *)
        /\ y = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "l1"]

l1(self) == /\ pc[self] = "l1"
            /\ y' = [y EXCEPT ![self] = x+1]
            /\ x' = y'[self]
            /\ PrintT(<<self,pc,x'>>)
            /\ pc' = [pc EXCEPT ![self] = "Done"]

p(self) == l1(self)

Next == (\E self \in Procs: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AllDone == \A self \in Procs: pc[self] = "Done"
Correctness == [](AllDone => x = N)

=============================================================================
\* Modification History
\* Last modified Tue Jan 10 09:23:07 CET 2017 by bela
\* Last modified Fri Feb 13 10:00:32 EST 2015 by nrla
\* Created Wed Feb 11 18:05:23 EST 2015 by nrla
