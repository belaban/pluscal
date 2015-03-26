-------------------------------- MODULE Dekker --------------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC


(*
 \* http://en.wikipedia.org/wiki/Dekker%27s_algorithm. We only model 2 processes
--algorithm Dekker {
  variables entrance_intents=[i \in 0..1 |-> FALSE], \* intent to enter critical section
            turn=0; \* who's turn is it (first: p0)
  
  process (proc \in 0..1)
    variables other=1-self; \* the other process; works only with 2 processes 
  {
     p0:
       entrance_intents[self] := TRUE;
     p1:  
       await ~entrance_intents[other] /\ turn = self; 
     cs: \* critical section
       print <<self, "critical section">>;
       turn := other;
       entrance_intents[self] := FALSE;
  }

 
}

*)

\* BEGIN TRANSLATION
VARIABLES entrance_intents, turn, pc, other

vars == << entrance_intents, turn, pc, other >>

ProcSet == (0..1)

Init == (* Global variables *)
        /\ entrance_intents = [i \in 0..1 |-> FALSE]
        /\ turn = 0
        (* Process proc *)
        /\ other = [self \in 0..1 |-> 1-self]
        /\ pc = [self \in ProcSet |-> "p0"]

p0(self) == /\ pc[self] = "p0"
            /\ entrance_intents' = [entrance_intents EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << turn, other >>

p1(self) == /\ pc[self] = "p1"
            /\ ~entrance_intents[other[self]] /\ turn = self
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << entrance_intents, turn, other >>

cs(self) == /\ pc[self] = "cs"
            /\ PrintT(<<self, "critical section">>)
            /\ turn' = other[self]
            /\ entrance_intents' = [entrance_intents EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ other' = other

proc(self) == p0(self) \/ p1(self) \/ cs(self)

Next == (\E self \in 0..1: proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
