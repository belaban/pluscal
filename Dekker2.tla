-------------------------------- MODULE Dekker2 --------------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC


(*
 \* http://en.wikipedia.org/wiki/Dekker%27s_algorithm. We only model 2 processes
--algorithm Dekker2 {
  variables entrance_intents=[i \in 0..1 |-> FALSE], \* intent to enter critical section
            turn=0; \* who's turn is it (first: p0)
  
  fair process (proc \in 0..1)
    variables other=1-self; \* the other process; works only with 2 processes 
  {
     start: 
       while(TRUE) {
  
       p0:
         entrance_intents[self] := TRUE;

       p1:
         while(entrance_intents[other]) {
             if(turn # self) {
                entrance_intents[self] := FALSE;
               bw:
                 \* while(turn # self) {skip;};
                 await turn = self;
                 entrance_intents[self] := TRUE;
             }
         };
        
       cs: \* critical section
         print <<"critical section", self>>;
         turn := other;
         entrance_intents[self] := FALSE;
       }
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
        /\ pc = [self \in ProcSet |-> "start"]

start(self) == /\ pc[self] = "start"
               /\ pc' = [pc EXCEPT ![self] = "p0"]
               /\ UNCHANGED << entrance_intents, turn, other >>

p0(self) == /\ pc[self] = "p0"
            /\ entrance_intents' = [entrance_intents EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << turn, other >>

p1(self) == /\ pc[self] = "p1"
            /\ IF entrance_intents[other[self]]
                  THEN /\ IF turn # self
                             THEN /\ entrance_intents' = [entrance_intents EXCEPT ![self] = FALSE]
                                  /\ pc' = [pc EXCEPT ![self] = "bw"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "p1"]
                                  /\ UNCHANGED entrance_intents
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED entrance_intents
            /\ UNCHANGED << turn, other >>

bw(self) == /\ pc[self] = "bw"
            /\ turn = self
            /\ entrance_intents' = [entrance_intents EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << turn, other >>

cs(self) == /\ pc[self] = "cs"
            /\ PrintT(<<"critical section", self>>)
            /\ turn' = other[self]
            /\ entrance_intents' = [entrance_intents EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ other' = other

proc(self) == start(self) \/ p0(self) \/ p1(self) \/ bw(self) \/ cs(self)

Next == (\E self \in 0..1: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 0..1 : WF_vars(proc(self))

\* END TRANSLATION

=============================================================================
