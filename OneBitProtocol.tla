-------------------------------- MODULE OneBitProtocol --------------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC



(*

--algorithm OneBitProtocol {
    variable x \in [{0,1} -> BOOLEAN] ;
    
    fair process (P \in {0,1}) { 
      r: while (TRUE) { 
           either { 
             with (v \in BOOLEAN) { x[self] := v };
             goto r
           }
           or skip;
           e1: x[self] := TRUE;
           e2: if (~x[1-self]) { 
                  cs: print <<pc[self], pc[1-self]>>; 
               }
               else {
                  if(self = 0) goto e2;
                  else {
                    e3: x[1] := FALSE;
                    e4: await ~x[0]
                        goto e1;
                  }
               };
         }
    }
}

  
*)



\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ x \in [{0,1} -> BOOLEAN]
        /\ pc = [self \in ProcSet |-> "r"]

r(self) == /\ pc[self] = "r"
           /\ \/ /\ \E v \in BOOLEAN:
                      x' = [x EXCEPT ![self] = v]
                 /\ pc' = [pc EXCEPT ![self] = "r"]
              \/ /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "e1"]
                 /\ x' = x

e1(self) == /\ pc[self] = "e1"
            /\ x' = [x EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "e2"]

e2(self) == /\ pc[self] = "e2"
            /\ IF ~x[1-self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                  ELSE /\ IF self = 0
                             THEN /\ pc' = [pc EXCEPT ![self] = "e2"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ x' = x

cs(self) == /\ pc[self] = "cs"
            /\ PrintT(<<pc[self], pc[1-self]>>)
            /\ pc' = [pc EXCEPT ![self] = "r"]
            /\ x' = x

e3(self) == /\ pc[self] = "e3"
            /\ x' = [x EXCEPT ![1] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e4"]

e4(self) == /\ pc[self] = "e4"
            /\ IF x[0]
                  THEN /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "e4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ x' = x

P(self) == r(self) \/ e1(self) \/ e2(self) \/ cs(self) \/ e3(self)
              \/ e4(self)

Next == (\E self \in {0,1}: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(P(self))

\* END TRANSLATION

TypeOK ==    pc \in [{0,1} -> {"r", "e1", "e2", "cs"}]
          /\ x \in [{0,1} -> BOOLEAN]
InCS(i) == pc[i] = "cs"
MutualExclusion == ~(InCS(0) /\ InCS(1))
Inv ==    TypeOK
       /\ MutualExclusion
       /\ \A i \in {0,1}: InCS(i) \/ (pc[i] = "e2") => x[i]
Trying(p) == pc[p] \in {"e1", "e2", "e3", "e4"}
DeadlockFree == (Trying(0) \/ Trying(1)) ~> (InCS(0) \/ InCS(1))
=============================================================================
