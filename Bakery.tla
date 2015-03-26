------------------------------- MODULE Bakery -------------------------------

EXTENDS Integers
CONSTANT N
ASSUME N \in Nat

Procs == 1..N
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

(*
--algorithm AtomicBakery { 
    variable num = [i \in Procs |-> 0] ;
    
    process (p \in Procs)
      variables unchecked, max ;
    { 
      ncs: while (TRUE) { 
           e1: unchecked := Procs \ {self};
               max := 0;
           e2: while (unchecked # {}) { 
                 with (i \in unchecked) { 
                   unchecked := unchecked \ {i};
                   if (num[i] > max) { max := num[i] }
                 }
               };
           e3: with (i \in {j \in Nat : j > max}) { 
                 num[self] := i;
               }; 
               unchecked := Procs \ {self} ;
           wait: while (unchecked # {}) { 
                   with (i \in unchecked) { 
                     await \/ num[i] = 0
                           \/ <<num[self], self>> \prec <<num[i],i>>;
                     unchecked := unchecked \ {i};
                   }
                 };
           cs: skip ; \* the critical section;
           exit: num[self] := 0
           }
    }
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES num, pc, unchecked, max

vars == << num, pc, unchecked, max >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ num = [i \in Procs |-> 0]
        (* Process p *)
        /\ unchecked = [self \in Procs |-> defaultInitValue]
        /\ max = [self \in Procs |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << num, unchecked, max >>

e1(self) == /\ pc[self] = "e1"
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ num' = num

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self]:
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN /\ max' = [max EXCEPT ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ max' = max
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED << unchecked, max >>
            /\ num' = num

e3(self) == /\ pc[self] = "e3"
            /\ \E i \in {j \in Nat : j > max[self]}:
                 num' = [num EXCEPT ![self] = i]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "wait"]
            /\ max' = max

wait(self) == /\ pc[self] = "wait"
              /\ IF unchecked[self] # {}
                    THEN /\ \E i \in unchecked[self]:
                              /\ \/ num[i] = 0
                                 \/ <<num[self], self>> \prec <<num[i],i>>
                              /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                         /\ pc' = [pc EXCEPT ![self] = "wait"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                         /\ UNCHANGED unchecked
              /\ UNCHANGED << num, max >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, unchecked, max >>

exit(self) == /\ pc[self] = "exit"
              /\ num' = [num EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << unchecked, max >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ wait(self)
              \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
MutualExclusion == \A i,j \in Procs : (i # j) => ~ (/\ pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================
\* Modification History
\* Last modified Tue Mar 24 09:57:41 CET 2015 by bela
\* Created Tue Mar 24 09:38:07 CET 2015 by bela
