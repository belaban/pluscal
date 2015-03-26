-------------------------------- MODULE test --------------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC

CONSTANTS Goal, Jugs, Capacity

ASSUME /\ Goal \in Nat
       /\ Capacity \in [Jugs -> Nat \ {0}]

Min(m,n) == IF m < n THEN m ELSE n

Max(m,n) == IF m > n THEN m ELSE n

Foo == [x \in Nat, y \in Nat |-> x*y]

(*

--algorithm DieHard {
    variables injug = [j \in Jugs |-> 0];
  { 
    while(TRUE) {
       either with(j \in Jugs) { \* Empty a jug
          injug[j] := 0;
       }
       or with(j \in Jugs) { \* Fill a jug
          injug[j] := Capacity[j];
       }
       \* Move water from j -> k
       or with(j \in Jugs, k \in Jugs \ {j}, 
               pour = Min(injug[j], Capacity[k] - injug[k])) { 
          injug[j] := injug[j] - pour || injug[k] := injug[k] + pour;
       }
    };
    print [j \in Jugs |-> injug[j]];
  }
}

*)
http://www.archimedes-lab.org/How_to_Solve/images/Water_gas_puzzle.gif
\* BEGIN TRANSLATION

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Mar 19 12:34:13 CET 2015 by bela
\* Created Thu Mar 12 17:37:39 CET 2015 by bela
