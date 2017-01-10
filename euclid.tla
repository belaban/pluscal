------------------------------- MODULE euclid -------------------------------

(* for functions print, .., and assert *)
EXTENDS Naturals, TLC
(* parameterize the algorithm by K, make concrete before checking model *)
\* CONSTANT K


(* PlusCal options (-termination) *)

(* helpers *)
Divides(i,j) == \E k \in 0..j : j = i * k
\*Divides(i,j) == j % i = 0
IsGCD(i,j,k) == Divides(i,j) /\ Divides(i,k) /\ \A r \in 0..j \cup 0..k : Divides(r,j) /\ Divides(r,k) => Divides(r,i)

THEOREM GCD1 == \A x \in Nat \ {0}: IsGCD(x,x,x)

(*
--algorithm euclid {
  variables m=30, n=18, u=m, v=n, v_ini=v;
  { 
    bela: while (u # 0) {
      iff: if (u < v)
        u := v || v := u;
      tmp: u := u - v;
    };
    print <<m,v_ini,"have gdc",v>>;
    (* correctness condition *)
    assert IsGCD(v,m,n)
  }
}
*)
\* BEGIN TRANSLATION
VARIABLES m, n, u, v, v_ini, pc

vars == << m, n, u, v, v_ini, pc >>

Init == (* Global variables *)
        /\ m = 30
        /\ n = 18
        /\ u = m
        /\ v = n
        /\ v_ini = v
        /\ pc = "bela"

bela == /\ pc = "bela"
        /\ IF u # 0
              THEN /\ pc' = "iff"
              ELSE /\ PrintT(<<m,v_ini,"have gdc",v>>)
                   /\ Assert(IsGCD(v,m,n), 
                             "Failure of assertion at line 29, column 5.")
                   /\ pc' = "Done"
        /\ UNCHANGED << m, n, u, v, v_ini >>

iff == /\ pc = "iff"
       /\ IF u < v
             THEN /\ /\ u' = v
                     /\ v' = u
             ELSE /\ TRUE
                  /\ UNCHANGED << u, v >>
       /\ pc' = "tmp"
       /\ UNCHANGED << m, n, v_ini >>

tmp == /\ pc = "tmp"
       /\ u' = u - v
       /\ pc' = "bela"
       /\ UNCHANGED << m, n, v, v_ini >>

Next == bela \/ iff \/ tmp
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Jan 05 18:44:44 CET 2017 by bela
\* Created Mon Mar 09 16:07:32 CET 2015 by bela
