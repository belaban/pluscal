----------------------- MODULE EuclidSedgewickpstyle -----------------------
(* for functions print, .., and assert *)
EXTENDS Naturals, TLC
(* parameterize the algorithm by K, make concrete before checking model *)
CONSTANT K

(* PlusCal options (-termination) *)

(* helpers *)
Divides(i,j) == \E k \in 0..j : j = i * k
IsGCD(i,j,k) == Divides(i,j) /\ Divides(i,k) /\ \A r \in 0..j \cup 0..k : Divides(r,j) /\ Divides(r,k) => Divides(r,i)

(*
--algorithm EuclidSedgewick
  variables m \in 1..K, n \in 1..K, u=m, v=n
  begin 
    print <<u,v>>;
    while (u # 0) do
      if (u < v) then u := v || v := u end if;
      u := u - v
    end while;
    (* correctness condition *)
    assert IsGCD(v,m,n)
 end algorithm
*)

\* BEGIN TRANSLATION
VARIABLES m, n, u, v, pc

vars == << m, n, u, v, pc >>

Init == (* Global variables *)
        /\ m \in 1..K
        /\ n \in 1..K
        /\ u = m
        /\ v = n
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT(<<u,v>>)
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << m, n, u, v >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF (u # 0)
               THEN /\ IF (u < v)
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_3"
               ELSE /\ Assert(IsGCD(v,m,n), 
                              "Failure of assertion at line 23, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>
         /\ UNCHANGED << m, n >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ u' = u - v
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << m, n, v >>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Feb 17 10:31:21 EST 2015 by nrla
\* Created Wed Feb 11 18:29:13 EST 2015 by nrla
