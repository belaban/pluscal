--------------------------------- MODULE eu ---------------------------------
EXTENDS TLC, Sequences, Integers

CONSTANTS K,M

(*

--algorithm eu {
     variables x=K,y=M; \* y will hold the result
     
     {
       while(x # 0) {
          if(x < y)
              x := y || y := x;
          x := x-y;
          print <<x,y>>;
       };
       
       print <<"gcd", K, M, x, y>>;
     }
     
}

*)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = K
        /\ y = M
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # 0
               THEN /\ IF x < y
                          THEN /\ /\ x' = y
                                  /\ y' = x
                          ELSE /\ TRUE
                               /\ UNCHANGED << x, y >>
                    /\ pc' = "Lbl_2"
               ELSE /\ PrintT(<<"gcd", K, M, x, y>>)
                    /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ x' = x-y
         /\ PrintT(<<x',y>>)
         /\ pc' = "Lbl_1"
         /\ y' = y

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Tue Mar 24 16:24:16 CET 2015 by bela
\* Created Tue Mar 24 16:17:55 CET 2015 by bela
