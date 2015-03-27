---------------------------- MODULE OneBitClock ----------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC

Put(s) == Append(s, "widget")
Get(s) == Tail(s)


(*

--fair algorithm OneBitClock {
    variable b = 0 , box = << >> ;
 
    process(Producer = 0) { 
      p1: 
      while (TRUE) {
        await b = 0 ;
        box := Put(box) ;
        b := 1;
        print <<0,b,box>>;
      }
    }
 
    process (Consumer = 1) { 
      c1: 
      while (TRUE) { 
        await b = 1 ;
        box := Get(box) ;
        b := 0;
        print <<1,b,box>>;
      }
    }

}

*)
\* BEGIN TRANSLATION
VARIABLES b, box

vars == << b, box >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ b = 0
        /\ box = << >>

Producer == /\ b = 0
            /\ box' = Put(box)
            /\ b' = 1
            /\ PrintT(<<0,b',box'>>)

Consumer == /\ b = 1
            /\ box' = Get(box)
            /\ b' = 0
            /\ PrintT(<<1,b',box'>>)

Next == Producer \/ Consumer

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Mar 27 09:24:54 CET 2015 by bela
\* Created Thu Mar 26 18:33:13 CET 2015 by bela
