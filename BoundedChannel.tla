--------------------------- MODULE BoundedChannel ---------------------------

EXTENDS Integers, Sequences

CONSTANTS Msg, \* set of messages 
          N \* max size of bounded channel

ASSUME /\ N \in Nat \ {0}
       /\ Msg # {}
       
VARIABLE ch \* the channel


TypeOK == ch \in Seq(Msg)

Init == ch = <<>>


Send == /\ Len(ch) < N
        /\ \E m \in Msg: ch' = Append(ch, m)
        
Recv == /\ Len(ch) > 0
        /\ ch' = Tail(ch)       

Next == Send \/ Recv

Spec == Init /\ [][Next]_<<ch>>

=============================================================================
\* Modification History
\* Last modified Tue Mar 24 13:58:37 CET 2015 by bela
\* Created Tue Mar 24 13:48:11 CET 2015 by bela
