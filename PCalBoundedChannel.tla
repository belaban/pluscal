------------------------- MODULE PCalBoundedChannel -------------------------

EXTENDS Integers, Sequences

CONSTANTS Msg, \* set of messages 
          N \* max size of bounded channel

ASSUME /\ N \in Nat \ {0}
       /\ Msg # {}
       
       

       
(*

--algorithm PCalBoundedChannel { 
    variables ch = <<>>; \* the channel
  
    macro Send(m) {
       if(Len(ch) < N) {
          ch := Append(ch, m);
       }
    }
    
    macro Recv() {
       if(Len(ch) > 0) {
          ch := Tail(ch);
       }
    }
  
    process(sender="S") {
       s0: 
         while(TRUE) {
           \* Send(m);
           await Len(ch) < N;
           with(m \in Msg)
              ch := Append(ch, m);
         }
    }
    
    process(receiver="R") {
       r0: 
         while(TRUE) {
           \* Recv();
           await Len(ch) > 0;
           ch := Tail(ch);
         }
    }
    
    
   (*{
      while(TRUE) {
         either {
            with(m \in Msg) {
               Send(m);
            }
         }
         or {
            Recv();
         }
      }
   }*)
}


*)


\* BEGIN TRANSLATION
VARIABLE ch

vars == << ch >>

ProcSet == {"S"} \cup {"R"}

Init == (* Global variables *)
        /\ ch = <<>>

sender == /\ Len(ch) < N
          /\ \E m \in Msg:
               ch' = Append(ch, m)

receiver == /\ Len(ch) > 0
            /\ ch' = Tail(ch)

Next == sender \/ receiver

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
       




=============================================================================
\* Modification History
\* Last modified Tue Mar 24 14:39:27 CET 2015 by bela
\* Created Tue Mar 24 14:11:22 CET 2015 by bela



       
