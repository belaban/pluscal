----------------------------- MODULE ABProtocol -----------------------------
EXTENDS Naturals, Sequences, TLC
(* the input array of messages to the algorithm *)
CONSTANT Msg

(* PlusCal options (-termination) *)

(* define remove operation*)
Remove(i,seq) == [ j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

(*
--algorithm ABProtocol 
{ variables input = <<>>; output = <<>>; msgC = <<>>; ackC = <<>>;

 macro Send(m, chan) { chan := Append(chan,m) }
 macro Rcv(v, chan) { await chan # <<>>; 
                      v := Head(chan); 
                      chan := Tail(chan)}                   

 process (Sender = "S") 
   variables next = 1; sbit = 0; ack;
   { s: while (TRUE) {
       either with (m \in Msg) { input := Append(input, m)}    \* grab message from user to send 
       or { await next <= Len(input) ;                         \* wait until message is available, then send next message 
             Send(<<input[next],sbit>>, msgC)}
       or { Rcv(ack, ackC);                                    \* receive acknowledgement and set up for next message
            if (ack = sbit) { next := next+1;
                               sbit := (sbit+1)%2 }}}}
     
  process (Receiver = "R") 
    variables rbit = 1; msg;
    { r: while (TRUE) {
        either Send(rbit,ackC)                                 \* send current acknowledgement
        or  { Rcv(msg, msgC);                                  \* receive next message (unconditional) and deliver if has correct abit
              if (msg[2] # rbit) { rbit := (rbit+1)%2 ;
                                   output := Append(output, msg[1])}}}}
                                   
  process (LoseMsg = "L") 
  { l: while (TRUE) {
      either with (i \in 1..Len(msgC)) { msgC := Remove(i, msgC)} \* drop a randomly chosen message
      or with (i \in 1..Len(ackC)) {ackC := Remove(i, ackC) }}}   \* drop a randomly chosen ack

} (* end ABProtocol *)  
                
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES input, output, msgC, ackC, next, sbit, ack, rbit, msg

vars == << input, output, msgC, ackC, next, sbit, ack, rbit, msg >>

ProcSet == {"S"} \cup {"R"} \cup {"L"}

Init == (* Global variables *)
        /\ input = <<>>
        /\ output = <<>>
        /\ msgC = <<>>
        /\ ackC = <<>>
        (* Process Sender *)
        /\ next = 1
        /\ sbit = 0
        /\ ack = defaultInitValue
        (* Process Receiver *)
        /\ rbit = 1
        /\ msg = defaultInitValue

Sender == /\ \/ /\ \E m \in Msg:
                     input' = Append(input, m)
                /\ UNCHANGED <<msgC, ackC, next, sbit, ack>>
             \/ /\ next <= Len(input)
                /\ msgC' = Append(msgC,(<<input[next],sbit>>))
                /\ UNCHANGED <<input, ackC, next, sbit, ack>>
             \/ /\ ackC # <<>>
                /\ ack' = Head(ackC)
                /\ ackC' = Tail(ackC)
                /\ IF ack' = sbit
                      THEN /\ next' = next+1
                           /\ sbit' = (sbit+1)%2
                      ELSE /\ TRUE
                           /\ UNCHANGED << next, sbit >>
                /\ UNCHANGED <<input, msgC>>
          /\ UNCHANGED << output, rbit, msg >>

Receiver == /\ \/ /\ ackC' = Append(ackC,rbit)
                  /\ UNCHANGED <<output, msgC, rbit, msg>>
               \/ /\ msgC # <<>>
                  /\ msg' = Head(msgC)
                  /\ msgC' = Tail(msgC)
                  /\ IF msg'[2] # rbit
                        THEN /\ rbit' = (rbit+1)%2
                             /\ output' = Append(output, msg'[1])
                        ELSE /\ TRUE
                             /\ UNCHANGED << output, rbit >>
                  /\ ackC' = ackC
            /\ UNCHANGED << input, next, sbit, ack >>

LoseMsg == /\ \/ /\ \E i \in 1..Len(msgC):
                      msgC' = Remove(i, msgC)
                 /\ ackC' = ackC
              \/ /\ \E i \in 1..Len(ackC):
                      ackC' = Remove(i, ackC)
                 /\ msgC' = msgC
           /\ UNCHANGED << input, output, next, sbit, ack, rbit, msg >>

Next == Sender \/ Receiver \/ LoseMsg

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Sender)
        /\ WF_vars(Receiver)
        /\ WF_vars(LoseMsg)

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Tue Feb 24 14:47:59 EST 2015 by nrla
\* Created Wed Feb 11 01:11:40 EST 2015 by nrla
