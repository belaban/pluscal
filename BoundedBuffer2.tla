-------------------------------- MODULE BoundedBuffer2 --------------------------------
EXTENDS Naturals, Integers, FiniteSets, Bags, Sequences, TLC

CONSTANTS producers,     \* set of producers 
          consumers,     \* set of consumers 
          BUF_SIZE       \* size of the buffer
          
ASSUME /\ producers # {}
       /\ consumers # {}
       /\ producers \intersect consumers = {}
       /\ BUF_SIZE > 0
       

participants == producers \union consumers



(*

--algorithm BoundedBuffer2 {
    variables running_threads=participants,
              wait_set={},        \* producers or consumers waiting on a full/empty buffer
              buf = <<>>,         \* buffer
              accesses=0;         \* total number of gets and puts (used for termination)

    \* define {running_threads == participants \ wait_set}              
  
    macro wait(p) {
       wait_set := wait_set \union {p};
       running_threads := running_threads \ {p};
    }
    
    macro notify() {
       if(wait_set # {}) {
          with(m \in wait_set) {
            wait_set := wait_set \ {m};
            running_threads := running_threads \union {m};
          }
       }
    }
    
    macro notifyAll() {
       if(wait_set # {}) {
          running_threads := running_threads \union wait_set;
          wait_set := wait_set \ wait_set;
       }
    }
              
    macro put(p) {
       if(Len(buf) < BUF_SIZE) {
          buf := Append(buf, accesses);
          accesses := accesses +1;
          notifyAll();
       }
       else
          wait(p);
    }
    
    macro get(p) {
       if(Len(buf) > 0) {
          buf := Tail(buf);
          notifyAll();
       }
       else {
          wait(p);
       }
    }
              
  
  
    {
       while(TRUE) {
          with(p \in running_threads) {
             if(p \in producers) {
                put(p);
             }
             else {
                get(p);
             }
          }
       }
    }
 

}

*)

\* BEGIN TRANSLATION
VARIABLES running_threads, wait_set, buf, accesses

vars == << running_threads, wait_set, buf, accesses >>

Init == (* Global variables *)
        /\ running_threads = participants
        /\ wait_set = {}
        /\ buf = <<>>
        /\ accesses = 0

Next == \E p \in running_threads:
          IF p \in producers
             THEN /\ IF Len(buf) < BUF_SIZE
                        THEN /\ buf' = Append(buf, accesses)
                             /\ accesses' = accesses +1
                             /\ IF wait_set # {}
                                   THEN /\ running_threads' = (running_threads \union wait_set)
                                        /\ wait_set' = wait_set \ wait_set
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << running_threads, 
                                                        wait_set >>
                        ELSE /\ wait_set' = (wait_set \union {p})
                             /\ running_threads' = running_threads \ {p}
                             /\ UNCHANGED << buf, accesses >>
             ELSE /\ IF Len(buf) > 0
                        THEN /\ buf' = Tail(buf)
                             /\ IF wait_set # {}
                                   THEN /\ running_threads' = (running_threads \union wait_set)
                                        /\ wait_set' = wait_set \ wait_set
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << running_threads, 
                                                        wait_set >>
                        ELSE /\ wait_set' = (wait_set \union {p})
                             /\ running_threads' = running_threads \ {p}
                             /\ buf' = buf
                  /\ UNCHANGED accesses

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
