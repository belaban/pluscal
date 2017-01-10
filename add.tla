------------------------------- MODULE add -------------------------------
EXTENDS Naturals, TLC
CONSTANT N
ASSUME N \in Nat \{0}

Procs == 1..N

(*
--algorithm add {
    variables size=0, counter=0;
    
    process (p \in Procs)
       variables tmp=0; 
    {
       incr_size: size := size +1; \* Add an element to the queue
       
       incr_counter: tmp := counter || counter := counter+1;
                     print <<counter,size>>;
                     \* assert ~(counter < 0); \* counter can never be negative
           
       tmp_check: if(tmp = 0) { \* start draining the queue
                     decr_size: size := size-1; \* Remove an element from the queue
                     decr_counter: counter := counter-1;
                     print <<counter,size>>;
                     assert ~(counter < 0);
                     assert ~(size < 0);
                     check: if(counter # 0)
                         goto decr_size;    
                  }   
                  else {
                     goto Done;
                  } 
    
    }
}
 
*)
\* BEGIN TRANSLATION
VARIABLES size, counter, pc, tmp

vars == << size, counter, pc, tmp >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ size = 0
        /\ counter = 0
        (* Process p *)
        /\ tmp = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "incr_size"]

incr_size(self) == /\ pc[self] = "incr_size"
                   /\ size' = size +1
                   /\ pc' = [pc EXCEPT ![self] = "incr_counter"]
                   /\ UNCHANGED << counter, tmp >>

incr_counter(self) == /\ pc[self] = "incr_counter"
                      /\ /\ counter' = counter+1
                         /\ tmp' = [tmp EXCEPT ![self] = counter]
                      /\ PrintT(<<counter',size>>)
                      /\ pc' = [pc EXCEPT ![self] = "tmp_check"]
                      /\ size' = size

tmp_check(self) == /\ pc[self] = "tmp_check"
                   /\ IF tmp[self] = 0
                         THEN /\ pc' = [pc EXCEPT ![self] = "decr_size"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << size, counter, tmp >>

decr_size(self) == /\ pc[self] = "decr_size"
                   /\ size' = size-1
                   /\ pc' = [pc EXCEPT ![self] = "decr_counter"]
                   /\ UNCHANGED << counter, tmp >>

decr_counter(self) == /\ pc[self] = "decr_counter"
                      /\ counter' = counter-1
                      /\ PrintT(<<counter',size>>)
                      /\ Assert(~(counter' < 0), 
                                "Failure of assertion at line 25, column 22.")
                      /\ Assert(~(size < 0), 
                                "Failure of assertion at line 26, column 22.")
                      /\ pc' = [pc EXCEPT ![self] = "check"]
                      /\ UNCHANGED << size, tmp >>

check(self) == /\ pc[self] = "check"
               /\ IF counter # 0
                     THEN /\ pc' = [pc EXCEPT ![self] = "decr_size"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << size, counter, tmp >>

p(self) == incr_size(self) \/ incr_counter(self) \/ tmp_check(self)
              \/ decr_size(self) \/ decr_counter(self) \/ check(self)

Next == (\E self \in Procs: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Mon Jan 09 19:12:42 CET 2017 by bela
\* Last modified Fri Feb 13 10:00:32 EST 2015 by nrla
\* Created Wed Feb 11 18:05:23 EST 2015 by nrla
