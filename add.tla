------------------------------- MODULE add -------------------------------
EXTENDS Naturals, TLC
CONSTANT N
ASSUME N \in Nat \{0}

Procs == 1..N

(*
  Algorithm for having an MPSC queue where producers (after adding to the queue) either become the single consumer,
  or terminate. The queue is modelled by 'size', and 'counter' decides which producer gets to act as consumer
  next (after adding an element to the queue). The Java algorithm is in DrainTest (JGroups): 
  https://github.com/belaban/JGroups/blob/master/tests/junit-functional/org/jgroups/tests/DrainTest.java
*)

(*
--algorithm Add {
    variables size=0, counter=0;
    
    process (p \in Procs)
       variables tmp=0; 
    {
       incr_size: size := size +1; \* Add an element to the queue
       
       incr_counter: tmp := counter || counter := counter+1;                     
           
       tmp_check: 
           if(tmp = 0) { \* start draining the queue
               decr_size: 
                   size := size-1; \* Remove an element from the queue
                   assert ~(size < 0); \* size can never be negative
                     
               decr_counter:
                   counter := counter-1;
                   \* print <<counter,size>>;
                   assert ~(counter < 0); \* counter can never be negative
                   if(counter # 0)
                       goto decr_size;    
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
                      /\ pc' = [pc EXCEPT ![self] = "tmp_check"]
                      /\ size' = size

tmp_check(self) == /\ pc[self] = "tmp_check"
                   /\ IF tmp[self] = 0
                         THEN /\ pc' = [pc EXCEPT ![self] = "decr_size"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << size, counter, tmp >>

decr_size(self) == /\ pc[self] = "decr_size"
                   /\ size' = size-1
                   /\ Assert(~(size' < 0), 
                             "Failure of assertion at line 30, column 20.")
                   /\ pc' = [pc EXCEPT ![self] = "decr_counter"]
                   /\ UNCHANGED << counter, tmp >>

decr_counter(self) == /\ pc[self] = "decr_counter"
                      /\ counter' = counter-1
                      /\ Assert(~(counter' < 0), 
                                "Failure of assertion at line 35, column 20.")
                      /\ IF counter' # 0
                            THEN /\ pc' = [pc EXCEPT ![self] = "decr_size"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << size, tmp >>

p(self) == incr_size(self) \/ incr_counter(self) \/ tmp_check(self)
              \/ decr_size(self) \/ decr_counter(self)

Next == (\E self \in Procs: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Only one process can be in state decr_counter at any time (add to Model -> Model Overview -> Invariants)
OnlyOneDecrCounter == \A i,k \in Procs: (i # k) => ~(/\ pc[i] = "decr_counter" /\ pc[k] = "decr_counter") 

\* All the processes are done (state = "Done")
AllDone == \A self \in Procs: pc[self] = "Done"

\* We cannot have elements left in the queue but no threads to process them
\* Add Correctness to the model's properties (Model -> Model Overview -> Properties) 
Correctness == [](AllDone => size = 0 /\ counter = 0) 

=============================================================================
\* Modification History
\* Last modified Tue Jan 10 13:06:51 CET 2017 by bela
\* Last modified Fri Feb 13 10:00:32 EST 2015 by nrla
\* Created Wed Feb 11 18:05:23 EST 2015 by nrla
