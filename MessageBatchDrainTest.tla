------------------------------- MODULE MessageBatchDrainTest -------------------------------
EXTENDS Naturals, TLC
CONSTANT N
ASSUME N \in Nat \{0}

Procs == 1..N

(*
  Algorithm for having an MPSC queue where producers (after adding to the queue) either become the single consumer,
  or terminate. The queue is modelled by 'size', and 'counter' decides which producer gets to act as consumer
  next (after adding an element to the queue). The Java algorithm is in MessageBatchDrainTest (JGroups): 
  https://github.com/belaban/JGroups/blob/master/tests/junit-functional/org/jgroups/tests/MessageBatchDrainTest.java
  Contrary to DrainTest, producers can add _multiple_ elements and the
  consumer removes _all_ of the elements in the queue. Note that 'counter' can temporarily
  become negative, e.g. for threads T1, T2, T3:
  - T1 adds 10 -> size: 10, counter: 10
  - T2 adds 5  -> size: 15
  - T3 adds 5  -> size: 20
  - T1 removes all elements: removed: 0, size: 0, counter: -10
  - T2 increments counter by 5: counter is -5
  - T3 increments counter by 5: counter is 0
*)

(*
--algorithm Add {
    variables size=0, counter=0;
    
    process (p \in Procs)
       variables tmp=0, removed=0; 
    {   
       incr_size: size := size + self; \* Add 'self' elements to the queue: p1 adds 1, p2 2 etc...
       
       incr_counter: tmp := counter || counter := counter+self;                     
           
       tmp_check: 
           if(tmp = 0) { \* start draining the queue
               drain: 
                   removed := size || size := 0; \* Remove _all_ elements from the queue
                     
               decr_counter:
                   counter := counter-removed;
                   if(counter # 0)
                       goto drain;    
           }       
    }
}
 
*)
\* BEGIN TRANSLATION
VARIABLES size, counter, pc, tmp, removed

vars == << size, counter, pc, tmp, removed >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ size = 0
        /\ counter = 0
        (* Process p *)
        /\ tmp = [self \in Procs |-> 0]
        /\ removed = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "incr_size"]

incr_size(self) == /\ pc[self] = "incr_size"
                   /\ size' = size + self
                   /\ pc' = [pc EXCEPT ![self] = "incr_counter"]
                   /\ UNCHANGED << counter, tmp, removed >>

incr_counter(self) == /\ pc[self] = "incr_counter"
                      /\ /\ counter' = counter+self
                         /\ tmp' = [tmp EXCEPT ![self] = counter]
                      /\ pc' = [pc EXCEPT ![self] = "tmp_check"]
                      /\ UNCHANGED << size, removed >>

tmp_check(self) == /\ pc[self] = "tmp_check"
                   /\ IF tmp[self] = 0
                         THEN /\ pc' = [pc EXCEPT ![self] = "drain"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << size, counter, tmp, removed >>

drain(self) == /\ pc[self] = "drain"
               /\ /\ removed' = [removed EXCEPT ![self] = size]
                  /\ size' = 0
               /\ pc' = [pc EXCEPT ![self] = "decr_counter"]
               /\ UNCHANGED << counter, tmp >>

decr_counter(self) == /\ pc[self] = "decr_counter"
                      /\ counter' = counter-removed[self]
                      /\ IF counter' # 0
                            THEN /\ pc' = [pc EXCEPT ![self] = "drain"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << size, tmp, removed >>

p(self) == incr_size(self) \/ incr_counter(self) \/ tmp_check(self)
              \/ drain(self) \/ decr_counter(self)

Next == (\E self \in Procs: p(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Only one process can be in state decr_counter at any time (add to Model -> Model Overview -> Invariants)
OnlyOneDrain == \A i,k \in Procs: (i # k) => ~(/\ pc[i] = "drain" /\ pc[k] = "drain") 

\* All the processes are done (state = "Done")
AllDone == \A self \in Procs: pc[self] = "Done"

\* We cannot have elements left in the queue but no threads to process them
\* Add Correctness to the model's properties (Model -> Model Overview -> Properties) 
Correctness == [](AllDone => size = 0 /\ counter = 0) 


=============================================================================
\* Modification History
\* Last modified Tue Jan 10 15:29:18 CET 2017 by bela
\* Last modified Fri Feb 13 10:00:32 EST 2015 by nrla
\* Created Wed Feb 11 18:05:23 EST 2015 by nrla
