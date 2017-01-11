------------------------------- MODULE MessageBatchDrainTest2 -------------------------------
EXTENDS Naturals, TLC

CONSTANT N,              \* number of processes (e.g. 2)
         MAX_QUEUE_SIZE, \* max size of (bounded) queue (e.g. 10)
         ADD             \* number of elements to add (e.g. 6): make it such that N * ADD > MAX_QUEUE_SIZE to get dropped elements on addition

ASSUME N \in Nat \{0}

Procs == 1..N

Max(x,y) == IF x > y THEN x ELSE y
Min(x,y) == IF x < y THEN x ELSE y 

(*
  Algorithm for having an MPSC queue where producers (after adding to the queue) either become the single consumer, or terminate.
   
  The queue is bounded and is represented by 'size', and 'counter' decides which producer gets to act as consumer
  next (after adding an element to the queue).
  
  Note that if size is 7, MAX_QUEUE_SIZE 10 and we want to add 6 messages, then we can only add 3, dropping 3 elements, making size 10.
  
  The Java algorithm is in MessageBatchDrainTest2 (JGroups): 
  https://github.com/belaban/JGroups/blob/master/tests/junit-functional/org/jgroups/tests/MessageBatchDrainTest2.java
  
  Contrary to DrainTest, producers can add _multiple_ elements and the consumer removes _all_ of the elements in the queue. 
  
  Note that 'counter' can temporarily become negative, e.g. for threads T1, T2, T3:
  - T1 adds 10 -> size: 10, counter: 10
  - T2 adds 5  -> size: 15
  - T3 adds 5  -> size: 20
  - T1 removes all elements: removed: 0, size: 0, counter: -10
  - T2 increments counter by 5: counter is -5
  - T3 increments counter by 5: counter is 0
  
  
  This algorithm is INCORRECT as counter going from (say) -4 to 0 will allow the next process to enter the 'drain' label (tmp == 0) while the existing
  process is still in 'drain': this violates the OnlyOneDrain invariant (at the bottom) !!!
*)

(*
--algorithm Add {
    variables size=0, counter=0;
    
    
    process (p \in Procs)
       variables tmp=0, added=0, removed=0, new_size=0, old_size=0; 
    {   
       add:
           old_size := size;
           new_size := Min(size+ADD, MAX_QUEUE_SIZE);        
           added := new_size - size || size := new_size; \* Add ADD elements to the queue
           print <<"old_size= ", old_size, "new_size= ",new_size, "size= ", size, "added= ", added>>;
           
           if(added > 0) {
             
               incr_counter: 
                   tmp := counter || counter := counter+added;                     
           
               tmp_check: 
                   if(tmp = 0) { \* start draining the queue
                       drain: 
                           removed := size || size := 0; \* Remove _all_ elements from the queue
                     
                       decr_counter:
                           counter := counter-removed;
                           if(counter # 0)
                               goto drain;    
                   }                     
           };                  
    }
}
 
*)
\* BEGIN TRANSLATION
VARIABLES size, counter, pc, tmp, added, removed, new_size, old_size

vars == << size, counter, pc, tmp, added, removed, new_size, old_size >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ size = 0
        /\ counter = 0
        (* Process p *)
        /\ tmp = [self \in Procs |-> 0]
        /\ added = [self \in Procs |-> 0]
        /\ removed = [self \in Procs |-> 0]
        /\ new_size = [self \in Procs |-> 0]
        /\ old_size = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "add"]

add(self) == /\ pc[self] = "add"
             /\ old_size' = [old_size EXCEPT ![self] = size]
             /\ new_size' = [new_size EXCEPT ![self] = Min(size+ADD, MAX_QUEUE_SIZE)]
             /\ /\ added' = [added EXCEPT ![self] = new_size'[self] - size]
                /\ size' = new_size'[self]
             /\ PrintT(<<"old_size= ", old_size'[self], "new_size= ",new_size'[self], "size= ", size', "added= ", added'[self]>>)
             /\ IF added'[self] > 0
                   THEN /\ pc' = [pc EXCEPT ![self] = "incr_counter"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << counter, tmp, removed >>

incr_counter(self) == /\ pc[self] = "incr_counter"
                      /\ /\ counter' = counter+added[self]
                         /\ tmp' = [tmp EXCEPT ![self] = counter]
                      /\ pc' = [pc EXCEPT ![self] = "tmp_check"]
                      /\ UNCHANGED << size, added, removed, new_size, old_size >>

tmp_check(self) == /\ pc[self] = "tmp_check"
                   /\ IF tmp[self] = 0
                         THEN /\ pc' = [pc EXCEPT ![self] = "drain"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << size, counter, tmp, added, removed, 
                                   new_size, old_size >>

drain(self) == /\ pc[self] = "drain"
               /\ /\ removed' = [removed EXCEPT ![self] = size]
                  /\ size' = 0
               /\ pc' = [pc EXCEPT ![self] = "decr_counter"]
               /\ UNCHANGED << counter, tmp, added, new_size, old_size >>

decr_counter(self) == /\ pc[self] = "decr_counter"
                      /\ counter' = counter-removed[self]
                      /\ IF counter' # 0
                            THEN /\ pc' = [pc EXCEPT ![self] = "drain"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << size, tmp, added, removed, new_size, 
                                      old_size >>

p(self) == add(self) \/ incr_counter(self) \/ tmp_check(self)
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
\* Last modified Wed Jan 11 14:13:14 CET 2017 by bela
\* Last modified Fri Feb 13 10:00:32 EST 2015 by nrla
\* Created Wed Feb 11 18:05:23 EST 2015 by nrla
