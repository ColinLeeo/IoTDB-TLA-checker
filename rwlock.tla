------------------------------- MODULE rwLock -------------------------------
EXTENDS Integers, Sequences

VARIABLES readers, waitingWriters, writer, queue

Init ==
    /\ readers = 0
    /\ waitingWriters = 0
    /\ writer = FALSE   
    /\ queue = <<>>
    
TryAcquireRLock ==
    /\ waitingWriters = 0 
    /\ writer = FALSE
    /\ readers' = readers + 1
    /\ queue' = queue
    /\ UNCHANGED <<waitingWriters, writer, queue>>

TryAcquireWLock ==
    /\ writer = FALSE
    /\ readers = 0
    /\ waitingWriters' = waitingWriters - 1
    /\ writer' = TRUE
    /\ UNCHANGED readers
    /\ queue' = Append(queue, "Write")
    
ReleaseRLock ==
    /\ readers > 0
    /\ readers' = readers - 1
    /\ UNCHANGED << writer, waitingWriters, queue>>
    
ReleaseWLock ==
   /\ writer = TRUE
   /\ writer' = FALSE
   /\ waitingWriters' = waitingWriters - 1
   /\ UNCHANGED readers
   /\ queue' = Tail(queue)

Next ==
    \/ TryAcquireRLock
    \/ ReleaseRLock
    \/ TryAcquireWLock
    \/ ReleaseWLock

Spec == Init /\ [][Next]_<<readers, waitingWriters, writer, queue>>

TypeInvariant ==
    /\ readers \in Nat
    /\ waitingWriters \in Nat
    /\ writer \in {TRUE, FALSE}

=============================================================================
\* Modification History
\* Last modified Wed May 08 17:32:21 CST 2024 by 18367
\* Created Mon Apr 01 00:32:31 CST 2024 by 18367
