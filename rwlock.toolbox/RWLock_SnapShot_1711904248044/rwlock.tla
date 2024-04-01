------------------------------- MODULE rwlock -------------------------------
EXTENDS Integers, Sequences

\* 读写锁的变量
VARIABLES readers, waitingWriters, writer, queue

\* 初始状态
\* 读者的数量为 0，是否有进程等待写锁，queue 表示等待写锁的队列
Init ==
    /\ readers = 0
    /\ waitingWriters = 0
    /\ writer = FALSE   
    /\ queue = <<>>
    
TryAcquireRLock ==
    /\ waitingWriters = 0 \* 没有写请求时，才允许获取读锁
    /\ writer = FALSE
    /\ readers' = readers + 1
    /\ queue' = queue
    /\ UNCHANGED <<waitingWriters, writer, queue>>

TryAcquireWLock ==
    /\ writer = FALSE
    /\ readers = 0 \* 没有写操作
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

\* 行为定义
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
\* Last modified Mon Apr 01 00:54:34 CST 2024 by 18367
\* Created Mon Apr 01 00:32:31 CST 2024 by 18367
