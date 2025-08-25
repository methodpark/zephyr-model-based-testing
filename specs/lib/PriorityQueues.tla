---- MODULE PriorityQueues ----

\* This module contains reusable operator definitions for modeling Zephyr's priority queues.
\* A priority queue is represented as a sequence of thread IDs, ordered by priority.
\* Like in Zephyr, for threads of same priority, FIFO order is used.
\* We use the same interpretation of priorities as in Zephyr, i.e. lower numerical values indicate higher priority.

LOCAL INSTANCE Naturals

Seq == INSTANCE Sequences
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE Functions

CONSTANTS
    NULL,
    \* Operator mapping thread ids to priorities.
    \* Must be defined in the spec using this module.
    ThreadPrio(_)

\* In Zephyr, a higher number is a lower priority and  v.v.
PrioHigher(p1, p2) == p1 < p2
PrioEqual(p1, p2) == p1 = p2
PrioLower(p1, p2) == p1 > p2
PrioHigherOrEqual(p1, p2) == PrioHigher(p1, p2) \/ PrioEqual(p1, p2)

New == <<>>
Empty(prioq) == prioq = <<>>
First(prioq) == Seq!Head(prioq)
FirstOrNULL(prioq) == IF ~Empty(prioq) THEN Seq!Head(prioq) ELSE NULL
Tail(prioq) == Seq!Tail(prioq)
Len(prioq) == Seq!Len(prioq)

\* The set of threads in the priority queue
Threads(prioq) == Range(prioq)

EnqueueThreadByPrio(prioq, thread_id, thread_prio) ==
    \* Evaluates to the priority queue that results from adding the 
    \* thread with id `thread_id` to `prioq` if the thread has priority `thread_prio`.
    LET
        idx == SelectLastInSeq(
            prioq,
            LAMBDA tid: PrioHigherOrEqual(ThreadPrio(tid), thread_prio)
        )
    IN
        InsertAt(prioq, idx+1, thread_id)

EnqueueThreadByPrioMapping(prioq, thread_id, thread_prio_mapping) ==
    \* Evaluates to the priority queue that results from adding the 
    \* thread with id `thread_id` to `prioq` if the thread priorities are given by 
    \* the function `thread_prio_mapping`.
    LET
        idx == SelectLastInSeq(
            prioq,
            LAMBDA tid: PrioHigherOrEqual(thread_prio_mapping[tid], thread_prio_mapping[thread_id])
        )
    IN
        InsertAt(prioq, idx+1, thread_id)

Enqueue(prioq, thread_id) ==
    \* Evaluates to the priority queue that results from adding the
    \* thread with id `thread_id` to `prioq`.
    EnqueueThreadByPrio(prioq, thread_id, ThreadPrio(thread_id))

RECURSIVE Merge(_, _)
Merge(dest_prioq, src_prioq) ==
    \* Evaluates to the priority queue that results from adding
    \* all threads from `src_prioq` to `dest_prioq` iteratively
    \* in the order given by `src_prioq`.
    IF Empty(src_prioq)
    THEN
        dest_prioq
    ELSE
        LET
            new_dest_prioq == Enqueue(dest_prioq, First(src_prioq))
            new_src_prioq == Tail(src_prioq)
        IN
            Merge(new_dest_prioq, new_src_prioq)

ThreadPrioHigherOrEqual(tid1, tid2) == PrioHigherOrEqual(ThreadPrio(tid1), ThreadPrio(tid2))
\* A priority queue for the threads in the set `thread_ids`.
\* The order of threads with the same priority is undefined.
NewQueueFromThreads(thread_ids) == SetToSortSeq(thread_ids, ThreadPrioHigherOrEqual)

\* The result of removing thread `thread_id` from prioq.
DequeueThread(prioq, thread_id) == Remove(prioq, thread_id)

====
