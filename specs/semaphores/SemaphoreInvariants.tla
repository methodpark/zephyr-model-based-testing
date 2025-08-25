---- ---- MODULE SemaphoreInvariants ----
EXTENDS TLC, Naturals, Integers

CONSTANTS
    N_THREADS,      \* Number of threads
    NULL,           \* Represents absence of data
    ThreadIDs,
    SemaphoreIDs,
    ThreadPrio(_)

VARIABLES pc, runq, current, threads, sems

PrioQ == INSTANCE PriorityQueues


----------------------------------------
\* Helpers

InitializedSemaphores == { sid \in SemaphoreIDs: sems[sid] # NULL }

----------------------------------------
\* Invariants inspired by OpenCOM RTOS TLA+ book

\* I1: There are never more threads on the run queue than there are threads in the system.
RunQLengthAtMostNumberOfTotalThreads == PrioQ!Len(runq) <= N_THREADS

\* I2: There are never more threads on a wait queue than there are in total.
WaitQLengthAtMostNumberOfTotalThreads == 
    \A sid \in InitializedSemaphores: PrioQ!Len(sems[sid].wait_q) <= N_THREADS

\* I3: All entries of the semaphore wait queues must be valid thread IDs.
WaitQueueEntriesValidThreadIDs ==
    \A sid \in InitializedSemaphores: PrioQ!Threads(sems[sid].wait_q) \subseteq ThreadIDs

\* I4a: No ready thread can be on a wait queue
AllReadyThreadsNotOnWaitQueue ==
    \A ready_tid \in PrioQ!Threads(runq):
        \A sid \in InitializedSemaphores:
            ready_tid \notin PrioQ!Threads(sems[sid].wait_q)

\* I4b: No thread waiting for a semaphore can be on the run queue
AllWaitingThreadsNotOnRunQueue ==
    \A sid \in InitializedSemaphores:
        \A wait_tid \in PrioQ!Threads(sems[sid].wait_q):
            wait_tid \notin PrioQ!Threads(runq)

\* I5: The semaphore wait queue must be empty whenever the count is larger than zero.
NonZeroCountImpliesWaitQueueEmpty ==
    \A sid \in InitializedSemaphores:
        sems[sid].count > 0 => PrioQ!Empty(sems[sid].wait_q)

----------------------------------------

\* I6: A waiting thread is always at the RESCHED_K_SEM_TAKE label.
WaitingThreadAtTakeReschedule ==
    \A sid \in InitializedSemaphores:
        \A wait_tid \in PrioQ!Threads(sems[sid].wait_q):
            pc[wait_tid] = "RESCHED_K_SEM_TAKE"

\* I7: The ready list and all semaphore wait queues are sorted such that a thread 
\* at a lower index in the queue has higher or equal priority compared to threads at higher indices.

PrioQSorted(prioq) ==
    \A i, j \in DOMAIN prioq:
        i < j => PrioQ!PrioHigherOrEqual(threads[prioq[i]].prio, threads[prioq[j]].prio)

AllPrioQueuesSorted ==
    /\ PrioQSorted(runq)
    /\ \A sid \in InitializedSemaphores: PrioQSorted(sems[sid].wait_q)

\* I8: The current thread is always on the run queue.
CurrentThreadOnRunQueue == current \in PrioQ!Threads(runq)

----------------------------------------

SemaphoreInvariant ==
    /\ RunQLengthAtMostNumberOfTotalThreads
    /\ WaitQLengthAtMostNumberOfTotalThreads
    /\ WaitQueueEntriesValidThreadIDs
    /\ AllReadyThreadsNotOnWaitQueue
    /\ AllWaitingThreadsNotOnRunQueue
    /\ NonZeroCountImpliesWaitQueueEmpty
    /\ WaitingThreadAtTakeReschedule
    /\ AllPrioQueuesSorted
    /\ CurrentThreadOnRunQueue

====
