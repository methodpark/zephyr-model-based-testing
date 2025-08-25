---- ---- MODULE MutexInvariants ----
EXTENDS TLC, Naturals, Integers

CONSTANTS
    N_THREADS,      \* Number of threads
    NULL,           \* Represents absence of data
    ThreadIDs,
    SemaphoreIDs,
    MutexIDs,
    ThreadPrio(_)

VARIABLES pc, runq, current, threads, mutexes, sems, ret, logical_state_id, 
          stack
VARIABLES tid_thread_create, prio, delay_thread_create, sem_init_sem_ptr, 
          initial_count, limit, sem_give_sem_ptr, sem_take_sem_ptr, 
          sem_take_timeout, mutex_init_mut_ptr, mutex_lock_mut_ptr, 
          mutex_lock_timeout, mutex_unlock_mut_ptr

PrioQ == INSTANCE PriorityQueues

----------------------------------------
\* Helpers

InitializedSemaphores == { sid \in SemaphoreIDs: sems[sid] # NULL }
InitializedMutexes == { mid \in MutexIDs: mutexes[mid] # NULL }

----------------------------------------

\* I1: There are never more threads on the run queue than there are threads in the system.
RunQLengthAtMostNumberOfTotalThreads == PrioQ!Len(runq) <= N_THREADS

\* I2: There are never more threads on a wait queue than there are in total.
WaitQLengthAtMostNumberOfTotalThreads == 
    /\ \A sid \in InitializedSemaphores:
        PrioQ!Len(sems[sid].wait_q) <= N_THREADS
    /\ \A mid \in InitializedMutexes:
        PrioQ!Len(mutexes[mid].wait_q) <= N_THREADS

\* I3: All entries of the semaphore and mutex wait queues must be valid thread IDs.
WaitQueueEntriesValidThreadIDs ==
    /\ \A sid \in InitializedSemaphores:
        PrioQ!Threads(sems[sid].wait_q) \subseteq ThreadIDs
    /\ \A mid \in InitializedMutexes:
        PrioQ!Threads(mutexes[mid].wait_q) \subseteq ThreadIDs

\* I4a: No ready thread can be on a wait queue
AllReadyThreadsNotOnWaitQueue ==
    \A ready_tid \in PrioQ!Threads(runq):
        /\ \A sid \in InitializedSemaphores:
            ready_tid \notin PrioQ!Threads(sems[sid].wait_q)
        /\ \A mid \in InitializedMutexes:
            ready_tid \notin PrioQ!Threads(mutexes[mid].wait_q)

\* I4b: No thread waiting for a semaphore or mutex can be on the run queue
AllWaitingThreadsNotOnRunQueue ==
    /\ \A sid \in InitializedSemaphores:
        \A wait_tid \in PrioQ!Threads(sems[sid].wait_q):
            wait_tid \notin PrioQ!Threads(runq)
    /\ \A mid \in InitializedMutexes:
        \A wait_tid \in PrioQ!Threads(mutexes[mid].wait_q):
            wait_tid \notin PrioQ!Threads(runq)


----------------------------------------

\* The priority of a mutex owning thread must always be higher or equal
\* compared to all waiting threads due to priority inheritance.

OwnerPrioAlwaysAtLeastWaitingPrio ==
    \A mid \in InitializedMutexes:
        \A waiting_tid \in PrioQ!Threads(mutexes[mid].wait_q):
            PrioQ!PrioHigherOrEqual(
                ThreadPrio(mutexes[mid].owner),
                ThreadPrio(waiting_tid)
            )

----------------------------------------

Invariant ==
    /\ RunQLengthAtMostNumberOfTotalThreads
    /\ WaitQLengthAtMostNumberOfTotalThreads
    /\ WaitQueueEntriesValidThreadIDs
    /\ AllReadyThreadsNotOnWaitQueue
    /\ AllWaitingThreadsNotOnRunQueue
    /\ OwnerPrioAlwaysAtLeastWaitingPrio

====
