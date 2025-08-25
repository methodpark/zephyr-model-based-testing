---- ---- MODULE MutexTrapProperties ----
EXTENDS TLC

CONSTANTS
    N_THREADS,      \* Number of threads
    N_SEMAPHORES,   \* Number of semaphores
    NULL,           \* Represents absence of data
    ThreadIDs,
    SemaphoreIDs,
    MutexIDs,
    MainThreadID,
    MainThreadInitialPrio,
    ThreadPrio(_)

VARIABLES pc, current, runq, threads, mutexes, sems, ret, logical_state_id, 
          stack
VARIABLES tid_thread_create, prio, delay_thread_create, sem_init_sem_ptr, 
          initial_count, limit, sem_give_sem_ptr, sem_take_sem_ptr, 
          sem_take_timeout, mutex_init_mut_ptr, mutex_lock_mut_ptr, 
          mutex_lock_timeout, mutex_unlock_mut_ptr
vars == << pc, current, runq, threads, mutexes, sems, ret, logical_state_id, 
           stack, tid_thread_create, prio, delay_thread_create, 
           sem_init_sem_ptr, initial_count, limit, sem_give_sem_ptr, 
           sem_take_sem_ptr, sem_take_timeout, mutex_init_mut_ptr, 
           mutex_lock_mut_ptr, mutex_lock_timeout, mutex_unlock_mut_ptr >>

-----------------------------------------------
\* Helpers

InitializedMutexes == {mid \in MutexIDs: mutexes[mid] # NULL}

-----------------------------------------------

\* True if the mutex `mutex_id` is owned in the current state,
\* and if the owner's current prio is different than its original prio.
MutexPriorityInheritance(mutex_id) == 
    /\ mutexes[mutex_id] # NULL
    /\ mutexes[mutex_id].owner # NULL
    /\ mutexes[mutex_id].owner_orig_prio # ThreadPrio(mutexes[mutex_id].owner)

\* If checked as an INVARIANT, this will cause TLC to generate a trace,
\* in which priority inheritance is active in the last state.
NeverPriorityInheritance == \A mutex_id \in MutexIDs: ~MutexPriorityInheritance(mutex_id)

====
