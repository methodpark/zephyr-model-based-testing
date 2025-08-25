---- ---- MODULE SemaphoreTrapProperties ----
EXTENDS TLC

CONSTANTS
    N_THREADS,      \* Number of threads
    N_SEMAPHORES,   \* Number of semaphores
    NULL,           \* Represents absence of data
    ThreadIDs,
    SemaphoreIDs,
    MainThreadID,
    MainThreadInitialPrio

VARIABLES pc, runq, current, threads, sems, ret, logical_state_id, stack
VARIABLES tid_thread_create, prio, delay_thread_create, sem_init_sem_ptr, 
          initial_count, limit, sem_give_sem_ptr, sem_take_sem_ptr, 
          sem_take_timeout, sem_reset_sem_ptr
vars == << pc, runq, current, threads, sems, ret, logical_state_id, stack, 
           tid_thread_create, prio, delay_thread_create, sem_init_sem_ptr, 
           initial_count, limit, sem_give_sem_ptr, sem_take_sem_ptr, 
           sem_take_timeout, sem_reset_sem_ptr >>

-----------------------------------------------

ThreadExecutesAction(tid, action_label) == current = tid /\ pc[current] = action_label

-----------------------------------------------

KSemInitFails == 
    /\ ThreadExecutesAction(1, "K_SEM_INIT")
    /\ ret'[current] # 0

KSemInitNeverFails == [][~KSemInitFails]_vars

-----------------------------------------------

ThreadGivesAwaitedSem(tid, sem_id) ==
    /\ ThreadExecutesAction(tid, "K_SEM_GIVE")
    /\ sem_give_sem_ptr[tid] = sem_id
    /\ sems[sem_id] # NULL
    /\ sems[sem_id].wait_q # <<>>

Thread1GivesAwaitedSem1 == ThreadGivesAwaitedSem(1, 1)

Thread1NeverGivesAwaitedSem1 == [][~Thread1GivesAwaitedSem1]_vars

====
