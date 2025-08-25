----------------------------- MODULE Semaphores -----------------------------

\* This module contains a PlusCal specification of Zephyr's Semaphore API,
\* under the assumption of a single-core system without interrupts, i.e. no preemption.
\* Threads are modeled as PlusCal processes and identified by a unique natural number.

\* Kernel API functions are modelled as PlusCal procedures.
\* Currently, the test generation relies on a convention, that the label at the beginning
\* of a procedure is the capitalized procedure name (e.g. procedure k_sem_take, label K_SEM_TAKE)
\* and that, if a thread gets blocked in an API call, it passes to another label inside the
\* procedure that is again the capitalized procedure name, but prefixed with "RESCHED_".
\* See k_sem_take for an example.

\* Procedure parameters should have unique names, otherwise the PlusCal translator will rename
\* them, which makes it inconvenient to use them in TLA+ properties.

\* Initially, there is only one running thread in the model. 
\* The remaining threads will be created using a simplified version of k_thread_create,
\* which is also modelled as a PlusCal procedure.

\* Once all threads are initialized, the specification allows any valid sequence of 
\* semaphore API calls that does not lead to a deadlock.
\* A few features of the API are currently not reflected:

\* 1. k_sem_take can only take K_FOREVER an K_NO_WAIT as timeout parameters,
\*    no "real-time" timeout.

\* 2. Static semaphore initialization is not reflected. Semaphores are initialized
\*    dynamically using k_sem_init.

EXTENDS Naturals, TLC, Sequences, Integers

LOCAL INSTANCE TLCExt
LOCAL INSTANCE Functions
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE FiniteSetsExt

CONSTANTS
    N_COOP_PRIOS,       \* number of cooperative priorities
    N_PREEMPT_PRIOS,    \* number of preemptive priorities
    N_THREADS,          \* Number of threads
    N_SEMAPHORES,       \* Number of semaphores
    K_SEM_LIMIT_MAX,    \* The maximum semaphore count limit.
    NULL,               \* Represents absence of data
    K_FOREVER,          \* Must be a Model Value
    K_NO_WAIT,          \* Must be a Model Value
    IDLE_THREAD,        \* Idle thread ID, must be a model value
    ThreadPrio(_)       \* An operator mapping a thread ID to the thread's priority in the current state.


ASSUME N_THREADS \in Nat \ {0}          \* At least one thread
ASSUME N_PREEMPT_PRIOS \in Nat \ {0}    \* At least of preemptive priority
ASSUME N_COOP_PRIOS \in Nat             \* Optionally: Cooperative priorities
ASSUME N_SEMAPHORES \in Nat \ {0}       \* At least one semaphore

\* We use the same priority representation as in Zephyr:
\* Cooperative priorities are negative, preemptive priorities positive.
\* Higher values represent lower priorities.
PreemptPriorities == 0..N_PREEMPT_PRIOS-1
CoopPriorities == -N_COOP_PRIOS..-1
Priorities == PreemptPriorities \union CoopPriorities

ThreadIDs == 1..N_THREADS                       \* The set of all thread IDs
SemaphoreIDs == 1..N_SEMAPHORES                 \* The set of all semaphore IDs

MainThreadID == CHOOSE t \in ThreadIDs: TRUE    \* Choose an arbitrary thread as initial thread.
MainThreadInitialPrio == 0                      \* Use a fixed prio 0 for the first thread.

(*--algorithm Semaphores

variables

  \* The currently running thread.
  current = MainThreadID;

  \* Initially, the runq contains only the main thread.
  runq = PrioQ!NewQueueFromThreads({ MainThreadID });

  \* Function (or sequence) that maps thread IDs to thread descriptors.
  \* In this spec, the only information required about a thread is its priority.
  \* Initially, all threads except the main thread are uninitialized (NULL).
  threads = [
    t \in ThreadIDs |->
    IF t = MainThreadID THEN [prio |-> MainThreadInitialPrio] ELSE NULL
  ];

  \* Function (or sequence) that maps semaphore IDs to semaphore records.
  \* Initially, all semaphores are uninitialized.
  sems = [s \in SemaphoreIDs |-> NULL];

  \* Function mapping thread IDs to a return value.
  \* This is necessary because PlusCal procedures (our abstraction of API calls)
  \* cannot return values. `ret` must be a global variable, because one thread
  \* may determine another thread's return value (e.g. k_sem_reset while a thread
  \* is waiting for a semaphore leads to an error returned by k_sem_take).
  ret = [t \in ThreadIDs |-> 0];

  \* This is not needed for the specification itself, only for test generation purposes.
  \* Background: A single API call is represented by 2-3 transitions in a counterexample.
  logical_state_id = 1;

define
  
  \* The operator that is substituted for `ThreadPrio` in imported modules (see cfg-file).
  ThreadPrioImpl(tid) == threads[tid].prio

  Errno == INSTANCE Errno
  PrioQ == INSTANCE PriorityQueues

  ThreadInitialized(tid) == threads[tid] # NULL
  ThreadUninitialized(tid) == ~ThreadInitialized(tid)
  InitializedThreads == {tid \in ThreadIDs: ThreadInitialized(tid)}
  UninitializedThreads == {tid \in ThreadIDs: ThreadUninitialized(tid)}

  SemaphoreInitialized(sem_id) == sems[sem_id] # NULL
  SemaphoreUninitialized(sem_id) == ~SemaphoreInitialized(sem_id)
  InitializedSemaphores == {sid \in SemaphoreIDs: SemaphoreInitialized(sid)}
  UninitializedSemaphores == {sid \in SemaphoreIDs: SemaphoreUninitialized(sid)}

  TypeInvariant ==
    /\ threads \in Seq([prio: Int] \union {NULL})
    /\ sems \in Seq(
            [wait_q: Seq(ThreadIDs), limit: Nat, count: Nat] \union {NULL}
        )
    /\ runq \in Seq(ThreadIDs)
    /\ ret \in [ThreadIDs -> Int]
    /\ current \in (ThreadIDs \union {IDLE_THREAD})
end define

macro update_current()
    \* Update the current thread based on the run queue.
    \* Should be used after any operation that may change the run queue.
begin
    if PrioQ!Empty(runq) then
        current := IDLE_THREAD;
    else
        \* If the current thread is cooperative and in the runq, do not preempt it.
        if ~(threads[current].prio < 0 /\ self \in PrioQ!Threads(runq)) then
            current := PrioQ!First(runq);
        end if;
    end if;
end macro;

macro run_k_sem_init(sem_id)
    \* Non-deterministically choose an initial count and limit and call the
    \* k_sem_init procedure for `sem_id`. Allow also invalid arguments, e,g,
    \* a limit of 0 or an initial count greater than the limit.
begin
    with limit_arg \in 0..K_SEM_LIMIT_MAX do
        with init_count_arg \in 0..K_SEM_LIMIT_MAX+1 do
            call k_sem_init(sem_id, init_count_arg, limit_arg);
        end with;
    end with;
end macro;

macro run_semaphore_operation_initialized()
    \* Non-deterministically choose a semaphore and an operation to run.
    \* Run blocking k_sem_take only if it does not cause deadlock.
begin
    with sid \in InitializedSemaphores do
        if (sems[sid].count > 0 \/ PrioQ!Len(runq) > 1) then
            either
                with timeout_arg \in {K_NO_WAIT, K_FOREVER} do
                    call k_sem_take(sid, timeout_arg)
                end with;
            or
                call k_sem_give(sid);
            or
                call k_sem_reset(sid);
            end either;
        else 
            either
                call k_sem_take(sid, K_NO_WAIT)
            or
                call k_sem_give(sid);
            or
                call k_sem_reset(sid);
            end either;
        end if;
    end with;
end macro;

macro run_semaphore_operation()
    \* If there are no initialized semaphores, initialize one.
    \* If there are some uninitialized semaphores, either initialize one,
    \* or non-deterministically choose an initialized semaphore and an operation to run.
begin
    if (InitializedSemaphores = {}) then 
        \* If no semaphores are initialized, initialize one.
        with sem_id \in UninitializedSemaphores do 
            run_k_sem_init(sem_id);
        end with;
    elsif (UninitializedSemaphores # {}) then
        \* If some semaphores are uninitialized, either initialize one or run an operation on an initialized semaphore.
        either
            with sem_id \in UninitializedSemaphores do 
                run_k_sem_init(sem_id);
            end with;
        or
            run_semaphore_operation_initialized();
        end either;
    else
        run_semaphore_operation_initialized();
    end if;
end macro;

procedure k_thread_create(tid_thread_create, prio, delay_thread_create)
    \* Simplified version of k_thread_create that assumes K_NO_WAIT as delay.
begin
    K_THREAD_CREATE:
    assert ThreadUninitialized(tid_thread_create);
    assert prio \in Priorities;
    assert delay_thread_create = K_NO_WAIT;

    logical_state_id := logical_state_id + 1;

    threads[tid_thread_create] := [prio |-> prio];
    runq := PrioQ!EnqueueThreadByPrio(runq, tid_thread_create, prio);
    ret[self] := tid_thread_create;

    update_current();

    if (current = self) then
        \* If self is still the current thread after the update, we can return immediately.
        return;
    else 
        \* Otherwise, we need to wait until rescheduled.
        RESCHED_K_THREAD_CREATE:
        await current = self;
        return;
    end if;
end procedure;

\* ====================================================================
\* Semaphore API

procedure k_sem_init(sem_init_sem_ptr, initial_count, limit)
begin
    K_SEM_INIT:
    assert SemaphoreUninitialized(sem_init_sem_ptr);
    
    logical_state_id := logical_state_id + 1;

    if (limit > 0 /\ initial_count <= limit) then
        ret[self] := 0;
        sems[sem_init_sem_ptr] := [
            wait_q |-> PrioQ!New,
            count |-> initial_count,
            limit |-> limit
        ];
        return;
    else
        ret[self] := -Errno!EINVAL;
        return;
    end if;
end procedure;

procedure k_sem_give(sem_give_sem_ptr)
begin
    K_SEM_GIVE:
    assert SemaphoreInitialized(sem_give_sem_ptr);

    logical_state_id := logical_state_id + 1;

    with s = sem_give_sem_ptr do  \* rename parameter for better readability

        if (PrioQ!Empty(sems[s].wait_q)) then
            sems[s].count := Min({sems[s].count + 1, sems[s].limit});
            return;
        else
            with next_thread = PrioQ!First(sems[s].wait_q) do
                ret[next_thread] := 0;
                runq := PrioQ!Enqueue(runq, next_thread);
                sems[s].wait_q := PrioQ!Tail(sems[s].wait_q);
            end with;

            update_current();
            
            \* If the current thread is still self after the update, we can return immediately.
            if (current = self) then
                return;
            end if;

        end if;
    end with;

    \* If we reach here, we need to wait until rescheduled.
    RESCHED_K_SEM_GIVE:
    await current = self;
    return;

end procedure;

procedure k_sem_take(sem_take_sem_ptr, sem_take_timeout)
begin
    K_SEM_TAKE:
    assert SemaphoreInitialized(sem_take_sem_ptr);

    logical_state_id := logical_state_id + 1;

    with s = sem_take_sem_ptr do
        if (sems[s].count > 0) then
            sems[s].count := sems[s].count - 1;
            ret[self] := 0;
            return;
        elsif (sem_take_timeout = K_NO_WAIT) then
            ret[self] := -Errno!EBUSY;
            return;
        else
            runq := PrioQ!DequeueThread(runq, self);
            sems[s].wait_q := PrioQ!Enqueue(sems[s].wait_q, self);

            update_current();

            \* If the current thread is still self after the update, we can return immediately.
            if (current = self) then
                return;
            end if;

        end if;
    end with;

    \* If we reach here, we need to wait until rescheduled.
    RESCHED_K_SEM_TAKE:
    await current = self;
    return;
    
end procedure;

procedure k_sem_reset(sem_reset_sem_ptr)
begin
    K_SEM_RESET:
    assert SemaphoreInitialized(sem_reset_sem_ptr);

    logical_state_id := logical_state_id + 1;

    with s = sem_reset_sem_ptr do
        
        \* Set return values for all threads waiting on the semaphore
        ret := [tid \in PrioQ!Threads(sems[s].wait_q) |-> -Errno!EAGAIN] @@ ret;

        \* Merge the waiting queue with the run queue.
        \* This is equivalent to iteratively takting the first thread from the waitq and adding it to runq.
        runq := PrioQ!Merge(runq, sems[s].wait_q);

        \* Reset the semaphore state
        sems[s].count := 0 ||
        sems[s].wait_q := PrioQ!New;

        update_current();

        \* If the current thread is still self after the update, we can return immediately.
        if (current = self) then
            return;
        end if;
    end with;

    \* If we reach here, we need to wait until rescheduled.
    RESCHED_K_SEM_RESET:
    await current = self;
    return;

end procedure;


process thread \in ThreadIDs
    \* Main loop. Only the current thread can run.
    \* As long as not all threads are initialized, thread initialization is prioritized.
    \* Then semaphore operations are run.
begin
    LOOP:
        while TRUE do
            await self = current; \* Wait until the scheduler dispatches this thread.

            if UninitializedThreads # {} then
                \* Create a new thread with any priority.
                with t \in UninitializedThreads do
                    with p \in Priorities do 
                        call k_thread_create(t, p, K_NO_WAIT);
                    end with;
                end with;
            else
                run_semaphore_operation();
            end if;
        end while;
end process;

end algorithm; *)

---------------------------------------------------------
\* Safety Invariants

\* These invariants should always hold, otherwise, there is an error in the model.
SemaphoreInvariants == INSTANCE SemaphoreInvariants
SemaphoreInvariant == SemaphoreInvariants!SemaphoreInvariant

---------------------------------------------------------
\* Test Case Generation

\* Using an alias, we can reformat counterexample state such that they contain
\* C statements to be added to a ZTEST test case. Essentially, this Alias
\* maps PlusCal actions (e.g. K_SEM_TAKE) to the corresponding C statements
TestGen == INSTANCE SemaphoreTestGen
Alias == TestGen!Alias

-------------------------------------------------------------
\* Exclude logical_state_id from the view

CustomView == << pc, runq, current, threads, sems, ret, stack, 
           tid_thread_create, prio, delay_thread_create, sem_init_sem_ptr, 
           initial_count, limit, sem_give_sem_ptr, sem_take_sem_ptr, 
           sem_take_timeout, sem_reset_sem_ptr >>

-------------------------------------------------------------
\* False invariants for generating traces

TrapProperties == INSTANCE SemaphoreTrapProperties
TestInvariant == logical_state_id < 10
TestProperty == TrapProperties!KSemInitNeverFails

=============================================================================
