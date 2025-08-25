----------------------------- MODULE Mutexes -----------------------------

\* This module contains a PlusCal specification of Zephyr's Mutex API,
\* under the assumption of a single-core system without interrupts, i.e. no preemption.
\* Threads are modelled as PlusCal processes and identified by a unique natural number.

\* Kernel API functions are modelled as PlusCal procedures.
\* Currently, the test generation relies on a convention, that the label at the beginning
\* of a procedure is the capitalized procedure name (e.g. procedure k_mutex_lock, label K_MUTEX_LOCK)
\* and that, if a thread gets blocked in an API call, it passes to another label inside the
\* procedure that is again the capitalized procedure name, but prefixed with "RESCHED_".
\* See k_mutex_lock for an example.

\* Procedure parameters should have unique names, otherwise the PlusCal translator will rename
\* them, which makes it inconvenient to use them in TLA+ properties.

\* Initially, there is only one running thread in the model. 
\* The remaining threads will be created using a simplified version of k_thread_create,
\* which is also modelled as a PlusCal procedure.

\* Once all threads are initialized, the specification allows any valid sequence of 
\* mutex and semaphore API calls that does not lead to a deadlock.

\* Semaphores are included in the specification. This allows for a greater
\* variety of traces. Without semaphores, there would be no way to take a mutex-owning
\* thread to a waiting state.

\* A few features of the mutex and semaphore APIs are currently not reflected:

\* 1. k_mutex_lock and k_sem_take can only take K_FOREVER and K_NO_WAIT as timeout parameters,
\*    no "real-time" timeout.

\* 2. Static semaphore and mutex initialization is not reflected. They are initialized
\*    dynamically using k_sem_init and k_mutex_init.

EXTENDS Naturals, TLC, Sequences, Integers

LOCAL INSTANCE TLCExt
LOCAL INSTANCE Functions
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE FiniteSetsExt

CONSTANTS
    N_COOP_PRIOS, \* number of cooperative priorities
    N_PREEMPT_PRIOS,  \* number of preemptive priorities
    N_THREADS,      \* Number of threads
    N_MUTEXES,      \* Number of mutexes
    N_SEMAPHORES,   \* Number of semaphores. Semaphores are used to generate more interesting traces.
    NULL,           \* Represents absence of data
    K_FOREVER,
    K_NO_WAIT,
    IDLE_THREAD,     \* Idle thread ID
    ThreadPrio(_),
    ThreadPrioNextState(_)


ASSUME N_THREADS \in Nat \ {0}
ASSUME N_MUTEXES \in Nat \ {0}
ASSUME N_SEMAPHORES \in Nat

PreemptPriorities == 0..N_PREEMPT_PRIOS-1
CoopPriorities == -N_COOP_PRIOS..-1
Priorities == PreemptPriorities \union CoopPriorities
ThreadIDs == 1..N_THREADS
MutexIDs == 1..N_MUTEXES
SemaphoreIDs == 1..N_SEMAPHORES
MainThreadID == CHOOSE t \in ThreadIDs: TRUE
MainThreadInitialPrio == 0

(*--algorithm Mutexes

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

  \* Function (or sequence) that maps mutex IDs to mutex records.
  \* Initially, all mutexes are uninitialized.
  mutexes = [m \in MutexIDs |-> NULL];

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
  ThreadPrioImpl(tid) == threads[tid].prio
  \* TODO: ThreadPrioNextState should probably be defined outside of PlusCal
  ThreadPrioNextStateImpl(tid) == threads'[tid].prio
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

  MutexInitialized(mut_id) == mutexes[mut_id] # NULL
  MutexUninitialized(mut_id) == ~MutexInitialized(mut_id)
  InitializedMutexes == {mut_id \in MutexIDs: MutexInitialized(mut_id)}
  UninitializedMutexes == {mut_id \in MutexIDs: MutexUninitialized(mut_id)}

  TypeInvariant ==
    /\ threads \in Seq([prio: Int] \union {NULL})
    /\ mutexes \in Seq(
            [wait_q: Seq(ThreadIDs), owner: ThreadIDs \union {NULL}, owner_orig_prio: Int, lock_count: Nat] \union {NULL}
        )
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

macro run_mutex_operation_initialized()
    \* Non-deterministically choose a mutex and an operation to run on it.
    \* Run blocking k_mutex_lock only if it does not cause deadlock.
begin
    with mut_id \in InitializedMutexes, allowed_timeouts = (
            IF mutexes[mut_id].lock_count = 0 \/ PrioQ!Len(runq) > 1
                THEN {K_NO_WAIT, K_FOREVER}
                ELSE {K_NO_WAIT} 
            )
    do

        either
            with arg_timeout \in allowed_timeouts do
                call k_mutex_lock(mut_id, arg_timeout);
            end with;
        or
            call k_mutex_unlock(mut_id);
        end either;

    end with;
end macro;

macro run_mutex_operation()
begin
    if (InitializedMutexes = {}) then 
        \* No mutexes initialized, initialize one.
        with mut_id \in UninitializedMutexes do 
            call k_mutex_init(mut_id);
        end with;
    elsif (UninitializedMutexes # {}) then
        \* If some mutexes are uninitialized, either initialize one or run an operation on an initialized one.
        either
            with mut_id \in UninitializedMutexes do 
                call k_mutex_init(mut_id);
            end with;
        or
            run_mutex_operation_initialized();
        end either;
    else
        run_mutex_operation_initialized();
    end if;
end macro;

\* ====================================================================
\* Threac Creation API - not subject to test, only used to create threads initially.

procedure k_thread_create(tid_thread_create, prio, delay_thread_create)
    \* Simplified version of k_thread_create that assumes K_NO_WAIT as delay.
begin
    K_THREAD_CREATE:
    assert ThreadUninitialized(tid_thread_create);
    assert prio \in Priorities /\ delay_thread_create \in {K_NO_WAIT, K_FOREVER};
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
\* Semaphore API - not subject to test, only for blocking threads

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

    with s = sem_give_sem_ptr do

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

\* ====================================================================
\* Mutex API

procedure k_mutex_init(mutex_init_mut_ptr)
begin
    K_MUTEX_INIT:
    assert MutexUninitialized(mutex_init_mut_ptr);

    logical_state_id := logical_state_id + 1;

    mutexes[mutex_init_mut_ptr] := [
        owner |-> NULL,
        owner_orig_prio |-> 0,
        wait_q |-> PrioQ!New,
        lock_count |-> 0
    ];

    ret[self] := 0;

    return;
end procedure;

procedure k_mutex_lock(mutex_lock_mut_ptr, mutex_lock_timeout)
begin
    K_MUTEX_LOCK:
    assert MutexInitialized(mutex_lock_mut_ptr);

    logical_state_id := logical_state_id + 1;

    with m = mutex_lock_mut_ptr do
        if (mutexes[m].lock_count = 0 \/ mutexes[m].owner = current) then
            \* Mutex is not taken or it is already locked by the caller -> reentrant lock.
            mutexes[m].lock_count := mutexes[m].lock_count + 1 ||
            mutexes[m].owner := self ||
            mutexes[m].owner_orig_prio := (
                IF mutexes[m].lock_count = 0 
                THEN ThreadPrio(self) 
                ELSE mutexes[m].owner_orig_prio  \* in case of reentrant lock, thread's prio may already be inherited
            );
            ret[self] := 0;
            return;
        elsif (mutex_lock_timeout = K_NO_WAIT) then
            ret[self] := -Errno!EBUSY;
            return;
        else
            \* Mutex is locked by another thread, need to wait.

            if PrioQ!PrioHigher(ThreadPrio(self), ThreadPrio(mutexes[m].owner)) then
                \* Owning thread has lower priority than self -> Priorty Inheritance

                threads[mutexes[m].owner].prio := ThreadPrio(self);  \* give the current owner my prio

                if (mutexes[m].owner \in PrioQ!Threads(runq)) then

                    \* Remove self and owner from runq, then re-add owner with its new prio.
                    with tmp_runq = PrioQ!DequeueThread(PrioQ!DequeueThread(runq, self), mutexes[m].owner) do
                        runq := PrioQ!EnqueueThreadByPrio(
                            tmp_runq,
                            mutexes[m].owner,
                            threads[mutexes[m].owner].prio
                        );
                    end with;

                else 
                    \* The owner is not in the runq. Only remove self.
                    runq := PrioQ!DequeueThread(runq, self);
                end if;
            else
                runq := PrioQ!DequeueThread(runq, self);
            end if;

            mutexes[m].wait_q := PrioQ!Enqueue(mutexes[m].wait_q, self);

            update_current();

            \* If the current thread is still self after the update,
            \* we can return immediately.
            if (current = self) then
                return;
            end if;

        end if;
    end with;

    \* If we reach here, we need to wait until rescheduled.
    RESCHED_K_MUTEX_LOCK:
    await current = self;
    return;

end procedure;

procedure k_mutex_unlock(mutex_unlock_mut_ptr)
begin
    K_MUTEX_UNLOCK:
    assert MutexInitialized(mutex_unlock_mut_ptr);

    logical_state_id := logical_state_id + 1;

    with m = mutex_unlock_mut_ptr do
        if (mutexes[m].owner = NULL) then 
            \* Mutex is not locked
            ret[self] := -Errno!EINVAL;
            return;
        elsif (mutexes[m].owner # current) then
            \* Calling thread does not hold mutex
            ret[self] := -Errno!EPERM;
            return;
        elsif (mutexes[m].lock_count > 1) then
            \* Reentrant locking. Thread still holds mutex after call.
            mutexes[m].lock_count := mutexes[m].lock_count - 1;
            ret[self] := 0;
            return;
        else 
            \* Unlock mutex

            if PrioQ!Empty(mutexes[m].wait_q) then
                \* No thread is awaiting mutex.
                ret[self] := 0;
                mutexes[m].lock_count := 0 ||
                mutexes[m].owner_orig_prio := 0 ||
                mutexes[m].owner := NULL;
                return;
            else
                \* Mutex is awaited by another thread.
                \* TODO: If the current thread's priority becomes lower, it needs to be re-eqnqueued into runq.
                if PrioQ!PrioHigher(
                    threads[self].prio, 
                    mutexes[m].owner_orig_prio
                ) then

                    \* Restore caller's original prio
                    threads[self].prio := mutexes[m].owner_orig_prio;

                    \* First readd unlocking thread with its original prio to runq.
                    \* Then enqueue the first thread from the wait queue, which becomes ready now.
                    with new_prio_mapping = [tid \in InitializedThreads |-> threads[tid].prio],
                        runq_without_self = PrioQ!DequeueThread(runq, self),
                        runq_self_readded = PrioQ!EnqueueThreadByPrioMapping(runq_without_self, self, new_prio_mapping)
                    do
                        runq := PrioQ!EnqueueThreadByPrioMapping( \* enqueue unlocked thread
                            runq_self_readded,
                            PrioQ!First(mutexes[m].wait_q),
                            new_prio_mapping
                        );
                    end with;

                else
                    runq := PrioQ!Enqueue(runq, PrioQ!First(mutexes[m].wait_q));
                end if;

                ret[self] := 0;

                mutexes[m].owner_orig_prio := ThreadPrio(PrioQ!First(mutexes[m].wait_q)) ||
                mutexes[m].owner := PrioQ!First(mutexes[m].wait_q) ||
                mutexes[m].wait_q := PrioQ!Tail(mutexes[m].wait_q);

                update_current();

                \* If the current thread is still self after the update,
                \* we can return immediately.
                if (current = self) then
                    return;
                end if;
            end if;
        end if;
    end with;
    
    \* If we reach here, we need to wait until rescheduled.
    RESCHED_K_MUTEX_UNLOCK:
    await current = self;
    return;
end procedure;

process thread \in ThreadIDs
    \* Main loop. Only the current thread can run.
    \* As long as not all threads are initialized, thread initialization is prioritized.
    \* Then semaphores and mutexes are initialized.
    \* Then, mutex operations or seamaphore operations are run.
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
            elsif UninitializedSemaphores # {} then
                \* Initialize binary semaphore with count 0.
                with sem_id \in UninitializedSemaphores do
                    call k_sem_init(sem_id, 0, 1);
                end with;
            else
                either
                    run_mutex_operation();
                or
                    with sid \in InitializedSemaphores do
                        if sems[sid].count = 0 /\ PrioQ!Len(runq) = 1 then
                            call k_sem_give(sid)
                        else
                            call k_sem_take(sid, K_FOREVER);
                        end if;
                    end with;
                end either;
            end if;
        end while;
end process;

end algorithm; *)

---------------------------------------------------------
\* Safety Invariants

\* These invariants should always hold, otherwise, there is an error in the model.
MutexInvariants == INSTANCE MutexInvariants
MutexInvariant == MutexInvariants!Invariant

----------------------------------------------------------------------------
\* Test Case Generation

TestGen == INSTANCE MutexTestGen
Alias == TestGen!Alias

-------------------------------------------------------------
\* Exclude logical_state_id from the view, as it is not part of the modelled
\* state space and only used for test case generation.

CustomView == << pc, runq, current, threads, mutexes, ret, stack, 
           tid_thread_create, prio, delay_thread_create, mutex_init_mut_ptr, 
           mutex_lock_mut_ptr, mutex_lock_timeout, mutex_unlock_mut_ptr >>

-------------------------------------------------------------
\* Limit state space exploration by excluding reentrant locks.

CustomConstraint == \A mut_id \in InitializedMutexes: mutexes[mut_id].lock_count < 2

-------------------------------------------------------------
\* False invariants for generating traces

MutexTrapProperties == INSTANCE MutexTrapProperties
TestInvariant == MutexTrapProperties!NeverPriorityInheritance


=============================================================================
