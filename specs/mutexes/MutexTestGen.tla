---- MODULE MutexTestGen ----
EXTENDS TLC, Sequences, Integers, Naturals, TestGenUtils

LOCAL INSTANCE SequencesExt

CONSTANTS
    N_THREADS,      \* Number of threads
    N_SEMAPHORES,   \* Number of semaphores
    N_MUTEXES,   \* Number of semaphores
    NULL,           \* Represents absence of data
    ThreadIDs,
    MainThreadID,
    MainThreadInitialPrio

VARIABLES pc, runq, current, threads, mutexes, sems, ret, logical_state_id, 
          stack
VARIABLES tid_thread_create, prio, delay_thread_create, sem_init_sem_ptr, 
          initial_count, limit, sem_give_sem_ptr, sem_take_sem_ptr, 
          sem_take_timeout, mutex_init_mut_ptr, mutex_lock_mut_ptr, 
          mutex_lock_timeout, mutex_unlock_mut_ptr

-----------------------------------------------
\* Util

CSemaphorePointer(tla_sem_id) == "&sems[" \o ToString(tla_sem_id-1) \o "]"
CMutexPointer(tla_mut_id) == "&mutexes[" \o ToString(tla_mut_id-1) \o "]"
CThreadID(tla_tid) == "thread_ids[" \o ToString(tla_tid-1) \o "]"

StateIDAssertion == 
    EqualityAssertion("state_id", ToString(logical_state_id'))
StateIDUpdate == "state_id++;"

SemaphoreCountAssertion(tla_sem_id) ==
    EqualityAssertion(
        FunctionCall("k_sem_count_get", <<CSemaphorePointer(tla_sem_id)>>),
        ToString(sems'[tla_sem_id].count)
    )

-----------------------------------------------
\* Global definitions

Defines == <<
    "#define NUM_THREADS (" \o ToString(N_THREADS) \o ")",
    "#define NUM_SEMS (" \o ToString(N_SEMAPHORES) \o ")",
    "#define NUM_MUTEXES (" \o ToString(N_MUTEXES) \o ")",
    "#define STACK_SIZE (512 + CONFIG_TEST_EXTRA_STACK_SIZE)"
>>

GlobalVariables == <<
    "K_THREAD_STACK_ARRAY_DEFINE(stack_array, NUM_THREADS, STACK_SIZE);",
    "struct k_thread threads[NUM_THREADS];",
    "k_tid_t thread_ids[NUM_THREADS];",
    "struct k_sem sems[NUM_SEMS];",
    "struct k_mutex mutexes[NUM_MUTEXES];",
    "unsigned int state_id = " \o ToString(logical_state_id) \o ";"
>>

LocalVariables == [tid \in ThreadIDs |-> <<
        "int ret_int;",
        "(void) ret_int;" \* to avoid unused variable warning
    >>
]

InitializationInstructions == <<
    "state_id = " \o ToString(logical_state_id) \o ";",
    "thread_ids[" \o ToString(MainThreadID-1) \o "] = k_current_get();",
    "k_thread_priority_set(_current, " \o ToString(MainThreadInitialPrio) \o "); // set initial threads priority"
>>

K_THREAD_CREATE_TRANSLATION_CONFIG == [
    call |-> <<
        StateIDUpdate,
        \* tid_thread_create = k_thread_create(&threads[0], stack, STACK_SIZE,
        \* thread_entry, NULL, NULL, NULL, prio, 0, K_NO_WAIT);
        (
            LET
                thread_c_idx == ToString(tid_thread_create[current]-1)
                stack_ptr == "stack_array[" \o thread_c_idx \o "]"
                thread_function == "THREAD_" \o thread_c_idx \o "_FUNC"
            IN
                AssignmentStatement(
                    "thread_ids[" \o thread_c_idx \o "]", 
                    FunctionCall(
                        "k_thread_create", <<
                            "&threads[" \o thread_c_idx \o"]",
                            stack_ptr,
                            "STACK_SIZE",
                            thread_function, "NULL", "NULL", "NULL",
                            ToString(prio[current]),
                            "0",
                            "K_NO_WAIT"
                        >>
                    )
                )
        )
    >>,
    local_assertions |-> <<>>,
    global_assertions |-> <<
        StateIDAssertion
    >>
]

K_SEM_INIT_TRANSLATION_CONFIG == [
    call |-> <<
        StateIDUpdate,
        \* ret_int = k_sem_init(&sems[0], 0 , 1);
        AssignmentStatement(
            "ret_int", 
            FunctionCall(
                "k_sem_init", <<
                    CSemaphorePointer(sem_init_sem_ptr[current]),
                    ToString(initial_count[current]),
                    ToString(limit[current])
                >>
            )
        )
    >>,
    local_assertions |-> <<
        EqualityAssertion("ret_int", ToString(ret'[current])),
        SemaphoreCountAssertion(sem_init_sem_ptr[current])
    >>,
    global_assertions |-> <<
        StateIDAssertion
    >>
]

K_SEM_GIVE_TRANSLATION_CONFIG == [
    call |-> <<
        StateIDUpdate,
        \* k_sem_give(&sems[0]);
        FunctionCallStatement(
            "k_sem_give", <<CSemaphorePointer(sem_give_sem_ptr[current])>>
        )
    >>,
    local_assertions |-> <<>>,
    global_assertions |-> <<
        SemaphoreCountAssertion(sem_give_sem_ptr[current]),
        StateIDAssertion
    >>
]

K_SEM_TAKE_TRANSLATION_CONFIG == [
    call |-> <<
        StateIDUpdate,
        \* ret_int = k_sem_take(&sems[0], K_FOREVER);
        AssignmentStatement(
            "ret_int", 
            FunctionCall(
                "k_sem_take", <<
                    CSemaphorePointer(sem_take_sem_ptr[current]),
                    ToString(sem_take_timeout[current])
                >>
            )
        )
    >>,
    local_assertions |-> <<
        EqualityAssertion("ret_int", ToString(ret'[current]))
    >>,
    global_assertions |-> <<
        SemaphoreCountAssertion(sem_take_sem_ptr[current]),
        StateIDAssertion
    >>
]

K_MUTEX_INIT_TRANSLATION_CONFIG == [
    call |-> <<
        StateIDUpdate,
        \* ret_int = k_mutex_init(&mutexes[0]);
        AssignmentStatement(
            "ret_int", 
            FunctionCall(
                "k_mutex_init", <<
                    CMutexPointer(mutex_init_mut_ptr[current])
                >>
            )
        )
    >>,
    local_assertions |-> <<
        EqualityAssertion("ret_int", ToString(ret'[current]))
    >>,
    global_assertions |-> <<
        StateIDAssertion
    >>
]

K_MUTEX_LOCK_TRANSLATION_CONFIG == [
    call |-> <<
        StateIDUpdate,
        \* ret_int = k_mutex_lock(&mutexes[0], K_FOREVER);
        AssignmentStatement(
            "ret_int", 
            FunctionCall(
                "k_mutex_lock", <<
                    CMutexPointer(mutex_lock_mut_ptr[current]),
                    ToString(mutex_lock_timeout[current])
                >>
            )
        )
    >>,
    local_assertions |-> <<
        EqualityAssertion("ret_int", ToString(ret'[current])),
        EqualityAssertion(
            FunctionCall("k_thread_priority_get", <<"_current">>),
            ToString(threads[current].prio)
        )
    >>,
    global_assertions |-> <<
        EqualityAssertion(
            FunctionCall("k_thread_priority_get", <<"_current">>),
            ToString(threads'[current'].prio)
        ),
        StateIDAssertion
    >>
]

K_MUTEX_UNLOCK_TRANSLATION_CONFIG == [
    call |-> <<
        StateIDUpdate,
        \* k_mutex_unlock(&mutexes[0]);
        AssignmentStatement(
            "ret_int", 
            FunctionCall(
                "k_mutex_unlock", <<
                    CMutexPointer(mutex_unlock_mut_ptr[current])
                >>
            )
        )
    >>,
    local_assertions |-> <<
        EqualityAssertion("ret_int", ToString(ret'[current])),
        EqualityAssertion(
            FunctionCall("k_thread_priority_get", <<"_current">>),
            ToString(threads[current].prio)
        )
    >>,
    global_assertions |-> <<
        EqualityAssertion(
            FunctionCall("k_thread_priority_get", <<"_current">>),
            ToString(threads'[current'].prio)
        ),
        StateIDAssertion
    >>
]

-----------------------------------------------

ActionTranslation == 
    CASE pc[current] = "K_THREAD_CREATE" -> K_THREAD_CREATE_TRANSLATION_CONFIG
        [] pc[current] = "RESCHED_K_THREAD_CREATE" -> K_THREAD_CREATE_TRANSLATION_CONFIG
        [] pc[current] = "K_SEM_INIT" -> K_SEM_INIT_TRANSLATION_CONFIG
        [] pc[current] = "K_SEM_GIVE" -> K_SEM_GIVE_TRANSLATION_CONFIG
        [] pc[current] = "RESCHED_K_SEM_GIVE" -> K_SEM_GIVE_TRANSLATION_CONFIG
        [] pc[current] = "K_SEM_TAKE" -> K_SEM_TAKE_TRANSLATION_CONFIG
        [] pc[current] = "RESCHED_K_SEM_TAKE" -> K_SEM_TAKE_TRANSLATION_CONFIG
        [] pc[current] = "K_MUTEX_INIT" -> K_MUTEX_INIT_TRANSLATION_CONFIG
        [] pc[current] = "K_MUTEX_LOCK" -> K_MUTEX_LOCK_TRANSLATION_CONFIG
        [] pc[current] = "RESCHED_K_MUTEX_LOCK" -> K_MUTEX_LOCK_TRANSLATION_CONFIG
        [] pc[current] = "K_MUTEX_UNLOCK" -> K_MUTEX_UNLOCK_TRANSLATION_CONFIG
        [] pc[current] = "RESCHED_K_MUTEX_UNLOCK" -> K_MUTEX_UNLOCK_TRANSLATION_CONFIG
        [] OTHER -> NULL

-----------------------------------------------

ReschedInFunction == (Len(pc[current]) >= Len("RESCHED") /\ SubSeq(pc[current], 1, Len("RESCHED")) = "RESCHED" /\ Len(stack[current]) = 1)

\* Blank line and comment, followed by a k_thread_abort for each thread except the running one
ShutDownInstructions == <<
    "",
    "// shutdown instructions"
    >> \o SetToSeq(
        {FunctionCallStatement("k_thread_abort", <<CThreadID(tid)>>): tid \in ThreadIDs \ {current'}}
    )

CommentStateNumbers == "// transition from state " \o ToString(logical_state_id) \o " to " \o ToString(logical_state_id')
CommentExpectPreemption == "// expect preemption and reschedule to thread " \o ToString(current' - 1)
CommentExpectReschdule == "// expected to be rescheduled from thread " \o ToString(current-1) \o " in transition starting from state " \o ToString(logical_state_id)

\* A function that maps thread IDs to Sequences of instructions that should be executed by them.
Instructions == 
    (
        IF current = current' /\ ~ReschedInFunction THEN
            \* Current is calling an API function and keeps running.
            current :> (
                <<"", CommentStateNumbers>>
                \o ActionTranslation.call 
                \o ActionTranslation.local_assertions 
                \o ActionTranslation.global_assertions
            )
        ELSE IF current # current' THEN
            \* Current is calling an API function and is preempted.
            \* Let the next thread run assertions on the global state.
            current :> (<<"", CommentStateNumbers, CommentExpectPreemption>> \o ActionTranslation.call)
            @@ current' :> <<"", CommentExpectReschdule>> \o ActionTranslation.global_assertions
        ELSE
            \* Current is not calling an API function, but is rescheduled. 
            \* Run assertions of local variables after returning from the function.
            current :> ActionTranslation.local_assertions
    ) @@ [tid \in ThreadIDs |-> <<>>]
    
MidState == [
    runq |-> runq,
    threads |-> threads,
    sems |-> sems,
    mutexes |-> mutexes,
    current |-> current,
    next |-> current',
    ret |-> ret,
    state_id |-> logical_state_id,
    instructions |-> IF ActionTranslation = NULL THEN [tid \in ThreadIDs |-> <<>>] ELSE Instructions,
    pc |-> pc,
    shutdown_instructions |-> ShutDownInstructions
]

FirstState == [
    defines |-> Defines,
    initialization_instructions |-> InitializationInstructions,
    global_variables |-> GlobalVariables,
    local_variables |-> LocalVariables
] @@ MidState

Alias == IF logical_state_id = 1 THEN FirstState ELSE MidState

====
