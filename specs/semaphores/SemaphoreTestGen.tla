---- MODULE SemaphoreTestGen ----

\* This module contains the configuration for generating test cases for Zephyr's semaphore API
\* from traces coming from the Semaphores PlusCal specification.

\* For every API call, there is a corresponding PlusCal label (e.g. K_SEM_TAKE).
\* For each of those labels, we define three sequences of instructions:

\* 1) call: the C statements that perform the API call and trigger the state transition
\* 2) global_assertions: the assertions on global state that should hold after the API call,
\*    regardless of which thread is running
\* 3) local_assertions: the assertions on local state (currently only return values) that should 
\*    hold once the caller of an API function resumes execution.

\* Additionally, we define global variables, preprocessor defines, and initialization instructions,
\* that the initial thread must execute before starting the test.


EXTENDS TLC, Sequences, Integers, Naturals, TestGenUtils

LOCAL INSTANCE SequencesExt

CONSTANTS
    N_THREADS,      \* Number of threads
    N_SEMAPHORES,   \* Number of semaphores
    NULL,           \* Represents absence of data
    ThreadIDs,      \* Set of thread IDs
    SemaphoreIDs,   \* Set of semaphore IDs
    MainThreadID,   \* The ID of the main thread
    MainThreadInitialPrio \* The initial priority of the main thread


\* Variables are copied from the (translated) Semaphores PlusCal specification.
VARIABLES pc, runq, current, threads, sems, ret, logical_state_id, stack
VARIABLES tid_thread_create, prio, delay_thread_create, sem_init_sem_ptr, 
          initial_count, limit, sem_give_sem_ptr, sem_take_sem_ptr, 
          sem_take_timeout, sem_reset_sem_ptr

-----------------------------------------------
\* Global definitions

Defines == <<
    \* Define macros for the number of threads and semaphoes.
    "#define NUM_THREADS (" \o ToString(N_THREADS) \o ")",
    "#define NUM_SEMS (" \o ToString(N_SEMAPHORES) \o ")",

    \* The stack size is required for thread creation.
    "#define STACK_SIZE (512 + CONFIG_TEST_EXTRA_STACK_SIZE)"
>>

GlobalVariables == <<
    \* Define stack arrays and stack descriptors.
    "K_THREAD_STACK_ARRAY_DEFINE(stack_array, NUM_THREADS, STACK_SIZE);",
    "struct k_thread threads[NUM_THREADS];",

    \* Use an additional array to store thread IDs returned by k_thread_create
    \* and the thread ID of the main thread.
    "k_tid_t thread_ids[NUM_THREADS];",

    \* Array of semaphores
    "struct k_sem sems[NUM_SEMS];",

    \* The state_id will be used for checking the scheduling order.
    "unsigned int state_id = " \o ToString(logical_state_id) \o ";"
>>

\* Every thread gets a local variable ret_int to store return values of API calls.
LocalVariables == [tid \in ThreadIDs |-> <<
        "int ret_int;",
        "(void) ret_int;" \* to avoid unused variable warning
    >>
]

\* Before running the first transition, the main thread:
\* 1) initializes the state_id variable 
\* 2) stores its thread ID in thread_ids array
\* 3) sets its initial priority to the one defined in the PlsuCal spec
InitializationInstructions == <<
    "state_id = " \o ToString(logical_state_id) \o ";",
    "thread_ids[" \o ToString(MainThreadID-1) \o "] = k_current_get();",
    "k_thread_priority_set(_current, " \o ToString(MainThreadInitialPrio) \o "); // set initial threads priority"
>>

-----------------------------------------------
\* Helpers

\* Semaphore ID 1 becomes &sems[0]
CSemaphorePointer(tla_sem_id) == "&sems[" \o ToString(tla_sem_id-1) \o "]"

\* Thread 1 becomes thread_ids[0]
CThreadID(tla_tid) == "thread_ids[" \o ToString(tla_tid-1) \o "]"

\* E.g. "zassert_equal(k_sem_count_get(&sems[0]), 1);"
SemaphoreCountAssertion(sem_id) == 
    EqualityAssertion(
        FunctionCall("k_sem_count_get", <<CSemaphorePointer(sem_id)>>),
        ToString(sems'[sem_id].count)
    )

StateIDAssertion == 
    EqualityAssertion("state_id", ToString(logical_state_id'))
StateIDUpdate == "state_id++;"

-----------------------------------------------
\* Translation configurations for PlusCal actions aka labels

\* For K_THREAD_CREATE, we generate two statements:
\* 1) An increment of state_id as we are transitioning to the next state
\* 2) The call to k_thread_create. The returned thread ID is stored in thread_ids array.
K_THREAD_CREATE_TRANSLATION_CONFIG == [
    call |-> <<
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
        \* Check the scheduling order.
        StateIDAssertion
    >>
]

K_SEM_INIT_TRANSLATION_CONFIG == [
    call |-> <<
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
        \* Check the return value of k_sem_init
        EqualityAssertion("ret_int", ToString(ret'[current]))
    >> \o (
        IF sems'[sem_init_sem_ptr[current]] # NULL 
        THEN <<
                \* Check the semaphore count
                SemaphoreCountAssertion(sem_init_sem_ptr[current])
            >>
        ELSE <<>>
    ),
    global_assertions |-> <<
        \* Check the scheduling order.
        StateIDAssertion
    >>
]

K_SEM_GIVE_TRANSLATION_CONFIG == [
    call |-> <<
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
    
K_SEM_RESET_TRANSLATION_CONFIG == [
    call |-> <<
        \* k_sem_reset(&sems[0]);
        FunctionCallStatement(
            "k_sem_reset", <<CSemaphorePointer(sem_reset_sem_ptr[current])>>
        )
    >>,
    local_assertions |-> <<>>,
    global_assertions |-> <<
        SemaphoreCountAssertion(sem_reset_sem_ptr[current]),
        StateIDAssertion
    >>
]
-----------------------------------------------

ActionTranslation == 
    \* The translation configuration for the action taken in the current transition.
    \* By convention, an action label prefixed with "RESCHED_" indicates that
    \* the calling thread was blocked and is now being rescheduled.
    CASE pc[current] = "K_THREAD_CREATE" -> K_THREAD_CREATE_TRANSLATION_CONFIG
        [] pc[current] = "RESCHED_K_THREAD_CREATE" -> K_THREAD_CREATE_TRANSLATION_CONFIG
        [] pc[current] = "K_SEM_INIT" -> K_SEM_INIT_TRANSLATION_CONFIG
        [] pc[current] = "K_SEM_GIVE" -> K_SEM_GIVE_TRANSLATION_CONFIG
        [] pc[current] = "RESCHED_K_SEM_GIVE" -> K_SEM_GIVE_TRANSLATION_CONFIG
        [] pc[current] = "K_SEM_TAKE" -> K_SEM_TAKE_TRANSLATION_CONFIG
        [] pc[current] = "RESCHED_K_SEM_TAKE" -> K_SEM_TAKE_TRANSLATION_CONFIG
        [] pc[current] = "K_SEM_RESET" -> K_SEM_RESET_TRANSLATION_CONFIG
        [] pc[current] = "RESCHED_K_SEM_RESET" -> K_SEM_RESET_TRANSLATION_CONFIG
        [] OTHER -> NULL

-------------------------------------------------------------

\* TRUE iff this is a reschedule action
ReschedInFunction == (Len(pc[current]) >= Len("RESCHED") /\ SubSeq(pc[current], 1, Len("RESCHED")) = "RESCHED" /\ Len(stack[current]) = 1)

\* Helpers for adding comments to the ZTEST test case
CommentStateNumbers == "// transition from state " \o ToString(logical_state_id) \o " to " \o ToString(logical_state_id')
CommentExpectPreemption == "// expect preemption and reschedule to thread " \o ToString(current' - 1)
CommentExpectReschedule == "// expected to be rescheduled from thread " \o ToString(current-1) \o " in transition starting from state " \o ToString(logical_state_id)

\* Shutdown instructions: Instructions to execute in a state if it is the last one in the trace.
\* Blank line and comment, followed by a k_thread_abort for each thread except the running one
ShutDownInstructions == <<
    "",
    "// shutdown instructions"
    >> \o SetToSeq(
        {FunctionCallStatement("k_thread_abort", <<CThreadID(tid)>>): tid \in ThreadIDs \ {current'}}
    )

\* A function that maps thread IDs to Sequences of instructions that should be executed by them.
\* This way, every state contains the information, which statements should be added to which thread.
Instructions == 
    (
        IF current = current' /\ ~ReschedInFunction THEN
            \* Current is calling an API function and keeps running.
            \* Add a comment, increment the state id, and trigger the API call.
            \* Then, run assertions on local and global state.
            current :> (
                <<"", CommentStateNumbers, StateIDUpdate>>
                \o ActionTranslation.call 
                \o ActionTranslation.local_assertions 
                \o ActionTranslation.global_assertions
            )
        ELSE IF current # current' THEN
            \* Current is calling an API function and is preempted.
            \* Let the next thread run assertions on the global state.
            current :> (<<"", CommentStateNumbers, CommentExpectPreemption, StateIDUpdate>> \o ActionTranslation.call)
            @@ current' :> <<"", CommentExpectReschedule>> \o ActionTranslation.global_assertions
        ELSE
            \* Current is not calling an API function, but is returning from a previous, blocking call. 
            \* Run assertions of local variables after returning from the function.
            current :> ActionTranslation.local_assertions
    ) @@ [tid \in ThreadIDs |-> <<>>]

MidState == [
    runq |-> runq,
    threads |-> threads,
    sems |-> sems,
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
