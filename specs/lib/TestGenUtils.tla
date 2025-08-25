---- MODULE TestGenUtils ----

\* This module contains utility operators for generating C statements and expressions.
\* These operators are used in the test generation modules to reformat raw TLC counterexamples
\* into C statements that can be added to a test case.

LOCAL INSTANCE Sequences
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals

RECURSIVE ArgList(_)
ArgList(args) == CASE Len(args) = 0 -> ""
                    [] Len(args) = 1 -> Head(args)
                    [] OTHER -> Head(args) \o ", " \o ArgList(Tail(args))

\* Given the function name `fun_name` and a sequence of strings `args`,
\* construct corresponding function call string.
FunctionCall(fun_name, args) == fun_name \o "(" \o ArgList(args) \o ")"

\* A function call as a C-Statement
FunctionCallStatement(fun_name, args) == FunctionCall(fun_name, args) \o ";"

\* A C assignment statement: <var_name> = <rhs_str>;
AssignmentStatement(var_name, rhs_str) == var_name \o " = " \o rhs_str \o ";"

\* Given a variable name and a value as strings, construct 
\* the ZTest Equality Assertion "zassert_equal(<var_name>, <val_str>)";
EqualityAssertion(var_name, val_str) == FunctionCallStatement("zassert_equal", <<var_name, val_str>>)
====
