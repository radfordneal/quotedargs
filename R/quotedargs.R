# Package quotedargs - A way of writing functions that quote their arguments
#
# Copyright Radford M. Neal, 2017.  Distributed under GPL-2 or GPL-3.


# QUOTED_... R FUNCTIONS.  These just call a C function that does the
# work, passing environments that will be needed to get and manipulate
# arguments.  Note that directly passing an argument to .Call results
# in its being evaluated, which we sometimes don't want.

quoted_arg <- function (...)
    .Call (C_quoted_arg, environment(), parent.frame())

quoted_environment <- function (arg)
    .Call (C_quoted_environment, environment(), parent.frame())

quoted_eval <- function (arg)
    .Call (C_quoted_eval, environment(), parent.frame())

quoted_assign <- function (name, value, eval.env, assign.env = parent.frame()) {
    .Call (C_quoted_assign, environment(), parent.frame(), 
           name, missing(eval.env), assign.env)
    invisible()
}


# NOTQUOTED FUNCTION.  Calls of notquoted are noticed by quoted_arg
# and may also be actually evaluated, in which case, notquoted should
# just return its argument (which will be evaluated).

notquoted <- function (x) x
