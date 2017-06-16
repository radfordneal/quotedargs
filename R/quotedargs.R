# Package quotedargs - A way of writing functions that quote their arguments
#
# Copyright Radford M. Neal, 2017.  Distributed under GPL-2 or GPL-3.

# QUOTED_... R FUNCTIONS.  These just call a C function that does the
# work, passing environments that will be needed to get and manipulate
# arguments.  Note that directly passing an argument to .Call would
# result in its being evaluated, which we don't want.

quoted_arg <- function (...)
    .Call ("quoted_arg", environment(), parent.frame(), 
           PACKAGE="quotedargs")

quoted_environment <- function (arg)
    .Call ("quoted_environment", environment(), parent.frame(), 
           PACKAGE="quotedargs")

# Next should probably be in C too for speed, but it can be done using the 
# above functions.

quoted_eval <- function (arg) {
    quoted_arg(arg)
    e <- quoted_environment(arg)
    if (is.null(e)) arg else eval(arg,envir=e)
}

quoted_assign <- function (name, expr, eval.env = parent.frame(), 
                                       assign.env = parent.frame()) {
    .Call ("quoted_assign", environment(), parent.frame(), 
           name, eval.env, assign.env, 
           PACKAGE="quotedargs")
}

# NOTQUOTED FUNCTION.  Calls of notquoted are noticed by quoted_arg,
# and may also be actually evaluated, in which case, notquoted should
# just return its argument (which will be evaluated).

notquoted <- function (x) x