% Package quotedargs - A way of writing functions that quote their arguments
%
% Copyright Radford M. Neal, 2017.  Distributed under GPL-2 or GPL-3.

\name{quotedargs-package}
\alias{quotedargs-package}
\alias{quoted_arg}
\alias{notquoted}
\alias{quoted_eval}
\alias{quoted_environment}
\alias{quoted_assign}
\title{Facility for using quoted arguments}
\description{
This package assists with writing functions that automatically quote
their arguments, but that may also wish to evalute them, in their original
environment.  These quoted arguments can be passed to other functions
that quote their arguments, with proper passing of their quoting environment.
It is also possible to set up a variable so that it looks just like
a quoted argument.

In the simplest applications of this package, one can think of calling
\code{quoted_arg(x)} (see below) as altering the default meaning of a
reference to an argument \code{x} from the value of the actual
argument, with the expression passed for \code{x} accessible via
\code{substitute(x)}, so that instead the default is the expression
passed for \code{x}, with the value accessible via
\code{quoted_eval(x)}, as described below.  But in more complex
applications, the facilities provided by this package are more than
just a convenient change of defaults, as they allow functions that
quote arguments to be combined in ways that would otherwise be difficult.
}
\usage{
quoted_arg (...)
quoted_eval (arg)
quoted_environment (arg)
notquoted (x)

quoted_assign (name, expr, eval.env = parent.frame(),
                           assign.env = parent.frame())
}
\arguments{
\item{...}{names (unquoted) of function arguments that should be quoted}
\item{arg}{the name of a quoted function argument (unquoted)}
\item{x}{any expression.}

\item{name}{the name (as a character string) of a variable to assign to}
\item{expr}{an expression to assign to the variable \code{name}}
\item{eval.env}{the environment in which \code{expr} may be evaluated}
\item{assign.env}{the environment in which to assign to \code{name}}
}
\details{
The \code{quoted_arg} function should be called at the start of a
function that uses quoted arguments, with arguments that are the
(unquoted) names of the arguments that should be quoted. After the
call of \code{quoted_arg}, simple references to these arguments will
give the expressions passed as arguments, rather than the values of
these expressions. 

However, the caller of the function can disable this quoting by
passing \code{notquoted(x)} instead of \code{x}, in which case
\code{x} will be evaluated when \code{quoted_arg} is called, and
references to \code{x} will deliver this value, not the expression.

To obtain the value of a quoted argument, \code{quoted_eval} can be
used. The evaluation will be done in the environment of the quoted
expression.  If \code{quoted_eval} is called more than once for the
same argument, the argument will be evaluated that many times
(possibly with different results).  If the actual argument used
\code{notquoted}, \code{quoted_eval} will simply return the
already-evaluated argument.

The environment used by \code{quoted_eval} can be obtained with
\code{quoted_environment}, which will be \code{NULL} if the actual
argument used \code{notquoted}, and may be \code{emptyenv()} if the
expression is self-evaluating, and hence its evaluation would not
reference an environment.

When a quoted argument is passed as an argument to another function
that quotes that argument, the quoted argument received will be the
argument originally passed, not a quoting of the name of the quoted
argument.

A variable can be set up so that it looks like a quoted argument by
calling \code{quoted_assign}.  By default, the variable created (or
changed) is in the current environment (the parent environment of
\code{quoted_assign}), but this can be changed with the
\code{assign.env} argument.  The \code{expr} argument gives the
expression analogous to an actual argument; if it has the form
\code{notquoted(x)} or is itself a quoted argument, it is handled the
same way as \code{quoted_arg} handles such an argument.  The
environment \code{eval.env} is stored with the assigned expression (in
a ``promise''), and will be used when evaluating this expression if
\code{quoted_eval} is called for the assigned variable.  It defaults
to the current environment (the parent of \code{quoted_assign}),
except that if \code{expr} is itself a quoted argument, the default is
\code{quoted_environment(expr)}.  Finally, if \code{eval.env} is
\code{NULL} or \code{expr} is a call of \code{notquoted} with one
argument, \code{expr} is immediately evaluated in the current
environment, and what is stored in the variable \code{name} will look
like a quoted argument in which the actual argument used
\code{notquoted}.
}
\value{
    \code{quoted_eval} and \code{quoted_environment} return values
    as described above.

    \code{notquoted} returns its argument.

    \code{quoted_arg} and \code{quoted_assign} always return NULL.  
}
\seealso{
    \code{\link{substitute}}, for how to get at the expression passed
    when an argument is not quoted.

    \code{\link{delayedAssign}}, for another function that is somewhat
    analogous to \code{quoted_assign}.
}
\examples{
# A simple example in which both the expression passed and its value
# are used.

showmean <- function (v) {
    quoted_arg(v)
    cat ("Mean of", deparse(v), "is", mean(quoted_eval(v)), "\n")
}

showmean(100+(1:3))                   # Will print 100 + (1:3)
showmean(notquoted(100+(1:3)))        # Will print c(101, 102, 103)

# A function that uses the function above, passing along its quoted 
# argument.

showmeansummary <- function (u) {
    quoted_arg(u)
    cat("Summary: ")
    showmean(u)
}

showmeansummary(100+(1:3))            # Will print 100 + (1:3)
showmeansummary(notquoted(100+(1:3))) # Will print c(101, 102, 103)

u <- v <- 100+(1:3)   # Evaluation of showmeansummary's argument
showmeansummary(u)    #   is done in the global environment, not
showmeansummary(v)    #   that of showmeansummary or showmean


# An illustration of quoted arguments being evaluated many times.

prsim <- function (a,b,n) {
    quoted_arg(a,b)
    cat ("Running simulation to find probability that all\n")
    cat (deparse(a), "are greater than all", deparse(b), "\n")
    count <- 0
    for (i in 1:n) {
        if (min(quoted_eval(a)) > max(quoted_eval(b)))
            count <- count + 1
    }
    count / n
}

set.seed(1)
prsim (rexp(10,0.1), rnorm(10,1), 1000)


# Creating a variable looking that behaves like a quoted argument.

quoted_assign("x",runif(1))

set.seed(1)
cat (paste0("Two evaluations of ",deparse(x),": "),
     quoted_eval(x), quoted_eval(x),
     "\n")


# Examples of when quotation of an argument is passed on.

qfun1 <- function (x) { quoted_arg(x); list(x,quoted_eval(x)) }

qfun2 <- function (y) {
    quoted_arg(y)
    a <- y
    quoted_assign ("b", y)
    list(qfun1(y),qfun1((y)),qfun1(a),qfun1(b))
}

qfun2(1+2)
}
