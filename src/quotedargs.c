/* Package quotedargs - A way of writing functions that quote their arguments.

   Copyright Radford M. Neal, 2017.  Distributed under GPL-2 or GPL-3. */

/* C functions.  These are called from R functions that pass the
   environments that they need access to (in particular to obtain
   arguments that should not be evaluated). */

#include <Rinternals.h>


/* The quotedargs package is implemented by adapting the "promise"
   mechanism used for deferred evaluation of arguments.  An argument
   is normally passed as a promise (and if not, a corresponding
   promise can be created), containing the argument expression and its
   environment, and an initially empty slot for the argument value.
   When the argument is first referenced for its value, the expression
   in its promise will be evaluated ("forced") in its environment, and
   the resulting value stored in the promise, and used for later
   references.

   The quoted_arg function simply fills in the value field of the
   argument's promise with the expression itself, thereby ensuring
   that later references deliver the expression, without it being
   evaluated.  The quoted_environment function can return the
   environment that is still present in the promise, which can also be
   used for quoted_eval.

   Promises that have been set up with quoted_arg (or quoted_assign)
   are marked with QUOTED_MASK (defined below) in their LEVELS (aka,
   general purpose, "gp") field.  This field is also used for PRSEEN,
   but this should not be a conflict, since PRSEEN is used only when a
   promise is forced, which should not happen once the value is filled
   in by quoted_arg.  (PRSEEN is also used in R Core implementations
   of R to avoid an infinite loop when checking missingness, but that
   is a bug, since it can produce incorrect results due to the
   conflict with PRSEEN's use in forcing promises.)  Possible future
   conflicts could be avoided if the R interpreter used only the
   low two bits of LEVELS for PRSEEN, rather than the whole thing.

   When notquoted is used, quoted_arg forces the argument, and sets
   LEVELS to NOTQUOTED_MASK (defined below).  This is necessary for
   the notquoted nature of the argument to propagate when it is passed
   to another function that calls quoted_arg for it.

   To propagate the quoted or notquoted nature of an argument whose
   expression is a symbol, quoted_args needs to look in the
   environment of the arguments's promise to see if that symbol is a
   quoted or notquoted argument (based on LEVELS in its promise), and
   if so, simply copy the information from that promise.  
*/


/* BITS IN LEVELS FOR A PROMISE.  These indicate that the promise is
   for a quoted argument, or for an argument that would have been
   quoted if it weren't that it has the form notquoted(x). */

#define QUOTED_MASK     0x4000
#define NOTQUOTED_MASK  0x2000


/* INSTALLED SYMBOLS NEEDED HERE.  Initialized in R_init_quotedargs. */

static SEXP dotdotdot_symbol;
static SEXP notquoted_symbol;
static SEXP arg_symbol;
static SEXP expr_symbol;


/* ENSURE THAT AN EXPRESSION IS NOT BYTE CODE.  Based on the bytecodeExpr 
   function in eval.c in the R interpreter. */

#ifndef BCODESXP
#define BCODESXP 21  /* handles versions of R before byte compiler existed */
#endif

static SEXP not_byte_code(SEXP e)
{
    if (TYPEOF(e) == BCODESXP)
        return LENGTH (BCODE_CONSTS(e)) > 0 ? VECTOR_ELT (BCODE_CONSTS(e), 0)
                                            : R_NilValue;
    else
        return e;
}


/* TEST WHETHER AN ARGUMENT IS A SYMBOL.  If it is, assign the symbol
   to 'sym' */

static int arg_is_symbol (SEXP prom, SEXP *sym)
{
    SEXP code;

    code = not_byte_code (TYPEOF(prom) == PROMSXP ? PRCODE(prom) : prom);

    if (TYPEOF(code) != SYMSXP)
        return 0;

    *sym = code;

    return 1;
}


/* TEST WHETHER AN ARGUMENT IS A CALL OF NOTQUOTED.  Must also have
   exactly one argument. */

static int notquoted_call (SEXP expr)
{
    return TYPEOF(expr) == LANGSXP 
             && CDR(expr) != R_NilValue && CDDR(expr) == R_NilValue /* 1 arg */
             && CAR(expr) == notquoted_symbol;
}


/* CHECK IF ARGUMENT IS A QUOTED OR NOTQUOTED ARGUMENT.  Looks in the
   given environment for the argumet's promise to figure this out.
   Returns R_NilValue if not a quoted argument, and otherwise the old
   promise. */

static SEXP look_upwards (SEXP expr, SEXP penv)
{
    if (TYPEOF(expr) != SYMSXP)
        return R_NilValue;

    SEXP old_prom = findVarInFrame (penv, expr);
    if (old_prom == R_UnboundValue || TYPEOF(old_prom) != PROMSXP 
          || (LEVELS(old_prom) & (QUOTED_MASK | NOTQUOTED_MASK)) == 0)
        return R_NilValue;

    return old_prom;
}


/* C ROUTINE FOR QUOTED_ARG.  Passed the environment of the R quoted_arg 
   function as 'env', and the environment of the caller of quoted_arg
   as 'cenv'. */

SEXP quoted_arg (SEXP env, SEXP cenv)
{
    if (TYPEOF(env) != ENVSXP || TYPEOF(cenv) != ENVSXP)
        error ("something wrong in quoted_arg");

    /* Get the pairlist of arguments from ... in the quoted_arg function. */

    SEXP dots = findVarInFrame (env, dotdotdot_symbol);
    if (dots == R_NilValue)
        return R_NilValue;
    if (TYPEOF(dots) != DOTSXP)
        error("something wrong in quoted_arg");

    /* Look at each element of ... */

    for ( ; dots != R_NilValue; dots = CDR(dots)) {

        SEXP arg = CAR(dots);
        SEXP sym;

        /* Check that the argument is a symbol (or bytecode for a symbol). */

        if (!arg_is_symbol(arg,&sym)) {
            error("argument of quoted_args is not a symbol");
        }

        /* Look up the symbol in the caller of quoted_arg. */

        SEXP prom = findVarInFrame(cenv,sym);
        if (prom == R_UnboundValue) {
            error(
             "argument of quoted_args not an argument of enclosing function");
        }

        SEXP expr, expr_nbc;

        if (TYPEOF(prom) != PROMSXP) {

            /* Handle the possibility that the argument was passed
               without a promise, as an optimization because it's
               self-evaluating, by creating a promise for it, and
               assigning it back to the formal argument. */

            expr = expr_nbc = prom;
            PROTECT (prom = allocSExp (PROMSXP));
            SET_PRCODE (prom, expr);
            SET_PRVALUE (prom, expr);
            SET_PRENV (prom, R_EmptyEnv);
            defineVar (sym, prom, cenv);
            SET_NAMED (prom, 1);
            SET_NAMED (expr, 2);
        }

        else {

            /* Get the argument expression from the promise, and also
               a version that won't have been byte compiled. */

            PROTECT(prom);
            expr = PRCODE(prom);
            expr_nbc = not_byte_code(expr);
        }

        SEXP old_prom = look_upwards (expr_nbc, PRENV(prom));

        if (old_prom != R_NilValue) {

            /* If the argument is a previously-quoted/notquoted argument,
               copy from the old promise. */

            SET_PRENV (prom, PRENV(old_prom));
            SET_PRCODE (prom, PRCODE(old_prom));
            SET_PRVALUE (prom, PRVALUE(old_prom));

            SETLEVELS (prom, LEVELS(prom) | (LEVELS(old_prom) 
                              & (QUOTED_MASK | NOTQUOTED_MASK)));
        }
        else if (notquoted_call(expr_nbc)) {

            /* If the argument has the form notquoted(x), force it,
               and then flag the promise as NOTQUOTED, which is
               necessary to recognize it if it is passed to another
               function in which it appears in quoted_arg.  

               It's necessary to force the promise because LEVELS is
               used during forcing, conflicting with its use here. */

            (void) eval (prom, R_EmptyEnv); /* forces promise to be evaluated */

            SETLEVELS (prom, LEVELS(prom) | NOTQUOTED_MASK);
        }
        else {

            /* If the argument is being quoted, set the value in its promise
               to the expression, making it look like it's been forced. */

            SET_PRVALUE (prom, PRCODE(prom));
            SET_NAMED (PRVALUE(prom), 2);

            SETLEVELS (prom, LEVELS(prom) | QUOTED_MASK);
        }

        UNPROTECT(1);  /* prom */
    }

    return R_NilValue;
}


/* C ROUTINE FOR QUOTED_ENVIRONMENT.  Passed the environment of the R
   quoted_environment function as 'env', and the environment of the
   caller of quoted_environment as 'cenv'. */

SEXP quoted_environment (SEXP env, SEXP cenv)
{
    if (TYPEOF(env) != ENVSXP || TYPEOF(cenv) != ENVSXP)
        error ("something wrong in quoted_environment");

    /* Get the argument of the quoted_environment function. */

    SEXP arg = findVarInFrame (env, arg_symbol);
    if (arg == R_UnboundValue) {
        error("something wrong in quoted_environment");
    }

    /* Check that the argument is a symbol (or bytecode for a symbol). */

    SEXP sym;
    if (!arg_is_symbol(arg,&sym)) {
        error("argument of quoted_environment is not a symbol");
    }

    /* Look up the symbol in the caller of quoted_environemnt. */

    SEXP prom = look_upwards (sym, cenv);
    if (prom == R_NilValue) {
        error ("argument of quoted_environment is not from "
               "quoted_args or quoted_assign");
    }

    /* Return the environment for a quoted argument, or R NULL otherwise. */

    return LEVELS(prom) & QUOTED_MASK ? PRENV(prom) : R_NilValue;
}


/* C ROUTINE FOR QUOTED_EVAL.  Passed the environment of the R quoted_eval 
   function as 'env', and the environment of the caller of quoted_eval
   as 'cenv'. */

SEXP quoted_eval (SEXP env, SEXP cenv)
{
    if (TYPEOF(env) != ENVSXP || TYPEOF(cenv) != ENVSXP)
        error ("something wrong in quoted_evalt");

    /* Get the argument of the quoted_eval function. */

    SEXP arg = findVarInFrame (env, arg_symbol);
    if (arg == R_UnboundValue) {
        error("something wrong in quoted_eval");
    }

    /* Check that the argument is a symbol (or bytecode for a symbol). */

    SEXP sym;
    if (!arg_is_symbol(arg,&sym)) {
        error("argument of quoted_eval is not a symbol");
    }

    /* Look up the symbol in the caller of quoted_eval. */

    SEXP prom = look_upwards (sym, cenv);
    if (prom == R_NilValue) {
        error ("argument of quoted_eval is not from "
               "quoted_args or quoted_assign");
    }

    if (LEVELS(prom) & NOTQUOTED_MASK) {

        /* Return the value stored in the promise of a nonquoted argument. */

        return PRVALUE(prom);
    }
    else {

        /* Return the result of evaluating the quoted expression in its
           environment. */

        return eval (PRCODE(prom), PRENV(prom));
    }
}


/* C ROUTINE FOR QUOTED_ASSIGN.  Passed the environment of the R quoted_assign
   function as 'env', the environment of the caller of quoted_assign as
   'cenv', and the 'name', 'eval.env', and 'assign.env' arguments.  The
   'expr' argument if obtained unevaluated from 'env'. */

SEXP quoted_assign (SEXP env, SEXP cenv, SEXP name, SEXP evalenv, 
                                                    SEXP assignenv)
{
    if (TYPEOF(env) != ENVSXP || TYPEOF(cenv) != ENVSXP)
        error ("something wrong in quoted_assign");

    /* Check validity of arguments. */

    if (TYPEOF(name) != STRSXP || LENGTH(name) != 1) 
        error ("'name' argument must be a single character string");
    if (evalenv != R_NilValue && TYPEOF(evalenv) != ENVSXP)
        error ("'eval.env' argument must be an environment or NULL");
    if (TYPEOF(assignenv) != ENVSXP)
        error ("'assign.env' argument must be an environment");

    /* Get the 'expr' argument of the quoted_environment function.  It
       will usually be a promise, from which we take the expression,
       but if it's not (maybe a promise was avoided as an optimization
       if it's self-evaluating) just take it as is. */

    SEXP expr = findVarInFrame (env, expr_symbol);
    if (expr == R_UnboundValue) {
        error("something wrong in quoted_assign");
    }

    SEXP expr_nbc = expr;  /* version avoiding byte code, if in promise */

    if (TYPEOF(expr) == PROMSXP) {
        expr = PRCODE(expr);
        expr_nbc = not_byte_code(expr);
    }

    /* Create the promise that will be assigned. */

    SEXP prom;
    PROTECT (prom = allocSExp (PROMSXP));

    SEXP old_prom = look_upwards (expr_nbc, cenv);

    if (old_prom != R_NilValue) {

        /* Copy promise for previously-quoted/notquoted arg to new promise. */

        SET_PRENV (prom, PRENV(old_prom));
        SET_PRCODE (prom, PRCODE(old_prom));
        SET_PRVALUE (prom, PRVALUE(old_prom));
        SETLEVELS (prom, LEVELS(prom) | (LEVELS(old_prom) 
                                          & (QUOTED_MASK | NOTQUOTED_MASK)));
    }
    else if (evalenv == NULL || notquoted_call(expr_nbc)) {

        /* Make the promise look like a notquoted argument. */

        SET_PRENV (prom, R_NilValue);
        SET_PRCODE (prom, expr);
        SET_PRVALUE (prom, eval (expr, evalenv==NULL ? cenv : evalenv));
        SETLEVELS (prom, NOTQUOTED_MASK);
    }
    else {

        /* Make the promise look like a quoted argument. */

        SET_PRENV (prom, evalenv);
        SET_PRCODE (prom, expr);
        SET_PRVALUE (prom, expr);
        SETLEVELS (prom, QUOTED_MASK);
    }

    /* Assign the promise created above. */

    defineVar (install(CHAR(STRING_ELT(name,0))), prom, assignenv);
    SET_NAMED (prom, 1);
    SET_NAMED (PRCODE(prom), 2);
    SET_NAMED (PRVALUE(prom), 2);

    UNPROTECT(1);  /* prom */

    return R_NilValue;
}


/* REGISTER ROUTINES WHEN DLL LOADED. */

#include <R_ext/Rdynload.h>

void R_init_quotedargs (DllInfo *info)
{
    static const R_CallMethodDef call_methods[] = {
        { "C_quoted_arg",         (DL_FUNC) &quoted_arg, 2 },
        { "C_quoted_environment", (DL_FUNC) &quoted_environment, 2 },
        { "C_quoted_eval",        (DL_FUNC) &quoted_eval, 2 },
        { "C_quoted_assign",      (DL_FUNC) &quoted_assign, 5 },
        { NULL, NULL, 0 }
    };

    R_registerRoutines (info, NULL, call_methods, NULL, NULL);
    R_useDynamicSymbols (info, FALSE);

    dotdotdot_symbol = install ("...");
    notquoted_symbol = install ("notquoted");
    arg_symbol       = install ("arg");
    expr_symbol      = install ("expr");
}
