# Efficiently evaluating builtin functions in the CK and CEK machines

It's important that builtin evaluation should be efficient in our
Plutus Core evaluators.  There's some machinery known as the constant
application machinery (CAM for short) which takes the name of a
builtin and a list of arguments of some unspecified type `term` which
is required to provide some `Constant`-like constructor which contains
values of built-in types.  `Constant` terms can be converted back into
Haskell values which can be used by the Haskell implementation of a
builtin. Non-`Constant` terms are opaque to builtins and can be fed to
them as arguments, but pass through undigested, as it were.  This
mechanism is described in more detail
[here](../../../language-plutus-core/docs/Builtins.md) and
[here](../../../language-plutus-core/docs/Constant-application.md).

The question considered here is how the evaluators should interact
with the CAM, especially when we're dealing with unsaturated builtins.
The basic problem is how to tell if an application has the required
number of arguments.  In the original version of the CEK machine, this
was handled entirely by the CAM.

### CEK strategy

Recall that the CEK machine uses a stack of _frames_ containing
information about the context surrounding the term currently being
evaluated.  When an application `[M N]` is encountered, firstly `M` is
reduced to a value (`F` say), which is saved in a frame on the stack,
then `N` is reduced to a value `V`, then `F` is applied to `V`: this
is the step that concerns us.

There are three possibilities:

 1. `F` is a lambda term of the form `(lam x t body)`.  In this case,
 evaluation proceeds in the CEK machine by binding `V` to `x` and then
 proceeding to evaluate `body`. (In the CK machine, `V` is substituted
 for every occurrence of `x` in `body`, which is then evaluated).

 2. `F` is an application of a builtin function to a (possibly empty) list of values.

 3. `F` is something else (a constant for example): in this case an error occurs.

Step 2 is the one that has to be efficient.  In the original CEK machine, a function
`termAsPrimIterApp` is called.  This takes a term and checks whether it is a sequence of
type instantiations and applications with the name of a builtin function at the head, for example

```
  [{([builtin b) V₁ V₂] T₁} V₃]
```

If the term is of this form then `termAsPrimIterApp` discards the
types and returns `Just (b, args)` where `b` is the name of the
builtin and `args` is a list of the arguments (and returns `Nothing`
if is is not of this form, leading to case 3 above).  In the original
CEK machine, this information was then passed to the CAM, which
retrieves the Haskell code for the appropriate builtin and applies it
the arguments, leading to one of three responses: `Stuck` if there
were too few arguments, an error if there were too many arguments, and
a `Success` result containing the result of applying the builtin
if there are the correct number of arguments and they have the correct
types.

This process is quite inefficient: it usually requires repeated
applications of `termAsPrimIterApp` and repeated calls to the CAM.

### Saturated builtins

One way to solve this problem is to insist on saturated builtins: the
typechecker can check that all builtin applications have the correct
number of arguments, and the evaluator is provided with an AST node
containing the correct number of arguments, so `termAsPrimIterApp`
isn't required and only a single call to the CAM is required.  On
simple benchmarks involving a lot of builtin applications, this was
substantially faster than the original CEK machine.  However,
saturated builtins complicated matters considerably and we decided not
to pursue them: see [this document](../../../language-plutus-core/docs/Saturatedness.md)
for a consideration of the issues involved.
One important factor was that an alternative version of the CEK
machine allowed us to retain unsaturated builtins but achieve similar
performance to unsaturated builtins.

### The alternative CEK machine
Part of the reason for abandoning saturated builtins was that
James proposed an alternative version of the CEK machine which
looked as if it might be more efficient than the original machine
with respect to environment handling. This involved a new notion of "value"
which Roman observed would allow us to simplify builtin application
by giving us somewhere to store the arguments to which a builtin had
so far been applied.

The original machine dealt with closures: pairs `(V,ρ)` with `V` a value and `ρ`
an environment containing values for the free variables in `V` (and probably
other variables as well: the new machine appeared attractive because it would
reduce the number of irrelevant variables stored in environments).

In James' original proposal, closures were to be replaced with a new kind
of "value":

```
V := con cn
   | abs ɑ (M , ⍴)
   | lam x (M , ρ)
   | iwrap A B V
```

These are similar to, but distinct from, the "values" in the Plutus Core
specification, which are terms that can't be reduced any further.

Roman's proposal was to change this to

```
V := con cn
   | abs ɑ (M , ⍴)
   | lam x (M , ρ)
   | iwrap A B V
   | builtin ρ bn count [types] [V]
```
(we'll call these things "CEK-values")

The `builtin` constructor contains

  * The name `bn` of the builtin
  * The environment `ρ` in effect at the time that `(builtin bn)` was first encountered.
  * A count of the arguments.  This is filled in with the arity of `bn`
    (looked up in a table) when `(builtin b)` was first encountered
  * A list of type arguments
  * A list of term arguments

The lists of arguments are initially empty: whenever a `builtin`
CEK-value is instantiated or applied to an argument the argument is
added to the appropriate list and the count is decremented.  When the
count reaches zero the builtin name and the arguments can be passed
directly to the constant application machinery.

(This technique is slightly fragile because we only count the total
number of type and term arguments, and don't check that type and term
arguments are correctly interleaved.  However, (a) these _will_ be
typed by the typechecker, (b) we'll eventually be moving to an untyped
evaluator where this is less important, and (c) if we really wanted to
be more robust we could keep separate lists of type and term arities,
or (better, but at a slight cost) provide a list of `TypeArg |
TermArg` values, removing the first element every time we encounter an
instantiation or application, and checking that it is of the correct kind.)

This process is clearly much more efficient than that in the original
CEK machine, and in fact enabled the alternative CEK machine with
unsaturated builtins to become competitive with the one with saturated
builtins.


### The CK machine

Unfortunately we can't use the above technique with the CK machine:
that works directly with values as described in the Plutus Core
specification, and there's nowhere to store the argument information.
I've considered a number of ways to fix this.

 * I initially thought we could store the required information
   in a frame.  This is how the CK machine worked with saturated
   builtins, but we can't use the same technique with unsaturated
   builtins.  In the unsaturated case a partially applied builtin
   is a perfectly legitimate value and could be returned by a function
   or supplied as an argument to another function.  This just doesn't
   fit in with the way that stack frames are used.

 * We could modify the notion of value used in the CK machine. This
   might be sensible.  The CK machine and the CEK machine both have two
   main phases: "compute" and "return", the former acting on terms and
   the latter acting on values.  In the CK machine, we've been using
   values of the type described in the Plutus Core specification,
   which are terms with a particular syntactic form.  However, I think
   there's no reason why type of the arguments consumed by the return
   phase have to bear any relation to the term type consumed by the
   compute phase, so this might be the way to go.

 * What I've done for the time being is to modify the CK machine to
   use a variant of the method used in the original CEK machine.
   Whenever we see an application `[M N]` where `M` isn't a lambda,
   we call `termAsPrimIterApp` to check if it's of the correct form,
   and if it is we look up the the arity of the function and compare it
   with the number of arguments; if they match, we hand the application
   off to the CAM.  This is a bit more efficient than the earlier method
   because we only call the CAM once, but it still requires repeated calls
   to the inefficient `termAsPrimIterApp`, which we otherwise don't need.

 * We could modify the `builtin` constructor in the AST to contain a
   list of arguments that it's received so far.  That's probably a
   really bad idea though, since it'd only be there for the benefit of the
   CK machine and it's taking us back towards the problems we had with
   saturated builtins.  Let's not do that.
 

I'm not sure what we want to do here.  How much do we care about the
CK machine these days?  I think we originally had it because it was
pretty simple and easily formalised, and fitted in nicely with the
reduction semantics.  Maybe that's not so important now?

Another issue is that in the specification we've been skating around
exactly how builtin evaluation works, but we'll need to be more
precise (and independent of the implementation language) if and when
we do away with static builtins.  Maybe the machine implementation
should be one that's easily specified.  An argument in favour of the
CK machine was its simplicity, but maybe it's not possible to be very
simple if we deal with builtins properly.

Also, our primary evaluator will eventually be untyped, and it'll
presumably be a CEK machine.  We'll surely still want a typed
evaluator as well though, so maybe that should be the CEK machine as
well.  It's maybe tempting to use the typed CEK machine and make it a
bit more robust by using the `TypeArg | TermArg` thing mentioned above
to count the arities: that'll be slightly less efficient, but we'll
only need it for the typed evaluator, where efficiency isn't paramount.


## Higher-rank builtins

In the specification, builtins are currently allowed to be
polymorphic, but all the type arguments have to precede the term
arguments (ie, all the quantifiers appear at the front).  

We've recently had a discussion about whether we want to allow
type and term arguments to be interleaved, allowing us to
have builtins with higher-rank types (and also non-canonical
rank-one types).  The internal machinery doesn't really care
about this, but it does present some problems.

One possible issue is that if we allow type arguments between term
arguments there's the question of how we erase them.  If we allow such
things, then we can have a polymorphic partially-applied builtin, and
such a thing could be passed to a function which could also accept
type-abstracted lambdas, and such a function would have to deal
uniformly with both possibilities.  The difficulty is that we no longer
have the value restriction, so we have to erase abstractions to
`delay` and apply `force` when type instantiation occurs.  Since
there's no possibility of computation occurring when a
partially-applied builtin is instantiated, it seems strange to
unnecessarily wrap them in a `delay`. [But what happens if the final
argument is a type argument, ie, if a builtin returns a polymorphic
value?  We currently require all builtin arguments to be values and
builtins are supposed to be parametrically polymorphic _and_ return
values, so can a builtin really return something that can compute when
instantiated?  Perhaps it can: maybe we can pass `Λt:*.error` (which
erases to `delay error`) to the identity function?]

Anyway, perhaps we could modify `force` so that it'll act on _any_
value, doing nothing when it's not wrapped in `delay`; we would then
be able to completely erase type arguments to builtins except perhaps
ones at the very end.  (I'm now wondering what would happen if you
force a _term_: could that ever happen?)

Roman has a number of other proposals, including erasing type arguments
of builtins to `()` and prohibiting final quantifiers altogether.

### Do we want higher-rank builtins?

It's maybe worth asking whether we need such things.  Is there a real
use case where they'd be useful?  Do they allow us to compile even
more Haskell into Plutus Core?  It appears that there's not a huge
amount of extra implementation effort involved though, so they
wouldn't be too difficult to support.

One thing that worries me a little is how higher-rank types would
affect the specification.  It might be quite tricky just to write down
a generic instance of such a type, for example.

What about formalisation? Would this complicate things in the Agda
formalisation, or is it simple to do?



