---
sidebar_position: 26
---

# TODO

□ figure out how case on data will work
□ Figure out how `case ... of ...` is compiled for built-in types.
□ Run all the examples with `uplc` command line
□ Add flag name below (now named TODO)
□ test what happens in uplc if you oversaturate one of the branches of a case on
SOP (this is the main motivation of multilambdas)

# Casing on built-in types in UPLC

Starting with (HARD FORK NAME HERE), UPLC supports a new way of processing
values of some built-in types, such as `Integer` and `Data`. The `case`
construct, originally introduced with [sums-of-products](), can also be used to
split on values of these built-in types.

Using `case` in UPLC may improve script performance and size, for example when
dealing with `ScriptContext`, which is encoded using `Data`. Even for types like
`Bool`, it may result in smaller script size, compared to built-in functions
like `ifThenElse`.

The currently supported built-in types that `case` supports are:

- `unit`
- `bool`
- `integer`
- `data`
- `list`
- `pair`

However, the branching may be subject to some constraints. For example, when
casing on `integer`, only non-negative integers can be matched and there is no
catch-all.

In Plinth, when using the TODO flag, many standard library functions will be
compiled into UPLC's `case`, such as `fstPair`, `ifThenElse` and `caseList`.
Note that Plinth's `case ... of ...` syntax is not necessarily compiled to UPLC,
as it can sometimes be more expressive.


## Bool

Booleans can be used in `case` with either one or two branches, where the first
is the `false` branch. Boolean negation can be written for example as:

```uplc
lam b (case b false true)
```

When only a single branch is provided, script execution will fail when the
boolean evaluates to `true`.

Using a single branch is appropriate when the second branch was supposed to fail
already, saving script size.

## Unit

Needs exactly one branch. If the expression being cased on evaluates to a unit
value, evaluation will continue with the expression in that branch.

```uplc
lam x (case x (con integer 5))
```

Is a function that returns `5` if `x` evaluates to `()` without an error.


## Pair

A built-in pair expects a single branch that is a function with two arguments.
This example implements the swap function:

```uplc
lam x (case x (lam a (lam b (con pair b a))))
```

## Integer

Casing on integers can be used for non-negative integers only, and a variable
amount of branches may be given:

```
case e
  branch_0
  branch_1
  ...
  branch_n
```

If the expression `e` evaluates to an integer `i`, `branch_i` will be evaluated.
If that branch is not given (or `i` is negative), evaluation will fail.

Note that there is no way to provide a "catch-all" case.

## List

A `case` on built-in lists may be given one or two branches (similar to
booleans), where the first one deals with the cons case, and the second one with
the empty list. If no second branch is given, execution will fail when the list
turns out to be empty.

This example implements the `head` function:

```uplc
lam xs (case xs (lam y (lam ys (y)))
```

## Data

When using `case` on values of the `data` type, only `Constr` constructors can
be matched, similar to how `case` works on
[sums-of-products](./encoding#sums-of-products).

```uplc
```


## Algebraic datatypes

Datatypes defined using `data` can be compiled with different encodings (see
[Encoding Data Types in UPLC](./encoding)). Consequently, a `case` expression in
Plinth will generate different UPLC.

### SOP Encoding (Sums-of-products)

This is the default for ADTs. The resulting UPLC will uses UPLC's `case` syntax, see the [SOP example](./encoding#sums-of-products).

### Scott Encoding

When enabling this encoding, the resulting UPLC will use a polymorphic matching
function of the Scott encoding, see the [Scott Encoding
example](encoding#scott-encoding).



# GHC's pattern match compiler

Plinth supports for most pattern matching features of GHC, because it uses GHC's
desugaring pass. Complex patterns are generally transformed into nested `case`
expressions. The general algorithm for compiling pattern matching is described
in [The Implementation of Functional Programming Languages, Chapter
4](https://www.microsoft.com/en-us/research/wp-content/uploads/1987/01/slpj-book-1987-small.pdf).
More detail about language extensions regarding pattern matching can be found in
the [GHC User
Guide](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/patterns.html).
