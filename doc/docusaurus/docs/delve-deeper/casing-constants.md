---
sidebar_position: 26
---

# Casing on built-in types in UPLC

Starting with _intra-era hard fork_, UPLC supports a new way of processing
values of some built-in types, such as `Integer` and `Data`. The `case`
construct, which was originally introduced for [sums-of-products](), can also be
used to case-split on such values.

Using `case` in UPLC programs can make processing of built-in types more
efficient, for example when dealing with `ScriptContext`, which is encoded using
`Data`. Even types like `Bool`

Depending on the built-in type, a certain order and amount of branches is
expected, and not necessarily all values can be matched using `case`.

## Bool

Booleans can be used in `case` with one or two branches, where the first is the
false branch. Boolean negation can be written as:

```
\b ->
  case b
    false
    true
```

When only one branch is provided, script execution will fail when the boolean
evaluates to `true`.

## Unit

Needs exactly one branch. If the expression being cased on evaluates to a unit
value, evaluation will continue with the expression in that branch.

## Pair

A built-in pair expects a single branch that is a function with two arguments

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

If the expression e evaluates to an integer `i`, `branch_i` will be evaluated.
If that branch is not given (or `i` is negative), execution will fail.

Note that there is no way to provide a "catch-all" case.

## List

A `case` on built-in lists may be given one or two branches (similar to
booleans), where the first one deals with the cons case, and the second one with
the empty list. If no second branch is given, execution will fail when the list
turns out to be empty.

## Data



# How to use built-in casing in Plinth

Compiler flag, functions.


# Pattern matching and Case

When you use pattern matching in Plinth, such as in a `case` expression, the
generated UPLC code will depend on the type of the value being matched on.

□ Is this true or only on the UPLC level, i.e. does the compiler compile into
case or something else for built-in datatypes. For example, casing on integers
is limited to non-negative branches, and BuiltinData only to Data.Constr

Usage in Plinth (if builtincasing flag):
(searching for BuiltinCasing)
- Bool matcher

"built-in terms" (not built-in functions apparently, for those see below)

- casePair (defineBuiltinTerm)
- caseList (defineBuiltinTerm)

Built-in functions that are mapped to case instead of their built-in:
- ifThenElse
- fstPair
- sndPair
- chooseUnit

## Case on built-in datatypes

As of ..., pattern matching of most built-in types

### Booleans

### Integers

### BuiltinData

Only works on Data.Constr constructors

□ TODO: how will case be handled


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
