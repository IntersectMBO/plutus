---
sidebar_position: 26
---

# Casing on built-in types in UPLC

Starting with _intra-era hard fork_, UPLC supports a new way of processing
values of built-in types, such as `Integer` and `Data`. The `Case` construct,
which was originally introduced for [sums-of-products](), can now also be used
to case-split on such values.

Using `Case` in UPLC programs can make processing of built-in types more
efficient, for example when dealing with `ScriptContext`, which is encoded using
`Data`.

Depending on the built-in type, a certain order of branches is expected, and not
necessarily all values can be matched using `Case`.

## Bool

For booleans, there are two ways how `Case` may be used. Either with two
branches, where the first is the false branch, and the second the true branch.

```
case b
  <false-branch>
  <true-branch>
```


□ does case evaluate its branches?




, Pair, Uni



## Integer

## List

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
