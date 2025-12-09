---
sidebar_position: 26
---

# Case-splitting on constants

:::info

This use of `case` was introduced in UPLC with protocol version 11 and requires
[Plutus Core version](../essential-concepts/versions#plutus-core-version) `1.1.0`.

:::

In UPLC, it is possible to branch on expressions of certain built-in types, like
`Integer` and `Bool`. This can be done with `case` syntax, which is also used
for [sums-of-products](./encoding#sums-of-products). Using `case` on built-in
values may improve script performance and size. 
The built-in types that `case` currently supports are:

- `bool`
- `unit`
- `integer`
- `list`
- `pair`

In the future, support for `data` is also planned.

For each type, the allowed branches and their order differs. For example, when
casing on `integer`, only non-negative integers can be matched and there is no
catch-all. See [Supported Types](#supported-types) for more detail.

## Compiling to `case` in Plinth

When compiling Plinth code with the `datatypes`
[option](./plinth-compiler-options) set to `BuiltinCasing`, many standard
library functions will be compiled into this use of `case`, such as `fstPair`,
`ifThenElse` and `caseList`. Note that Plinth's `case ... of ...` syntax is not
necessarily compiled to UPLC, as it can be more expressive.

## Supported types

### Bool

Booleans can be used in `case` with either one or two branches, where the first
is the `false` branch. Boolean negation can be written for example as:

```uplc
lam b (case b (con bool True) (con bool False))
```

When only a single branch is provided, script execution will fail when the
boolean evaluates to `true`.

Using a single branch is appropriate when the second branch was supposed to fail
already, saving script size.

### Unit

Needs exactly one branch. If the expression being cased on evaluates to a unit
value, evaluation will continue with the expression in that branch.

```uplc
lam x (case x (con integer 5))
```

Is a function that returns `5` if `x` evaluates to `()` without an error.


### Pair

A built-in pair expects a single branch: a function that takes both components
of the pair.

This example sums the two integer constants in a pair.

```uplc
lam x (case x (lam a (lam b [(builtin addInteger) a b])))
```

### Integer

Casing on integers can be used for non-negative integers only, and a variable
amount of branches may be given. If the expression `e` evaluates to an integer
`i`, the `i`th branch will be evaluated. If there is no branch, `case` will fail.

For example, the following expression evaluates to `con string "c"`

```
case [(builtin addInteger) (con integer 1) (con integer 1)]
  (con string "a")
  (con string "b")
  (con string "c")
```

If the `i`th branch is not given, or `i` is a negative integer, evaluation will
fail:

```
case [(builtin addInteger) (con integer 2) (con integer 2)]
  (con string "a")
  (con string "b")
  (con string "c")
```

Results in

```
An error has occurred:
'case' over a value of a built-in type failed with
'case 4' is out of bounds for the given number of branches: 3
Caused by: 4
```

Note that there is no way to provide a "catch-all" case.

### List

A `case` on built-in lists may be given one or two branches (similar to
booleans), where the first one deals with the cons case, and the second one with
the empty list. If no second branch is given, execution will fail when the list
turns out to be empty.

This example implements the `head` function, which fails if the list if empty.

```uplc
lam xs (case xs (lam y (lam ys y)))
```
