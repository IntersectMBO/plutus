---
sidebar_position: 26
---

# Case-splitting on constants

:::info

This use of `case` in UPLC was introduced with protocol version 11 and requires
[Plutus Core version](../essential-concepts/versions#plutus-core-version)
`1.1.0`.

:::

In UPLC, it is possible to branch on expressions of certain built-in types, like
`Integer` and `Bool` using `case` syntax, which is also used
for [sums-of-products](./encoding#sums-of-products). This may improve script performance
and size, compared to older alternatives that use built-in functions.

This page describes the built-in types that are supported in UPLC and how Plinth
developers can benefit from the improved performance.

## Usage from Plinth

:::info

The Plinth compiler option will change from `datatypes=BuiltinCasing` to
`datatypes=SumsOfProducts` in the future.

:::


Plinth developers can benefit from the performance of `case` by enabling the
compiler [option](./plinth-compiler-options) `datatypes=BuiltinCasing`, and
using standard library functions such as `caseList`, `fstPair`.
Note that Plinth's `case ... of ...` syntax is not generally compiled to UPLC,
as it can be more expressive.

## Supported types

The UPLC built-in types that `case` can be used on are:

- `bool`
- `unit`
- `integer`
- `list`
- `pair`

In the future, support for `data` is also planned.

### Bool

The following Plinth code implements a basic assertion:

```haskell
assert :: Bool -> BuiltinUnit
assert False = error ()
assert True = unitval
```

With `datatypes=BuiltinCasing`, it is compiled to the new casing on builtins:

```uplc
\b -> case b [error, ()]
```

In UPLC, booleans can be used in `case` with either one or two branches, where
the first is always the `False` branch. When only a single branch is provided,
script execution will fail when the boolean evaluates to True.

:::info

Compare this to the UPLC that would have been generated otherwise:

```uplc
\b -> force (force ifThenElse b (delay ()) (delay error))
```

This uses the UPLC builtin function `ifThenElse`, which requires delaying the branch
arguments, since application in UPLC is strict. The additional forcing and
delaying impacts the size and execution cost.
:::


### BuiltinUnit

The built-in unit type can be used in a trivial way with `case` in UPLC, which
takes exactly one branch. With `datatypes=BuiltinCasing`, Plinth will compile
`chooseUnit` from `PlutusTx.Builtins.Internal` into `case`. For example:

```haskell
forceUnit :: BuiltinUnit -> Integer
forceUnit e = chooseUnit e 5
```

Which results in the following UPLC:

```uplc
\e -> case e [5]
```

UPLC's case on built-in unit requires exactly one branch. If the expression
being cased on evaluates to the unit value, evaluation will continue with the
expression in that branch.

### BuiltinPair

To destruct a built-in pair, use `casePair` from `PlutusTx.Builtins`. For example:

```haskell
addPair :: BuiltinPair Integer Integer -> Integer
addPair p = casePair p (+)
```

This compiles into `case` in UPLC, which expects a single branch:

```
\p -> case p [(\x y -> addInteger x y)]
```

:::info

When compiling without `datatypes=BuiltinCasing`, Plinth's `choosePair` is
compiled into multiple built-in function calls to project out the pair's
components, impacting size and execution cost:

```uplc
\p -> addInteger (force (force fstPair) p) (force (force sndPair) p)
```

:::

### Integer

Casing on integers in UPLC can be used for non-negative integers only, and a variable
amount of branches may be given. If the expression `e` evaluates to an integer
`i`, the `i`th branch will be evaluated. If there is no branch, `case` will
fail.

In Plinth, use the `caseInteger` function:

```haskell
integerABC :: Integer -> BuiltinString
integerABC i = caseInteger i ["a", "b", "c"]
```

Applying this function to `2` gives `"c"`, while `10` or `-1` produce an error.
Note that the second argument must be given as a literal list, otherwise it is a
Plinth compile error.


Plinth generates the following UPLC:

```
\i -> case i ["a", "b", "c"]
```

In general, if `i`th branch is not given, or `i` is a negative integer, evaluation will
fail. Note that there is no way to provide a "catch-all" case for integers.

:::info

When not using `datatypes=BuiltinCasing`, Plinth's `caseInteger` is compiled
into a much less efficient implementation that turns the second argument in a
list (of which the representation depends on the chosen `datatypes=` flag), and
does a recursive lookup in that list. The above Plinth code is compiled to:


```uplc
(\traceError ->
       (\go i ->
          force
            (force ifThenElse
               (lessThanInteger i 0)
               (delay (traceError "PT6"))
               (delay
                  (go
                     i
                     (constr 1
                        [ "a"
                        , (constr 1
                             ["b", (constr 1 ["c", (constr 0 [])])]) ])))))
         ((\s -> s s)
            (\s ds ds ->
               case
                 ds
                 [ (traceError "PT7")
                 , (\x xs ->
                      force
                        (force ifThenElse
                           (equalsInteger 0 ds)
                           (delay x)
                           (delay
                              ((\x -> s s x) (subtractInteger ds 1) xs)))) ])))
      (\str -> (\x -> error) (force trace str (constr 0 [])))
```
:::


### BuiltinList

A `case` on built-in lists may be given one or two branches (similar to
booleans), where the first one deals with the cons case, and the second one with
the empty list. If no second branch is given, execution will fail when the list
turns out to be empty.

This example implements a `head` function for boolean lists, which fails if the list if empty.

```uplc
head :: BuiltinList Bool -> Bool
head xs = caseList (\_ -> error ()) (\x _ -> x) xs
```

:::info

When compiling without `datatypes=BuiltinCasing`, compilation falls back on
using multiple built-ins, such as `chooseList`, `headList` and `tailList`.
Similarly to booleans, the branches are thunked, impacting script size and
execution cost:

```uplc
(\xs ->
      force
        (force (force chooseList)
           xs
           (delay (\ds -> error))
           (delay ((\x xs ds -> x) (force headList xs) (force tailList xs))))
        (constr 0 []))
```

:::
