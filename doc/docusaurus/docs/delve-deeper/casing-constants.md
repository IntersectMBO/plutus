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

For each type, the allowed branches and their order differs. See [Supported
Types](#supported-types) for more detail.

## Compiling to `case` in Plinth

When compiling Plinth code with the [option](./plinth-compiler-options)
`datatypes=BuiltinCasing` (which in the future be achieved with
`datatypes=SumsOfProducts), many standard library functions will be compiled
into this use of `case`, such as `fstPair`, `ifThenElse` and `caseList`. Note
that Plinth's `case ... of ...` syntax is not necessarily compiled to UPLC, as
it can be more expressive.

## Supported types

### Bool

Consider the following Plinth code that implements an assertion:

```haskell
assertEx :: Bool -> ()
assertEx = \case
  False -> PlutusTx.error ()
  True -> ()
```

With `datatypes=BuiltinCasing`, it is compiled to the new casing on builtins:

```uplc
\b -> case b error (constr 0 [])
```

:::info

Compare this to the UPLC generated without using `datatypes=BuiltinCasing`.

```uplc
\b -> force (force ifThenElse b (delay (constr 0 [])) (delay error)))
```

This uses the UPLC builtin `ifThenElse`, which requires delaying the branch
arguments, since application in UPLC is strict. The additional forcing and
delaying impacts the size and execution cost.


:::


### Unit

The built-in unit type can be used in a trivial way with `case` in UPLC, which
takes exactly one branch. With `datatypes=BuiltinCasing`, Plinth will compile
the `chooseUnit` built-in into `case`. Consider the following trivial Plinth code:

```haskell
caseUnit :: PlutusTx.BuiltinUnit -> Bool
caseUnit e = PlutusTx.chooseUnit e True
```

Which results in the following UPLC:

```uplc
\e -> case e True
```

UPLC's case on built-in unit requires exactly one branch. If the expression
being cased on evaluates to the unit value, evaluation will continue with the
expression in that branch.

### Pair

To destruct a built-in pair, use `casePair`. It compiles into the `case`
construct. For example:

```haskell
\e -> PlutusTx.casePair e (PlutusTx.+)
```

This compiles into `case` in UPLC, which expects a single branch:

```
lam e (case e (lam x (lam y [(builtin addInteger) x y])))
```

:::info

When compiling without `datatypes=BuiltinCasing`, Plinth's `choosePair` is
compiled into multiple built-in function calls to project out the pair's
components, impacting size and execution cost:

```uplc
(\e -> addInteger (force (force fstPair) e) (force (force sndPair) e))
```

:::

### Integer

To use `case` can also be used for Integers, albeit in a more limited way than 

Casing on integers can be used for non-negative integers only, and a variable
amount of branches may be given. If the expression `e` evaluates to an integer
`i`, the `i`th branch will be evaluated. If there is no branch, `case` will
fail. In Plinth, this can be done with the `caseInteger` function:


```haskell
\x -> caseInteger x ["a", "b", "c"]
```

So when applied to `2`, the expression evaluates to `"c"`. The generated UPLC
will be:

```
lam x (case x (con string "a") (con string "b") (con string "c"))
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

Note that there is no way to provide a "catch-all" case for integers.

:::info

In Plinth, using `caseInteger` with `datatypes=BuiltinCasing` will be compiled into
the above `case` construct in PIR, provided the second argument is given as a
literal list (otherwise this is a compile error).

When not using `datatypes=BuiltinCasing`, Plinth's `caseInteger` is compiled
into a much less efficient implementation that turns the second argument in a
list (of which the representation depends on the chosen `datatypes=` flag), and
does a recursive lookup in that list.


```uplc
(program
   1.1.0
   ((\traceError ->
       (\go x ->
          force
            (force ifThenElse
               (lessThanInteger x 0)
               (delay (traceError "PT6"))
               (delay
                  (go
                     x
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
      (\str -> (\x -> error) (force trace str (constr 0 [])))))
```


```
(program
   1.1.0
   (\x ->
      force
        (force ifThenElse
           (equalsInteger 0 x)
           (delay "a")
           (delay
              (force
                 (force ifThenElse
                    (equalsInteger 1 x)
                    (delay "b")
                    (delay
                       (force
                          (force ifThenElse
                             (equalsInteger 2 x)
                             (delay "c")
                             (delay ((\cse -> case cse [cse]) error)))))))))))
```

:::


### List

A `case` on built-in lists may be given one or two branches (similar to
booleans), where the first one deals with the cons case, and the second one with
the empty list. If no second branch is given, execution will fail when the list
turns out to be empty.

This example implements the `head` function, which fails if the list if empty.

```uplc
lam xs (case xs (lam y (lam ys y)))
```

:::info

When compiling without `datatypes=BuiltinCasing`, Plinth's `caseList` is
compiled into a combination of built-in calls such as `chooseList`, `headList`
and `tailList`. Similarly to booleans, the branches are also thunked, impacting
script size and execution cost.

:::
