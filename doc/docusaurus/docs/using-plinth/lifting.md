---
sidebar_position: 11
---

# Lifting Values into CompiledCode

## Stage Constraints

The standard way of turning `a` into `CompiledCode a` is by compiling it (see [Compiling Plinth](./compiling-plinth.md)).
This requires the definition of `a` to be known at compile time.
As such, the following fails to compile:


```haskell
f :: Integer -> CompiledCode Integer
f x = $$(compile [|| x + 1 ||])
```

This is _not_ a Template Haskell stage error[^1], but the Plinth compiler imposes additional stage constraints on top of Template Haskell's.
To see why the above doesn't work, recognize that in the `CompiledCode` it is supposed to produce:
- `x` certainly cannot exist as a variable.
  Because when `f` is called, `x` is replaced by an integer constant, which needs to go into the `CompiledCode`.
  In other words, when we call `f 42`, we'd expect it to return a `CompiledCode` corresponding to `42 + 1`.
- But `x` cannot exist as a constant either, because `compile [|| x + 1 ||]` happens at compile time, and at compile time we don't yet know the value of `x`.

If you try to do this, you'll get a "no unfolding" error, meaning the Plinth compiler cannot proceed because the unfolding (definition) of `x` is not available.

On the other hand, the following is perfectly fine:

```haskell
f :: CompiledCode (Integer -> Integer)
f = $$(compile [|| \x -> x + 1 ||])
```

Now we are just compiling a regular lambda, and in the resulting `CompiledCode`, `x` is simply a lambda-bound variable.

The above can be summarized by the following rule for compiling Plinth Code:
- _Any variable inside the quotation passed to `compile` (i.e., the `...` in `$$(compile [|| ... ||])`) must either be a top-level variable (which can be defined in the same module or imported from a different module), or bound inside the quotation_.

## Lifting

Similar to the `Language.Haskell.TH.Syntax.Lift` class, which lifts Haskell values into Template Haskell ASTs, Plinth has a `PlutusTx.Lift.Class.Lift` class which lifts Haskell values into `CompiledCode`.
Both `Lift` classes work in a similar way - for instance, Template Haskell's `Lift` lifts integer 42 into a Template Haskell constant (`LitE (IntegerL 42)`), while Plinth's `Lift` lifts it into a PIR/UPLC constant (`con integer 42`).

`Lift` instances can generally be derived for data types that don't contain functions.
However, functions usually cannot be lifted.
To derive the Plinth `Lift` instance for a data type, use [makeLift](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Lift-TH.html#v:makeLift).

`Lift` makes it possible to write the above function of type `Integer -> CompiledCode Integer`, which can be written as

```haskell
f :: Integer -> CompiledCode Integer
f x = liftCodeDef (x + 1)
```

Now there's no Template Haskell, hence no compile time work being done.
When `f` is called, `x + 1` will be evaluated in Haskell into WHNF (i.e., an integer constant), which `liftCodeDef` dutifully converts into a `con integer`.

When you call `f 42`, the resulting `CompiledCode` contains a single constant, 43.
If you want the `CompiledCode` to instead contain `42 + 1`, you can compile `(+ 1)` separately, then apply it to the lifted `x`:

```haskell
f :: Integer -> CompiledCode Integer
f x = $$(compile [|| (+ 1) ||]) `unsafeApplyCode` liftCodeDef x
```

There are variants of `liftCodeDef` and `unsafeApplyCode`.
See [Haddock for PlutusTx.Lift](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Lift.html) and [Haddock for PlutusTx.Code](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Code.html) for more details.

---

[^1]: Here the usage of `x` is surrounded by one quotation (`[|| ... ||]`) and one splice (`$$(...)`), which is legit from the Template Haskell point of view. It would be a Template Haskell stage error if `x` was surrounded only by a splice (`f x = $$(compile (x + 1))`) or only by a quotation (`f x = compile [|| x + 1 ||]`, unless `x`'s type has a `Language.Haskell.TH.Syntax.Lift` instance).
