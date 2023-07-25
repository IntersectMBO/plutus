# Equality and serialization built-in functions for SOPs

## Preface

When we introduced SOPs we hoped it would allow us to get rid of encoding the `ScriptContext` using `Data` as processing `Data` is extremely inefficient compared to processing SOPs. Unfortunately, the community didn't approve of this idea due to SOPs not having equivalents of `equalsData` and `serialiseData` -- it turned out that contract developers rely on these primitives. That created a situation where we have a much more efficient way to encode data types (SOPs) and a huge bottleneck preventing us from leveraging it well: decoding `Data` can take up to 40% of script evaluation time and those `Data` objects are also huge script-size-wise. This issue is a blocker for [CIP-0097](https://github.com/michaelpj/CIPs/blob/mpj/script-context-sop/CIP-%3F%3F%3F%3F/README.md).

This document proposes SOP-based counterparts for `equalsData` and `serialiseData` to alleviate the problem. Unfortunately, it doesn't seem to allow us to solve the problem properly, because datums and redeemers have to stay `Data`-encoded and as such don't really benefit from addition of the proposed builtins. The overhead of decoding datums and redeemers seems high enough for this proposal, if implemented, to only provide marginal benefits that are not worth the additional complexity.

Costing issues are considered future work for a future proposal/amendement.

## Not just SOPs

Before we start, it's important to stress that `Data` objects contain `Integer`s and `ByteString`s and that whatever we do with SOPs, it should handle `Integer`s and `ByteString`s inside of constructors too.

It would be rather weird however to only allow for, say, checking equality of `Integer`s and `ByteString`s when they are wrapped in a constructor and fail within the same builtin if the constants are not wrapped, so it makes sense to handle constants and SOPs using the same builtin. We'll discuss later how to decide what constants to handle and what should cause evaluation failure regardless of whether they appear inside of a constructor or not.

A reasonable design then is one that only allows for checking equality of types whose _evaluated_ values are guaranteed to be in [canonical form](https://ncatlab.org/nlab/show/canonical+form):

> in type theory, a term belonging to some type is said to be of canonical form if it is explicitly built up using the constructors of that type. A canonical form is in particular a normal form (one not admitting any reductions), but the converse need not hold.
>
> For example, the terms of type `ℕ` (a natural numbers type) of canonical form are the numerals
`S(S(S(⋯(0)⋯)))`.

Hypothetically, we could allow for handling `VDelay`, `VLamAbs` and `VBuiltin` too by returning `Dunno` when checking, say, two `VLamAbs` for equality instead of error (or `True`/`False` at random), however allowing branching on whether an argument is a function or not sounds very weird, so it's best to fail on unexpected input.

All in all, given the choice to handle not just SOPs, but also some of the constants, it is proposed to name the equality checking builtin `equalsCanonical` and serialisation builtin `serialiseCanonical`.

## Untyped

Say we didn't have any Typed Plutus Core and only wanted to implement the most straightforward version of `equalsCanonical`, let's see how it could look like.

We'd add the following definitions:

```haskell
data EqCanonicalResult
    = EqCanonicalTrue             -- ^ Equal.
    | EqCanonicalFalse            -- ^ Not equal.
    | EqCanonicalUnexpectedInput  -- ^ Bad argument such as a lambda or a partially applied builtin.

instance Semigroup EqCanonicalResult where
    EqCanonicalTrue <> res2 = res2
    res1            <> _    = res1

instance Monoid EqCanonicalResult where
    mempty = EqCanonicalTrue

toEqCanonicalResult :: Bool -> EqCanonicalResult
toEqCanonicalResult True  = EqCanonicalTrue
toEqCanonicalResult False = EqCanonicalFalse

fromEqCanonicalResult :: EqCanonicalResult -> EvaluationResult Bool
fromEqCanonicalResult EqCanonicalTrue            = EvaluationSuccess True
fromEqCanonicalResult EqCanonicalFalse           = EvaluationSuccess False
fromEqCanonicalResult EqCanonicalUnexpectedInput = EvaluationFailure

class EqCanonical a where
    eqCanonical :: a -> a -> EqCanonicalResult
```

to some module, expose `eqCanonical` as a new builtin returning a `Bool` or failing evaluation:

```haskell
    toBuiltinMeaning _ver EqualsCanonical =
        makeBuiltinMeaning
            (\val1 val2 -> fromEqCanonicalResult $ eqCanonical val1 val2)
            (\_ _ _ -> ExBudgetLast mempty)
```

and provide support for the whole thing in the CEK machine by implementing `EqCanonical` for `CekValue`:

```haskell
instance (GEq uni, Closed uni, uni `Everywhere` Eq) => EqCanonical (ArgStack uni fun ann) where
    eqCanonical EmptyStack = \case
        EmptyStack -> EqCanonicalTrue
        _          -> EqCanonicalFalse
    eqCanonical (ConsStack arg1 args1) = \case
        ConsStack arg2 args2 -> eqCanonical arg1 arg2 <> eqCanonical args1 args2
        _                    -> EqCanonicalFalse

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => EqCanonical (CekValue uni fun ann) where
    eqCanonical (VConstr i1 args1) = \case
        VConstr i2 args2 -> toEqCanonicalResult (i1 == i2) <> eqCanonical args1 args2
        VCon _           -> EqCanonicalFalse
        _                -> EqCanonicalUnexpectedInput
    eqCanonical (VCon con1) = \case
        VCon con2   -> toEqCanonicalResult $ con1 == con2
        VConstr _ _ -> EqCanonicalFalse
        _           -> EqCanonicalUnexpectedInput
    eqCanonical _ = \_ -> EqCanonicalUnexpectedInput
```

I.e. for `CekValue` `eqCanonical` checks if both the arguments are either `VConstr` or `VCon` and fails otherwise. If the constructors are the same, then the function checks if their contents are the same too.

An `eqCanonical` application can have weird semantics if it doesn't come from a well-typed term, for example

```haskell
eqCanonical
    (VConstr 0 (ConsStack (mkConstant () True) EmptyStack))
    (VConstr 1 (ConsStack (VDelay <...> <...>) EmptyStack))
```

returns `False`, because the two tags are different (`0` vs `1`) and since `EqCanonicalResult` is short-circuiting we never get to check if the two `ArgStack`s are equal and thus never reach `VDelay`, which would otherwise fail evaluation.

But that's the usual untyped evaluation stuff, we have plenty of tests that fail to type check but evaluate successfully, see `IllTypedRuns` tests in [this](https://github.com/input-output-hk/plutus/blob/173dce5ee85cb8038563dd39299abb550ea13b88/plutus-core/untyped-plutus-core/test/Evaluation/Golden.hs) module. Preventing things from being weird is the reason why we have a type checker, hence let's improve upon the untyped builtin described in this section.

## Typed

An obvious starting point is to assign `equalsCanonical` the following type signature:

```
equalsCanonical : all a. a -> a -> bool
```

but that would be a parametricity breaking lie: the type signature says that the builtin can compare two values of an arbitrary type for equality and return a conclusive `True` or `False`, but this isn't of course possible if the values are, say, functions.

To state it more formally, this type signature gives rise to the following law:

```
forall (f :: a -> b) (x y :: a). equalsCanonical {a} x y = equalsCanonical {b} (f x) (f y)
```

In plain English, either all functions in your language are injective (it's a simplified law, in the actual one that would probably still not be sufficient) or `equalsCanonical` cannot use any of its arguments to influence the result of the operation.

I.e. by parametricity what `equalsCanonical` finishes with (successfully or not doesn't matter) must not be determined by any of the arguments, meaning `equalsCanonical` either always fails or always returns the same `bool`, irrespective of its arguments.

By allowing `equalsCanonical` take arguments into account when computing the result we'd break parametricity thus making the type signature a lie.

Instead, we can introduce a new built-in type constructor, let's call it `canonical` with the semantics that every `canonical a` value is known to be in canonical form. `equalsCanonical` then becomes

```
equalsCanonical : all a. canonical a -> canonical a -> bool
```

which is no longer a lie.

On the Haskell side it'll look like this:

```haskell
    toBuiltinMeaning _ver EqualsCanonical =
        makeBuiltinMeaning
            equalsCanonicalPlc
            (\_ _ _ -> ExBudgetLast mempty)
      where
        equalsCanonicalPlc :: Opaque val (Canonical a) -> Opaque val (Canonical a) -> EvaluationResult Bool
        equalsCanonicalPlc val1 val2 = fromEqCanonicalResult $ eqCanonical val1 val2
```

Now we of course didn't resolve any problem by introducing `canonical`, we just moved it from `equalsCanonical` to whatever builtin is going to create `canonical` values. However moving the problem this way opens up some interesting opportunities. A reasonable way of constructing a `canonical` value is a builtin that takes some kind of a proof that the value can indeed be represented in canonical form, here's one option on how to achieve that:

```
mkCanonical : all a. (a -> data) -> a -> canonical a
```

This builtin says that as long as any value of type `a` can be converted to a `data`, it's safe to say the value is going to be in canonical form when we reach it during evaluation. Here's its implementation:

```haskell
    toBuiltinMeaning _ver MkCanonical =
        makeBuiltinMeaning
            mkCanonicalPlc
            (\_ _ _ -> ExBudgetLast mempty)
      where
        mkCanonicalPlc :: Opaque val (a -> Data) -> Opaque val a -> Opaque val (Canonical a)
        mkCanonicalPlc _ = coerce
```

What is great about this builtin is that it's completely erasable, since its implementation ignores the first argument and returns the second one without changing it in any way on the Plutus side (even on the Haskell side that `coerce` doesn't survive compilation). I.e. it's basically the same as `trace` except it doesn't even have any side effect and we already know how to erase `trace`. Thus whatever we provide as that `a -> Data` function can be erased without pointlessly wasting precious bytes of script size.

Moreover, contract writers who don't care about types (which is often the case) can directly replace `equalsData` with `equalsCanonical` and still have everything working, since `canonical` isn't an actual built-in type whose values go into the `Constant` constructor, it's merely a [ghost of a departed proof](https://kataskeue.com/gdp.pdf).

How should we implement `Canonical` then given that it's a ghost in Plutus and only a type-level entity in Haskell not needing any term-level content? Well, the question kinda answers itself:

```haskell
type Canonical :: GHC.Type -> GHC.Type
data Canonical a
```

Moreover, once the grand universe split is complete (see [this](https://input-output.atlassian.net/browse/PLT-810) internal Jira ticket), we won't even need to add a runtime type tag for `Canonical` to the term-level universe, limiting its existence only to the type-level universe.

## Parametricity issues

Now `mkCanonical` is still problematic if the caller supplies a bogus `a -> data` function as a "proof", which would allow them to recover the parametricity-breaking

```
equalsCanonical : all a. a -> a -> bool
equalsCanonical x y = equalsCanonical (mkCanonical (\_ -> I 42) x) (mkCanonical (\_ -> I 42) y)
```

In this section we're going to evaluate just how problematic this issue is.

Firstly, having the parametricity-breaking `equalsCanonical` isn't anything groundbreaking for a programming language, for example OCaml has such a builtin. The effect of presence of this builtin on the type system is discussed in Jeremy Yallop's Advanced Functional Programming course, see 7.4.2 Non-parametric values in [this](https://www.cl.cam.ac.uk/teaching/1617/L28/parametricity.pdf) chapter. Quoting it here:

> However, OCaml provides the following built-in structural equality function:
>
> ```
> val (=) : 'a -> 'a -> bool
> ```
>
> Even though it has this type, it is not a constant function. This means that it is not parametric.
>
> The existence of this function and several similar ones in OCaml, can break the guarantees provided by abstraction and parametricity. However, not all guarantees are broken, for instance the preservation of invariants is not affected by any of the built-in functions available in OCaml.
>
> In practice, this means that such functions should only be used at known types. Using them on abstract types produces non-parametric code whose correctness may rely on details of an implementation that are not exposed in its interface.

The same unconstrained structural equality operation is also present in Isabelle and the effect of that on parametricity is discussed in [Conditional Parametricity in Isabelle/HOL](http://www.andreas-lochbihler.de/pub/gilcher2017ITP.pdf):

> Not all polymorphic functions in higher-order logic (HOL) are parametric though.
>
> For example, equality `(==) :: α → α → B` is not parametric in `α`: for the singleton type unit, equality always returns `True`, while for any non-singleton type it is not a constant function. As equality is not parametric, the statement `∀A :: α → α′ → B. (A ⇒ A ⇒ ←→) (==) (==)` does not hold, but a weaker version does: `∀A :: α → α′ → B. bi-unique A −→ (A ⇒ A ⇒ ←→) (==) (==)` where the condition `bi-unique A` requires `A` to be a single-valued and injective relation.
>
> So, we call equality `(==)` conditionally parametric for bi-unique relations.

I.e. the presence of such an operator does of course break the very general notion of parametricity and makes it necessary to amend the definition of parametricity applicable within the specific system, however so do a whole lot of other things: `seq` [breaks](https://dl.acm.org/doi/10.1145/964001.964010) the general parametricity in Haskell in a very non-trivial way (do check out the abstract), as well as other things, quoting [Graduality and Parametricity: Together Again for the First Time](http://maxsnew.com/docs/graduality-parametricity.pdf):

> It is worth noting that the presence of effects -- such as nontermination, mutable state, control effects -- requires different formulations of the logical relation that defines parametricity. However, those logical relations capture parametricity in that they always formalize uniformity of behavior across different type instantiations. For instance, for a language that supports nontermination, the logical relation for parametricity ensures that two different instantiations have the same termination behavior: either both diverge, or they both terminate with related values. Because of this, the presence of effects usually leads to weaker free theorems -- in pure System F all inhabitants of `∀𝑋. 𝑋 → 𝑋` are equivalent to the identity function, but in System F with non-termination, every inhabitant is either the identity or always errors. Though the free theorems are weaker, parametricity still ensures uniformity of behavior. As our counterexample above illustrates, GSF is non-parametric since it does not ensure uniform behavior. However, since the difference in behavior was between error and termination, it is possible that GSF satisfies a property that could be called łpartial parametricityž (or parametricity modulo errors) that weakens the notion of uniformity of behavior: either one side errors or we get related behaviors.

We have non-termination, `error` and `trace` in Plutus meaning we cannot use some very general notion of parametricity anyway, although admittedly `equalsCanonical` is far more "malicious" than those effects. Even then, there do exist notions of parametricity for systems even with full-scale type case, quoting [Generalizing Parametricity Using Information-flow](https://www.seas.upenn.edu/~sweirich/papers/seckinds/lics2005.ps):

> Currently, module implementors rely on parametric polymorphism to provide integrity and confidentiality guarantees about their abstract datatypes. However, standard parametricity does not hold for languages with run-time type analysis; this paper shows how to generalize parametricity so that it does. The key is to augment the type system with annotations about information-flow. Implementors can then easily see which parts of a program depend on the chosen implementation by tracking the flow of dynamic type information.

They use the same structural equality function as a "canonical example of run-time type analysis".

Overall, a structural equality operator does complicate metatheory, but it doesn't destroy it.

It is however important to look at the whole system, which in our case comprises four languages, not just TPLC and PIR.

## Security of the system as a whole

If `equalsCanonical : all a. a -> a -> bool` is still admissible, do we win anything at all by introducing the `mkCanonical` indirection? Yes: we introduce a hoop that the user needs to jump through to be able to use `equalsCanonical` and that hoop acts as explicit guidance.

We have a concrete example of such a thing in the code base: the [`Normalized`](https://github.com/input-output-hk/plutus/blob/99afebc7a0ce5352dd40fb86bac6255003028fd7/plutus-core/plutus-core/src/PlutusCore/Core/Type.hs#L194) newtype wrapper. Its constructor is exposed, because there's simply no sensible way not to expose it as one often has to manually construct `Normalized` types in the type checker and some safe automatically normalizing function can't be used for performance reasons. So while it doesn't provide any safety guarantees, it's still useful, because it points the developer to every place where attention is required when it comes to not breaking the internal invariant that type inference returns a `Normalized` type. It is then the responsibility of the developer to explain every usage of the `Normalized` constructor in the type checker and we do enforce that policy during code reviews.

`mkCanonical` plays the same role, with the user normally not being somebody who creates a smart contract, but a compiler developer, because we're not going to expose the unsafe `mkCanonical` builtin directly for smart contract writers to use. Instead, in Plutus Tx we'll expose something like

```haskell
mkCanonical :: ToData a => a -> Canonical a
```

which, given that `ToData` instances are normally derived, is mostly safe with the exception of the user manually providing a `ToData` instance with a non-injective `toBuiltinData` (which may even make sense for a quotient type for example).

As an option we could introduce a `MkCanonical` type class whose purpose is to ensure that every call to `mkCanonical` is safe, instead of relying on `toBuiltinData` being injective for all types. Using `ToData` has the advantage that with a flag one can switch from structural equality to equality-via-`Data` to test that the two agree.

Whatever we choose in the end to help the user not to shoot themselves in the foot with Plutus Tx version of `mkCanonical`, it needs to come with some sort of a "soft proof" like a satisfied instance constraint. By converting this "soft proof" to a `a -> data` function we create a true ghost of a departed proof, except rather than being a ghost within the same system like in the paper, in our case it is a ghost from a higher-level one.

Think of it as follows: it is fine for Agda code to compile to Haskell code with lots and lots of `unsafeCoerce` in it, because the safety was proven on the Agda side. In our case it's similar: we cannot preserve a proof across language boundaries, because TPLC and PIR simply don't have anything that would allow us to assign a type to a structural equality operator, so we have to bypass the type checker in some way (which we know is safe since we've proven that in the high-level language, be it Plutus Tx or some other language). Except in our case it's better, because at least we can have that `a -> data` ghost as a remnant of the original proof, forcing the compiler developer to make sure a proof is produced in the first place and its ghost is subsequently retained -- as opposed to allowing the compiler developer to call `equalsCanonical : all a. a -> a -> bool` nilly-willy.

Finally, if we want to, we can absolutely create

```haskell
class MkCanonical a where
    mkCanonical :: a -> Canonical a
```

such that it's always safe to call it -- by never exposing any constructor for `Canonical` in Plutus Tx and only allowing to derive the type class with the deriving machinery ensuring that `a` is a SOP and by constraining all of its type variables appropriately. And there's nothing unsafe about `equalsCanonical` in UPLC. So if we can have a safe `equalsCanonical` + `mkCanonical` in the user-facing Plutus Tx and in the ledger-facing Untyped Plutus Core, are they really as unsafe as our internal intermediate TPLC and PIR make them seem or is it more of a problem with the latter two than with the proposed builtins?

Not all invariants end up being reflected in the type system and we have already made sacrifices when it comes the semantics of Plutus IR when we allowed escaped types, see [this](https://github.com/input-output-hk/plutus/blob/ec1540a2da65280002f5877c64cda3480b81edef/language-plutus-core/docs/Typechecking%20PIR.md) originally rejected proposal. If `equalsCanonical` addresses the community split, it may be very worth the trouble that it brings to our internal intermediate languages. At least we have ghosts on our side and those have already helped the humanity once in the [battle of the Pelennor Fields](https://www.youtube.com/watch?v=TjzQ8VXqJ6E).

## A bird's-eye view

Here's how the whole system looks like from a high-level perspective:

- user-facing Plutus Tx: `mkCanonical :: MkCanonical a => a -> Canonical a` -- fully safe if we want to make it such
- internal intermediate TPLC and PIR: `mkCanonical : (a -> data) -> a -> canonical a` -- requires a custom definition of parametricity that isn't going to be particularly nice
- ledger-facing UPLC: `equalsCanonical` -- fully safe regardless of whether `mkCanonical` is used or not

## Misc

We may want to have ways of constructing `canonical` values other than via a `a -> Data` proof, since not everything canonical can be represented as `Data`. We can always add more builtins, but that seems like it might be wasteful, not sure.

We will of course need an opposite builtin to `mkCanonical`, but that's easy, on the Plutus side it's

```
unCanonical : all a. canonical a -> a
```

and on the Haskell side it's

```haskell
    toBuiltinMeaning _ver UnCanonical =
        makeBuiltinMeaning
            unCanonicalPlc
            (\_ _ -> ExBudgetLast mempty)
      where
        unCanonicalPlc :: Opaque val (Canonical a) -> Opaque val a
        unCanonicalPlc = coerce
```

This function is of course erasable too.

What's the kind of `canonical`? It may seem obvious that it's `* -> *`, but this isn't obvious at all, given that built-in types cannot create a `*` on the metatheory side, only a `#` (this distinction doesn't exist on the implementation side). Do we want to allow pointless built-in types like `[Canonical a]` if we're going to maintain the rule that any built-in type constructs a `#`? Or do we simply add `Canonical` to the `Type` AST and not make it into a built-in type polluting Typed Plutus Core with very Cardano-specific details? We'll need to sort that out too. Also the metatheory currently doesn't support builtins taking functions as arguments (implementation supports arbitrary Plutus types, although some are more ergonomic than others).

In the `EqCanonical` instance for `CekValue` we require each built-in type from the universe to implement `Eq`:

```haskell
instance (GEq uni, Closed uni, uni `Everywhere` Eq) => EqCanonical (CekValue uni fun ann) where
```

We may want to require ``uni `Everywhere` EqCanonical`` instead, in case some built-in types don't have decidable equality (currently all do).

Instead of having an `EqCanonical` class we may want to have a class for extracting either a SOP constructor (`VConstr` in `CekValue`) or a constant (`VCon` in `CekValue`) from a value, so that we can reuse it for both `equalsCanonical` and `serialiseCanonical` as otherwise we'd have to introduce another `SerialiseCanonical` class or something. Adding a new type class for every operation definable on values in canonical form would be silly. Maybe we could even just expand the today's `HasConstant` class that currently only allows one to extract a constant out of a value? Whatever answer to this question is going to be we should add `equalsCanonical` and `SerialiseCanonical` simultaneously in order to ensure we're not missing a part of the picture.
