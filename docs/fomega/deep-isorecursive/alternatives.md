# Alternatives to elimination contexts

Elimination contexts are problematic, see the problem.md document. Hence one option is to move away from them and use something else. This document describes possible alternatives.

## Head-spine form

An elimination context is either a type or an application of a type function (which is in the form of elimination context again) to a type argument. If the head of such application is a `fix`, then we can `wrap` and `unwrap` a term of such type. Wrapping results in the `head` of the application being substituted for the variable it binds. One of the premises `wrap` has is that the whole thing must be of kind `(type)` and the same holds for `unwrap`.

What I've just described is exactly iterated application that leads to hereditary substitution at the type level: allowing `Fix` to be applied to a bunch of arguments kinda asks for iterated application at the type level:

```
Gamma |- wrap α pat spine M : [(fix α pat) spine]
```

Also iterated application is common at the type level as it simplifies unification (which we do not care about) and can be used for the formalization, because it's required by hereditary substitution (we do not do hereditary substitution, so both the points are not important for us, but what I'm proving here is that the head-spine form at the type level is common unlike elimination contexts).

There is a [formalization sketch of this](https://gist.github.com/effectfully/8ae112e2a99393c493642fc52aafe87f#file-system-f-iso-agda).

Here are some examples:

the `nat` data type:

```
natF = \(nat :: *) -> all r. r -> (nat -> r) -> r
nat  = fix natF []
zero = wrap natF [] /\(r :: *) -> \(z : r) (f : nat -> r) -> z
succ = \(n : nat) -> wrap natF [] /\(r :: *) -> \(z : r) (f : nat -> r) -> f n
```

the `list` data type

```
listF = \(list :: * -> *) (a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r
list  = \(a :: *) -> fix listF [a]
nil   = /\(a :: *) -> wrap listF [a] /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> z
cons  = /\(a :: *) -> \(x : a) (xs : list a) ->
        wrap listF [a] /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> f x xs
```

where `[a]` is a list containing exactly one element: `a`.

In general, each recursive data type is a `fix` applied to a pattern functor and a spine of type arguments. The pattern functor binds at least one variable, the one representing recursion, but it can bind more like in the `list` example where an additional type variable `a :: *` is bound. At the term level `wrap` receives the pattern functor of a data type being constructed and a spine of type arguments. The exact problem with elimination contexts is that an elimination context can't be inferred and we can't specify it, because elimination contexts do not have syntax. Here we are allowed to specify spines, because they do have syntax.

## Replace `fix :: (* -> *) -> *` by `ifix :: ((k -> *) -> k -> *) -> k -> *`

The least invasive approach. We only need to replace `fix :: (* -> *) -> *` by `ifix :: ((k -> *) -> k -> *) -> k -> *`. The original `fix` can be easily recovered as

```
origF = \(r :: (* -> *) -> *) (f :: * -> *) -> f (r f)
fix   =  \(f :: * -> *) ->                     ifix  origF f
wrap  = /\(f :: * -> *) -> \(t : f (fix f)) -> iwrap origF f t
```

(the encoding of `nat`, for example, then remains the same).

The type rules:

```
[infer| pat :: (k -> *) -> k -> *]    [check | arg :: k]
--------------------------------------------------------
[infer| ifix pat arg :: *]

[infer| term : ifix vPat vArg]    [infer| vArg :: k]
------------------------------------------------------------------
[infer| unwrap term : NORM (vPat (\(a :: k) -> ifix vPat a) vArg)]

[infer| pat :: (k -> *) -> k -> *]    [check | arg :: k]    pat ~>? vPat    arg ~>? vArg
[check| term : NORM (vPat (\(a :: k) -> ifix vPat a) vArg)]
----------------------------------------------------------------------------------------
[infer| iwrap pat arg term : ifix vPat vArg]
```

Note that we have to expand `ifix vPat` to `\(a :: k) -> ifix vPat a`, because `ifix` is a syntactic form that always receives a pattern functor and a type argument and can't be eta-contracted.

Here is how the `list` data type looks with `ifix`:

```
listF = \(list :: * -> *) (a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r
list  = \(a :: *) -> ifix listF a
nil   = /\(a :: *) -> iwrap listF a /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> z
cons  = /\(a :: *) -> \(x : a) (xs : list a) ->
            iwrap listF a /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> f x xs
```

This is basically the same encoding as with the head-spine form approach, except `a` is provided directly rather than via a single-element list.

However we also need to cover the generic n-ary case. With kind-level products we could write `fix f (a1, a2, ... an)`. We do not have kind-level products, but we can just Church-encode spines:

```
ifix f (\(r :: k1 -> k2 -> ... -> kn -> *) -> r a1 a2 ... an)
```

which gives us `k ~ (k1 -> k2 -> ... -> kn -> *) -> *`. This is not a "true" Church-encoded spine, because the resulting type is limited to be of kind `*`, but this seems enough in our case (see [this illustration](TreeForest.md)).

What is implemented right now performs this Church-encoding and the resulting machinery looks very much like the head-spine form approach for the user. Our examples become

`nat`:

```
(nat, wrapNat) = makeRecursiveType nat (all r. r -> (nat -> r) -> r)
zero = wrapNat [] /\(r :: *) -> \(z : r) (f : nat -> r) -> z
succ = \(n : nat) -> wrapNat [] /\(r :: *) -> \(z : r) (f : nat -> r) -> f n
```

`list`:

```
(list, wrapList) = makeRecursiveType list \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r
nil  = /\(a :: *) -> wrapList [a] /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> z)
cons = /\(a :: *) -> \(x : a) (xs : list a) ->
           wrapList [a] /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> f x xs
```

where `makeRecursiveType` is a function that hides all the Church-encoding details from the user. We see spines here again: `[]` in the `nat` example and `[a]` in the `list` example. Those are true spines, they can be of any length. We could also make `wrapNat` not receive any spine at all, because it must always be the empty spine, but we keep those empty spines for uniformity.

## Comparison of the `ifix` and head-spine form approaches

As shown in the end of the previous section there is no big difference to the user which approach is used as they both look almost identically to the user with only small cosmetic differences.

Regardless of the approach, `unwrap` is always used the same way. Even with elimination contexts or without higher kinds at all `unwrap` was used in the same way. The usages of `unwrap` in the Plutus Core codebase have never changed basically.

It also does not matter which approach we choose from the encoding of mutual recursion perspective. This is because for encoding mutual recursion we use [ifix](../mutual-type-level-recursion/MutualData.agda) which we have out of the box in the `ifix` approach and which we can get trivially in the head-spine form approach:

```
ifix  =  \(f :: (k -> *) -> k -> *) (a :: k) ->                        Spines.fix  f [a]
iwrap = /\(f :: (k -> *) -> k -> *) (a :: k) -> \(t : f (ifix f) a) -> Spines.wrap f [a] t
```

(where `Spines.fix` and `Spines.wrap` are the corresponding primitives in the head-spine approach). I.e. the only thing we need is just to use a single-element spine.

There are only two notable differences between the approaches:

1. the head-spine form solution may be more efficient, because it does not Church-encode spines. The exact performance penalty is not clear right now and will be investigated
2. the `ifix` solution requires much less changes to the Plutus Core AST and thus is more conservative
3. it's not immediately clear how to specify the rules for the head-spine form solution (which is why they're not present in this document)

These are all the trade-offs known at the moment.

## Replace `synth`-only moded type system w/ `synth+check` moded type system

The original reason for introducing elimination contexts is because we have types of the form `K{(fix a B)}`, which is stuck and cannot compute, but where the fixed point type may have types of kind `k -> k'`. That is to say, we non-`lambda` forms at function kinds. In the term language, we might just compute by fix reduction `(fix x M) ~> [(fix x M)/x]M` and then proceed, but this can't happen at the type level because we're using type-level fix for things which would run forever if we were to do this (e.g. the type of lists).

The form of `K` is guaranteed a priori to be a (possibly-empty) spine with the `fix` at the head, because type-level functions and application are the only computation we have in types, and so the only things that can be stuck. So we know that `K{_} = [_ A_0 ... A_n]`.

If the type `K{(fix a B)}` had been given to us as input to a checking judgment instead of as a synthesized output, then we would have no trouble figuring out what `K` is, because we simply look at the type and see if it's a spin headed by a `fix`:

```
checkSpine :: Type -> Maybe (TyVar, Type, [Type])
applySpine :: Type -> [Type] -> Type

check g (Wrap m) a =
  case checkSpine a of
    Nothing -> False
    Just (alpha, b, as) -> check g m (applySpine (substitute (Fix alpha b) alpha b) as)
```
