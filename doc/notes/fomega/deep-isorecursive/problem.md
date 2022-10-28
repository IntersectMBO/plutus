# Discussion

This document describes the problem we stumbled upon while implementing elimination contexts.

## The proposed rules

(see proposal.md for details)

```
Γ ⊢ Q :: (type)    Q = E{(fix a C)}     Γ ⊢ M : E{[(fix a C)/a]C}
------------------------------------------------------------------
Γ ⊢ (wrap a C M) : Q

Γ ⊢ Q :: (type)    Q = E {(fix a C)}     Γ ⊢ M : Q
---------------------------------------------------
Γ ⊢ (unwrap M) : E{[(fix a C)/a]C}

```

Implementing `unwrap` is a breeze, but making the presented `wrap` computational (as opposed to declarative) doesn't seem to be possible.

## The problem

Consider the definition of `List` (that's some Plutus Core pseudocode):

```
fix List. \(A :: *) -> all (R :: *). R -> (A -> List A -> R) -> R
```

according to the rules, the empty list of integers is defined like that (I'm ignoring sizes):

```
wrap List
    (\(A :: *) -> all (R :: *). R -> (A -> List A -> R) -> R)
    (/\(R :: *) -> \(z : R) (f : Integer -> List Integer -> R) -> z)
```

How to infer that the type of this expression is `List Integer`?

The type of the term wrap receives is

```
all (R :: *). R -> (Integer -> List Integer -> R) -> R
```

Well, we can instantiate `A` from

```
(\(A :: *) -> all (R :: *). R -> (A -> List A -> R) -> R)
```

to some metavariable, perform unification and find the solution, but

1. this doesn't work for all cases, see below
2. introducing unification in a core language is not something we want to do anyway

The crucial part here is that `Integer` simply does not appear in the pattern functor of `List` while previously this was the case (after normalization). Hence we need to somehow "mine" it and the only other source we have is the term wrap receives, but this mining process seems silly. And what if some pattern functor has a leading lambda and ignores the variable it binds? Then a term of the fixed point of such pattern functor would check against this type constructor being applied to any type whatsoever. Meaning that we can't infer a single type for such term -- it has many types! I.e. the only thing we can infer is this type constructor applied to a metavariable that unifies with any other type. Or we can make a forall and a big lambda out of thin air just to fill this hole.

## A non-inferrable term

Consider term:

```
wrap (r :: * -> *) (\(any :: *) -> boolean) true
```

It type checks against this type:

```
fix r (\(any :: *) -> boolean) integer
```

The derivation:

```
a ~ r
C ~ \(_ :: *) -> boolean
E ~ hole integer

Q = (hole integer) {fix r (\(_ :: *) -> boolean)}
  ~ fix r (\(_ :: *) -> boolean) integer

true : (hole integer) {[fix r (\(_ :: *) -> boolean) / r] (\(_ :: *) -> boolean)}
     ~ (hole integer) {\(_ :: *) -> boolean}
     ~ (\(_:: *) -> boolean) integer
     ~ boolean

-------------------------------

wrap r (\(_ :: *) -> boolean) true : fix r (\(_ :: *) -> boolean) integer
```

However the term type checks not only against this type, but also against infinitely many other types such as

```
fix r (\(any :: *) -> boolean) boolean
fix r (\(any :: *) -> boolean) (list integer)
```

or basically any

```
fix r (\(any :: *) -> boolean) _a
```

where `_a` is some type.

This is due to this premise in the rule for `wrap`: `Γ ⊢ M : E{[(fix a C)/a]C}`. Here we infer the type of `M` and check whether it is of the `E{[(fix a C)/a]C}` form. In our case the inferred type is `boolean` and `[(fix a C)/a]C` is

```
[(fix r (\(_::*) -> boolean) / r] (\(_ :: *) -> boolean)
```

which reduces to `E{\(_ :: *) -> boolean}`. I.e. we have the equation

```
E{\(_ :: *) -> boolean} =?= boolean
```

which is the same as

```
(\(_ :: *) -> boolean) _x =?= boolean
```

which has multiple solutions, because `_x` can be anything of kind `*`, because it's simply ignored.

Thus we can't infer the type of `wrap r (\(_ :: *) -> boolean) true` without adding metavariables to the language.

## A possible solution

We can have the following rule for `wrap`:

```
Γ ⊢ pat :: K    F :: K -> *    Γ ⊢ term : F ([fix n pat / n] pat)
-----------------------------------------------------------------
Γ ⊢ wrap n pat F term : F (fix n pat)
```

here we add an additional `F` which plays the role of elimination context. I.e. this allows us to specify all arguments a `fix` is applied to. However we now have full computational power at hand with that `F :: K -> *` meaning we can fold/unfold in surprising places. Hence the `unwrap` rule has to be changed accordingly. I.e. the solution is rather heavy and changes the expected semantics of `wrap` and `unwrap`.
