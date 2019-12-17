{-# OPTIONS --type-in-type         #-}
{-# OPTIONS --no-termination-check #-}

-- In this post we'll consider how to define and generalize fixed-point combinators for families of
-- mutually recursive functions. Both in the lazy and strict settings.

module FixN where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Base
open import Data.Bool.Base

-- This module is parameterized by `even` and `odd` functions and defines the `Test` type
-- which is used below for testing particular `even` and `odd`.
module Test (even : ℕ -> Bool) (odd : ℕ -> Bool) where
  open import Data.List.Base
  open import Data.Product using (_,′_)

  Test : Set
  Test =
      (  map even (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
      ,′ map odd  (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
      )
    ≡ (  true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ []
      ,′ false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ []
      )

-- Brings `Test : (ℕ -> Bool) -> (ℕ -> Bool) -> Set` in scope.
open Test

module ScottTuple where

  -- Some convenience functions for deconstructing Scott-encoded 2-tuples
  sel₁ : ∀ {A B} -> A -> B -> A
  sel₁ = λ x y -> x
  sel₂ : ∀ {A B} -> A -> B -> B
  sel₂ = λ x y -> y

  -- Curry and uncurry for Scott-encoded 2-tuples
  curryScott2
    : ∀ {A B R}
    -> ((∀ {Q} -> (A -> B -> Q) -> Q) -> R)
    -> (A -> B -> R)
  curryScott2 tup a b = tup λ f -> f a b

  uncurryScott2
      : ∀ {A B R}
      -> (A -> B -> R)
      -> ((∀ {Q} -> (A -> B -> Q) -> Q) -> R)
  uncurryScott2 f g = g f

open ScottTuple

module Classic where
  open import Data.Product

  -- We can use the most straightforward fixed-point operator in order to get mutual recursion.
  {-# TERMINATING #-}
  fix : {A : Set} -> (A -> A) -> A
  fix f = f (fix f)

  -- We instantiate `fix` to be defined over a pair of functions. I.e. a generic fixed-point
  -- combinator for a family of two mutually recursive functions has this type signature:
  -- `∀ {A B} -> (A × B -> A × B) -> A × B` which is an instance of `∀ {A} -> (A -> A) -> A`.

  -- Here is the even-and-odd example.
  -- `even` is denoted as the first element of the resulting tuple, `odd` is the second.
  evenAndOdd : (ℕ -> Bool) × (ℕ -> Bool)
  evenAndOdd = fix $ λ p ->
      -- `even` returns `true`  on `0` and calls `odd`  on `suc`
      (λ { 0 -> true  ; (suc n) -> proj₂ p n })
      -- `odd`  returns `false` on `0` and calls `even` on `suc`
    , (λ { 0 -> false ; (suc n) -> proj₁ p n })

  even : ℕ -> Bool
  even = proj₁ evenAndOdd

  odd : ℕ -> Bool
  odd = proj₂ evenAndOdd

  test : Test even odd
  test = refl

  -- And that's all.

  -- This Approach

  -- 1. relies on laziness
  -- 2. relies on tuples
  -- 3. allows to encode a family of arbitrary number of mutually recursive functions
  --      of possibly distinct types

  -- There is one pitfall, though, if we write this in Haskell:

  -- evenAndOdd :: ((Int -> Bool), (Int -> Bool))
  -- evenAndOdd = fix $ \(even, odd) ->
  --     ( (\n -> n == 0 || odd  (n - 1))
  --     , (\n -> n /= 0 && even (n - 1))
  --     )

  -- we'll get an infinite loop, because matching over tuples is strict in Haskell (in Agda it's lazy)
  -- which means that in order to return a tuple, you must first compute it to whnf, which is a loop.
  -- This is what the author of [1] stumpled upon. The fix is simple, though: just use lazy matching
  -- (aka irrefutable pattern) like this:

  -- evenAndOdd = fix $ \(~(even, odd)) -> ...

  -- In general, that's a good approach for a lazy language, but Plutus Core is a strict one (so far),
  -- so we need something else. Besides, we can do some pretty cool generalizations, so let's do them.

module PartlyUncurried2 where
  open import Data.Product

  -- It is clear that we can transform

  -- ∀ {A B} -> (A × B -> A × B) -> A × B

  -- into

  -- ∀ {A B R} -> (A × B -> A × B) -> (A -> B -> R) -> R

  -- by Church-encoding `A × B` into `∀ {R} -> (A -> B -> R) -> R`.
  -- However in our case we can also transform

  -- A × B -> A × B

  -- into

  -- ∀ {Q} -> (A -> B -> Q) -> A -> B -> Q

  -- Ignoring the former transformation right now, but performing the latter we get the following:

  fix2 : ∀ {A B} -> (∀ {Q} -> (A -> B -> Q) -> A -> B -> Q) -> A × B
  fix2 f = f sel₁ (proj₁ (fix2 f)) (proj₂ (fix2 f))
         , f sel₂ (proj₁ (fix2 f)) (proj₂ (fix2 f))

  -- `f` is what was of the `A × B -> A × B` type previously, but now instead of receiving a tuple
  -- and defining a tuple, `f` receives a selector and two values of types `A` and `B`. The values
  -- represent the functions being defined, while the selector is needed in order to select one of
  -- these functions.

  -- Consider the example:

  evenAndOdd : (ℕ -> Bool) × (ℕ -> Bool)
  evenAndOdd = fix2 $ λ select even odd -> select
    (λ { 0 -> true  ; (suc n) -> odd  n })
    (λ { 0 -> false ; (suc n) -> even n })

  -- `select` is only instantiated to either `λ x y -> x` or `λ x y -> y` which allow us
  -- to select the branch we want to go in. When defining the `even` function, we want to go in
  -- the first branch and thus instantiate `select` with `λ x y -> x`. When defining `odd`,
  -- we want the second branch and thus instantiate `select` with `λ x y -> y`.
  -- All these instantiations happen in the `fix2` function itself.

  -- It is instructive to inline `fix2` and `select` along with the particular selectors. We get:

  evenAndOdd-inlined : (ℕ -> Bool) × (ℕ -> Bool)
  evenAndOdd-inlined = defineEven (proj₁ evenAndOdd-inlined) (proj₂ evenAndOdd-inlined)
                     , defineOdd  (proj₁ evenAndOdd-inlined) (proj₂ evenAndOdd-inlined)
    where
      defineEven : (ℕ -> Bool) -> (ℕ -> Bool) -> ℕ -> Bool
      defineEven even odd = λ { 0 -> true  ; (suc n) -> odd  n }

      defineOdd  : (ℕ -> Bool) -> (ℕ -> Bool) -> ℕ -> Bool
      defineOdd  even odd = λ { 0 -> false ; (suc n) -> even n }

  -- I.e. each definition is parameterized by both functions and this is just the same fixed point
  -- of a tuple of functions that we've seen before.

  test : Test (proj₁ evenAndOdd) (proj₂ evenAndOdd)
  test = refl

  test-inlined : Test (proj₁ evenAndOdd-inlined) (proj₂ evenAndOdd-inlined)
  test-inlined = refl

module Uncurried where
  -- We can now do another twist and turn `A × B` into `∀ {R} -> (A -> B -> R) -> R` which finally
  -- allows us to get rid of tuples:

  fix2 : {A B R : Set} -> (∀ {Q} -> (A -> B -> Q) -> A -> B -> Q) -> (A -> B -> R) -> R
  fix2 f k = k (fix2 f (f sel₁)) (fix2 f (f sel₂))

  -- `k` is the continuation that represents a Church-encoded tuple returned as the result.
  -- But... if `k` is just another way to construct a tuple, how are we not keeping `f` outside of
  -- recursion? Previously it was `fix f = f (fix f)` or

  -- fix2 f = f (λ x y -> x) (proj₁ (fix2 f)) (proj₂ (fix2 f))
  --        , f (λ x y -> y) (proj₁ (fix2 f)) (proj₂ (fix2 f))

  -- i.e. `f` is always an outermost call and recursive calls are somewhere inside. But in the
  -- definition above `f` is inside the recursive call. How is that? Watch the hands:

  --   fix2 f k                                                                                   [1]
  -- = k (fix2 f (f  λ x y -> x))  (fix2 f (f  λ x y -> y))                                       [2]
  -- ~ k (fix2 f (f (λ x y -> x))) (fix2 f (f (λ x y -> y)))                                      [3]
  -- ~ k (f (λ x y -> x) (fix2 f (f λ x y -> x)) (fix2 f (f λ x y -> y)))
  --     (f (λ x y -> y) (fix2 f (f λ x y -> y)) (fix2 f (f λ x y -> y)))

  -- [1] unfold the definition of `fix2`
  -- [2] add parens around selectors for clarity
  -- [3] unfold the definition of `fix` in both the arguments of `k`

  -- The result is very similar to the one from the previous section
  -- (quoted in the snippet several lines above).

  -- And the test:

  evenAndOdd : ∀ {R} -> ((ℕ -> Bool) -> (ℕ -> Bool) -> R) -> R
  evenAndOdd = fix2 $ λ select even odd -> select
    (λ { 0 -> true  ; (suc n) -> odd  n })
    (λ { 0 -> false ; (suc n) -> even n })

  test : Test (evenAndOdd λ x y -> x) (evenAndOdd λ x y -> y)
  test = refl

  -- It is straighforward to define a fixed-point combinator for a family of three mutually
  -- recursive functions:

  fix3 : {A B C R : Set} -> (∀ {Q} -> (A -> B -> C -> Q) -> A -> B -> C -> Q) -> (A -> B -> C -> R) -> R
  fix3 f k = k (fix3 f (f λ x y z -> x)) (fix3 f (f λ x y z -> y)) (fix3 f (f λ x y z -> z))

  -- The pattern is clear and we can abstract it.

module UncurriedGeneral where
  -- The type signatures of the fixed point combinators from the above

  -- ∀ {A B} -> (∀ {Q} -> (A -> B -> Q) -> A -> B -> Q) -> ∀ {R} -> (A -> B -> R) -> R
  -- ∀ {A B C} -> (∀ {Q} -> (A -> B -> C -> Q) -> A -> B -> C -> Q) -> ∀ {R} -> (A -> B -> C -> R) -> R

  -- (`∀ {R}` is moved slightly righter than what it was previously, because it helps readability below)
  -- can be generalized to

  -- ∀ {F} -> (∀ {Q} -> F Q -> F Q) -> ∀ {R} -> F R -> R

  -- with `F` being `λ X -> A -> B -> X` in the first case and `λ X -> A -> B -> C -> X` in the second.
  -- That's fact (1).

  -- Now let's look at the definitions. There we see

  -- fix2 f k = k (fix2 f (f λ x y -> x)) (fix2 f (f λ x y -> y))
  -- fix3 f k = k (fix3 f (f λ x y z -> x)) (fix3 f (f λ x y z -> y)) (fix3 f (f λ x y z -> z))

  -- i.e. each recursive call is parameterized by the `f` that never changes, but also by
  -- the `f` applied to a selector and selectors do change. Thus the

  -- λ selector -> fix2 f (f selector)
  -- λ selector -> fix3 f (f selector)

  -- parts can be abstracted into something like

  -- λ selector -> fixSome f (f selector)

  -- where `fixSome` can be both `fix2` and `fix3` depending on what you instantiate it with.
  -- Then we only need combinators that duplicate the recursive case an appropriate number of times
  -- (2 for `fix2` and 3 for `fix3`) and supply a selector to each of the duplicates. That's fact (2).
  -- And those combinators have to be of the same type, so we can pass them to the generic
  -- fixed-point combinator we're deriving.

  -- To infer the type of those combinators we start by looking at the types of

  -- λ selector -> fix2 f (f selector)
  -- λ selector -> fix3 f (f selector)

  -- which are

  -- ∀ {Q} -> (A -> B -> Q) -> Q
  -- ∀ {Q} -> (A -> B -> C -> Q) -> Q

  -- correspondingly. I.e. the unifying type of

  -- λ selector -> fixSome f (f selector)

  -- is `∀ {Q} -> F Q -> Q`.

  -- Therefore, the combinators receive something of type `∀ {Q} -> F Q -> Q` and return something of
  -- type `∀ {R} -> F R -> R` (the same type, just alpha-converted for convenience), because that's
  -- what `fix2` and `fix3` and thus the generic fixed-point combinator return.
  -- I.e. the whole unifying type of those combinators is

  -- (∀ {R} -> (∀ {Q} -> F Q -> Q) -> F R -> R)

  -- That's fact (3).

  -- Assembling everything together, we arrive at

  fixBy : {F : Set -> Set}
        -> ((∀ {Q} -> F Q -> Q) -> ∀ {R} -> F R -> R)  -- by fact (3)
        -> (∀ {Q} -> F Q -> F Q) -> ∀ {R} -> F R -> R  -- by fact (1)
  fixBy by f = by (fixBy by f ∘ f)                     -- by fact (2)

  -- Let's now implement particular `by`s:

  by2 : {A B : Set} -> (∀ {Q} -> (A -> B -> Q) -> Q) -> {R : Set} -> (A -> B -> R) -> R
  by2 r k = k (r λ x y -> x) (r λ x y -> y)

  by3 : {A B C : Set} -> (∀ {Q} -> (A -> B -> C -> Q) -> Q) -> {R : Set} -> (A -> B -> C -> R) -> R
  by3 r k = k (r λ x y z -> x) (r λ x y z -> y) (r λ x y z -> z)

  -- and fixed-points combinators from the previous section in terms of what we derived in this one:

  fix2 : ∀ {A B} -> (∀ {Q} -> (A -> B -> Q) -> A -> B -> Q) -> ∀ {R} -> (A -> B -> R) -> R
  fix2 = fixBy by2

  fix3 : ∀ {A B C} -> (∀ {Q} -> (A -> B -> C -> Q) -> A -> B -> C -> Q) -> ∀ {R} -> (A -> B -> C -> R) -> R
  fix3 = fixBy by3

  -- That's it. One `fixBy` to rule them all. The final test:

  evenAndOdd : ∀ {R} -> ((ℕ -> Bool) -> (ℕ -> Bool) -> R) -> R
  evenAndOdd = fix2 $ λ select even odd -> select
    (λ { 0 -> true  ; (suc n) -> odd  n })
    (λ { 0 -> false ; (suc n) -> even n })

  test : Test (evenAndOdd λ x y -> x) (evenAndOdd λ x y -> y)
  test = refl

module LazinessStrictness where
  open UncurriedGeneral using (fixBy)

  -- So what about strictness? `fixBy` is generic enough to allow both lazy and strict derivatives.
  -- The version of strict `fix2` looks like this in Haskell:

  -- apply :: (a -> b) -> a -> b
  -- apply = ($!)

  -- fix2
  --     :: ((a1 -> b1) -> (a2 -> b2) -> a1 -> b1)
  --     -> ((a1 -> b1) -> (a2 -> b2) -> a2 -> b2)
  --     -> ((a1 -> b1) -> (a2 -> b2) -> r) -> r
  -- fix2 f g k = k
  --     (\x1 -> f `apply` fix2 f g (\x y -> x) `apply` fix2 f g (\x y -> y) `apply` x1)
  --     (\x2 -> g `apply` fix2 f g (\x y -> x) `apply` fix2 f g (\x y -> y) `apply` x2)

  -- This is just like the Z combinator is of type `((a -> b) -> a -> b) -> a -> b`, so that it can
  -- be used to get fixed points of functions in a strict language where the Y combinator loops forever.

  -- The version of `fix2` that works in a strict language can be defined as follows:

  by2' : {A₁ B₁ A₂ B₂ : Set}
       -> (∀ {Q} -> ((A₁ -> B₁) -> (A₂ -> B₂) -> Q) -> Q)
       -> {R : Set} -> ((A₁ -> B₁) -> (A₂ -> B₂) -> R) -> R
  by2' r k = k (λ x₁ -> r λ f₁ f₂ -> f₁ x₁) (λ x₂ -> r λ f₁ f₂ -> f₂ x₂)

  fix2' : {A₁ B₁ A₂ B₂ : Set}
        -> (∀ {Q} -> ((A₁ -> B₁) -> (A₂ -> B₂) -> Q) -> (A₁ -> B₁) -> (A₂ -> B₂) -> Q)
        -> {R : Set} -> ((A₁ -> B₁) -> (A₂ -> B₂) -> R) -> R
  fix2' = fixBy by2'

  -- The difference is that in

  by2 : {A B : Set} -> (∀ {Q} -> (A -> B -> Q) -> Q) -> {R : Set} -> (A -> B -> R) -> R
  by2 r k = k (r λ x y -> x) (r λ x y -> y)

  -- both calls to `r` are forced before `k` returns, while in `by2'` additional lambdas that bind
  -- `x₁` and `x₂` block the recursive calls from being forced, so `k` at some point can decide not to
  -- recurse anymore (i.e. not to force recursive calls) and return a result instead.

module StrictPolymorphic where
  open UncurriedGeneral using (fixBy)

  -- `fix2'` discussed in the previous section allows to take the fixed point of two functions,
  -- but those functions have to be monomorphic. It's not an inherent limitation though, by
  -- tweaking `by*` functions we can take the fixed-point of polymorphic mutually recursive
  -- functions:

  module Poly {F₁ G₁ F₂ G₂ : Set -> Set} where
    F = λ (Q : Set) -> (∀ {A} -> F₁ A -> G₁ A) -> (∀ {A} -> F₂ A -> G₂ A) -> Q

    poly-by2' : (∀ {Q} -> F Q -> Q) -> {R : Set} -> F R -> R
    poly-by2' r k = k (λ x₁ -> r λ f₁ f₂ -> f₁ x₁) (λ {A} x₂ -> r λ f₁ f₂ -> f₂ x₂)

    poly-fix2' : (∀ {Q} -> F Q -> F Q) -> {R : Set} -> F R -> R
    poly-fix2' = fixBy poly-by2'

  -- In the same manner we can take the fixed point of a polymorphic and a monomorphic function:

  module PolyMono {B₁ A₂ B₂ : Set} {F₁ : Set -> Set} where
    F = λ (Q : Set) -> (∀ {A} -> F₁ A -> B₁) -> (A₂ -> B₂) -> Q

    poly-mono-by2' : (∀ {Q} -> F Q -> Q) -> {R : Set} -> F R -> R
    poly-mono-by2' r k = k (λ x₁ -> r λ f₁ f₂ -> f₁ x₁) (λ x₂ -> r λ f₁ f₂ -> f₂ x₂)

    poly-mono-fix2' : (∀ {Q} -> F Q -> F Q) -> {R : Set} -> F R -> R
    poly-mono-fix2' = fixBy poly-mono-by2'

  -- So in Plutus Core we can just generate appropriate `by*` functions on the fly depending on
  -- the type schema of each of the functions that we take the fixed point of, while compiling
  -- those functions from Plutus IR.

module ComputeUncurriedGeneral where
  -- You might wonder whether we can define a single `fixN` which receives a natural number and
  -- computes the appropriate fixed-point combinator of mutually recursive functions. E.g.

  -- fixN 2 ~> fix2
  -- fixN 3 ~> fix3

  -- So that we do not even need to specify `by2` and `by3` by ourselves. Yes we can do that, see [2]
  -- (the naming is slightly different there).

  -- Moreover, we can assign a type to `fixN` in pure System Fω, see [3].

module AlternativeFormulation where
  open import Data.Product

  -- In `PartiallyUncurried`, we are forced into a certain amount of unpacking and repacking because
  -- we only Scott-encode one of the tuples at that point. If we Scott-encode both, we end up with a
  -- slightly different formulation.

  -- Uncurry the argument tuple type.
  fix-uncurry : ∀ {A B} -> (A -> B -> A × B) -> A × B
  fix-uncurry f = (uncurry f) (fix-uncurry f)

  -- Scott-encode both tuple types.
  -- Here because the result type is the same we don't need to do anything except change to using
  -- uncurry for Scott tuples. In the inlined version we would just switch from using the tuple projector
  -- functions to using the Scott-tuple selector functions.
  fix-scott : ∀ {A B} -> (A -> B -> ∀ {Q} -> (A -> B -> Q) -> Q) -> ∀ {Q} -> (A -> B -> Q) -> Q
  fix-scott f = (uncurryScott2 f) (fix-scott f)

  -- Rearrange the arguments of `f`
  fix-rearrange : ∀ {A B} -> (∀ {Q} -> (A -> B -> Q) -> A -> B -> Q) -> ∀ {Q} -> (A -> B -> Q) -> Q
  fix-rearrange f k = (uncurryScott2 (f k)) (fix-rearrange f)

  -- Abstract the use of `uncurryScott2`, make point-free-er
  fix-abs : ∀ {A B} -> (∀ {Q} -> (A -> B -> Q) -> A -> B -> Q) -> ∀ {Q} -> (A -> B -> Q) -> Q
  fix-abs {A} {B} f = byish (fix-abs f) ∘ f
    where
      byish : (∀ {Q} -> (A -> B -> Q) -> Q) -> (∀ {R} -> (A -> B -> R) -> R)
      byish r k = (uncurryScott2 k) r

  -- We can now define another version of `fixBy`. Compare with the previous version:
  -- fixBy by f = by (fixBy by f ∘ f)
  -- This version looks like it should be provably equivalent via some kind of fixpoint
  -- "rolling rule" for `fixBy`.
  fixBy : {F : Set -> Set}
        -> ((∀ {Q} -> F Q -> Q) -> ∀ {R} -> F R -> R)
        -> (∀ {Q} -> F Q -> F Q) -> ∀ {R} -> F R -> R
  fixBy by f = by (fixBy by f) ∘ f

  by2 : {A B : Set} -> (∀ {Q} -> (A -> B -> Q) -> Q) -> {R : Set} -> (A -> B -> R) -> R
  by2 r k = k (r λ x y -> x) (r λ x y -> y)

  evenAndOdd : ∀ {R} -> ((ℕ -> Bool) -> (ℕ -> Bool) -> R) -> R
  evenAndOdd = fixBy by2 $ λ select even odd -> select
      (λ { 0 -> true  ; (suc n) -> odd  n })
      (λ { 0 -> false ; (suc n) -> even n })

  test : Test (evenAndOdd sel₁) (evenAndOdd sel₂)
  test = refl

module References where
  -- [1] "Mutual Recursion in Final Encoding", Andreas Herrmann
  -- https://aherrmann.github.io/programming/2016/05/28/mutual-recursion-in-final-encoding/

  -- [2] https://gist.github.com/effectfully/b3185437da14322c775f4a7691b6fe1f#file-mutualfixgenericcompute-agda

  -- [3] https://gist.github.com/effectfully/b3185437da14322c775f4a7691b6fe1f#file-mutualfixgenericcomputenondep-agda
