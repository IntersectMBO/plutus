-- In this document we'll show that having `ifix :: ((k -> *) -> k -> *) -> k -> *` is enough to
-- get `fix :: (k -> k) -> k` for any particular `k`.

module IFixIsEnough where

open import Agda.Primitive

-- First, the definition of `IFix`:

{-# NO_POSITIVITY_CHECK #-}
data IFix {α φ} {A : Set α} (F : (A -> Set φ) -> A -> Set φ) (x : A) : Set φ where
  wrap : F (IFix F) x -> IFix F x

-- We'll be calling `F` a pattern functor and `x` an index.

open import Function

-- The simplest non-trivial case of an n-ary higher-kinded `fix` is

-- fix2 :: ((j -> k -> *) -> j -> k -> *) -> j -> k -> *

-- So we'll start from encoding this fixed-point combinator.

module FixProduct where
  -- In Agda it has the following signature:

  Fix₂ : {A B : Set} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set

  -- One way of getting this type is by going through type-level tuples.

  open import Data.Product

  -- Having (defined for clarity)

  Fixₓ : {A B : Set} -> ((A × B -> Set) -> A × B -> Set) -> A × B -> Set
  Fixₓ = IFix

  -- we can just sprinkle `curry` and `uncurry` in appropriate places and get the desired definition:

  ConciseFix₂ₓ : {A B : Set} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set
  ConciseFix₂ₓ F = curry (Fixₓ (uncurry ∘ F ∘ curry))

  -- which after some expansion becomes

  Fix₂ {A} {B} F = λ x y ->
    Fixₓ (λ Rec -> uncurry (F (λ x′ y′ -> Rec (x′ , y′)))) (x , y)

  -- The main idea here is that since `IFix` receives onle one index, we need to somehow package the
  -- two indices we have (`x` and `y`) together to get a single index. And the simplest solution is
  -- just to make a two-element tuple out of `x` and `y`.

  -- However, this simple solution does not apply to vanilla System F-omega, because we do not have
  -- type-level tuples there. Hence some another way of packaging things together is required.

module FixEncodedProduct where
  -- The fact that we only use tuples at the type level suggests the following encoding of them:

  _×̲_ : Set -> Set -> Set₁  -- Type \x\_-- to get ×̲.
  A ×̲ B = (A -> B -> Set) -> Set

  -- Which is just the usual Church encoding (okay-okay, Boehm-Berarducci encoding)

  _Church×_ : ∀ {ρ} -> Set -> Set -> Set (lsuc ρ)
  _Church×_ {ρ} A B = {R : Set ρ} -> (A -> B -> R) -> R

  -- with `R` (not the type of `R`, but `R` itself) instantiated to `Set`.

  -- Here is a combinator that allows to recurse over `A ×̲ B` just like `Fixₓ` from the above
  -- allowed to recurse over `A × B`:

  abstract  -- We'll be marking some things as `abstract` just to get nice output from Agda when
            -- we ask it to normalize things.
    Fixₓ̲ : {A B : Set} -> ((A ×̲ B -> Set) -> A ×̲ B -> Set) -> A ×̲ B -> Set  -- Type \_x\_-- to get ₓ̲.
    Fixₓ̲ = IFix

  -- Now we have `A ×̲ B -> Set` appearing thrice in a type signature. We can simplify this expression:

  -- A ×̲ B -> Set                    ~ (by definition)
  -- ((A -> B -> Set) -> Set) -> Set ~ (see below)
  -- A -> B -> Set

  -- The fact that we can go from `((A -> B -> Set) -> Set) -> Set` to `A -> B -> Set` is related to
  -- the fact that triple negation is equivalent to single negation in a type theory. In fact, we can
  -- go from any `((A -> R) -> R) -> R` to `A -> R` and vice versa as witnessed by

  module TripleNegation where
    tripleToSingle : ∀ {α ρ} {A : Set α} {R : Set ρ}
                   -> (((A -> R) -> R) -> R) -> A -> R
    tripleToSingle h x = h λ f -> f x

    singleToTriple : ∀ {α ρ} {A : Set α} {R : Set ρ}
                   -> (A -> R) -> ((A -> R) -> R) -> R
    singleToTriple f h = h f

  -- Here are the `curry` and `uncurry` combinators then:

  curryₓ̲ : ∀ {α β ρ} {A : Set α} {B : Set β} {R : Set ρ}
         -> (((A -> B -> R) -> R) -> R) -> A -> B -> R
  curryₓ̲ h x y = h λ f -> f x y

  abstract
    uncurryₓ̲ : ∀ {α β ρ} {A : Set α} {B : Set β} {R : Set ρ}
             -> (A -> B -> R) -> ((A -> B -> R) -> R) -> R
    uncurryₓ̲ f h = h f

  -- And the definition of `ConciseFix₂` following the same pattern as the one from the previous section:

  ConciseFix₂ : {A B : Set} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set
  ConciseFix₂ F = curryₓ̲ (Fixₓ̲ (uncurryₓ̲ ∘ F ∘ curryₓ̲))

  -- Compare to the previous one:

  -- ConciseFix₂ₓ : {A B : Set} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set
  -- ConciseFix₂ₓ F = curry (Fixₓ (uncurry ∘ F ∘ curry))

  -- We can now ask Agda to normalize `ConciseFix₂`. After some alpha-renaming we get

  NormedConciseFix₂ : {A B : Set} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set
  NormedConciseFix₂ {A} {B} F = λ x y ->
    Fixₓ̲ (λ Rec -> uncurryₓ̲ (F (λ x′ y′ -> Rec (λ On -> On x′ y′)))) (λ On -> On x y)

  -- which is very similar to what we had previously

  -- Fix₂ₓ : {A B : Set} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set
  -- Fix₂ₓ {A} {B} F = λ x y ->
  --   Fixₓ (λ Rec -> uncurry (F (λ x′ y′ -> Rec (x′ , y′)))) (x , y)

  -- except we now have `λ On -> On x y` instead of `(x , y)`. What is this new thing? Well:

  _,̲_ : {A B : Set} -> A -> B -> A ×̲ B  -- Type ,\_-- to get ,̲.
  _,̲_ {A} {B} x y = λ (On : A -> B -> Set) -> On x y

  -- it's just a new way to package `x` and `y` together without ever touching tuples-as-data. Here
  -- we use a function in order to turn two indices into a single one.
  -- `λ On -> On x y` is the Church-encoded version of `(x , y)` (where `_,_` constructs data).

  -- Using `_,̲_` for clarity we arrive at the following:

  Fix₂ : {A B : Set} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set
  Fix₂ {A} {B} F = λ x y ->
    Fixₓ̲ (λ Rec -> uncurryₓ̲ (F (λ x′ y′ -> Rec (x′ ,̲ y′)))) (x ,̲ y)

  -- Compare again to the definition from the previous section:

  -- Fix₂ₓ : {A B : Set} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set
  -- Fix₂ₓ {A} {B} F = λ x y ->
  --   Fixₓ (λ Rec -> uncurry (F (λ x′ y′ -> Rec (x′ , y′)))) (x , y)

  -- The pattern is clearly the same. But now we do not use any type-level data, only lambda abstractions
  -- and function applications which we do have at the type level in System F-omega, so it all is legal
  -- there.

module Direct where
  -- In this section we'll encode other higher-kinded `Fix`es in addition to `Fix₂` from
  -- the previous section.

  -- `Fix₂` with everything inlined and computed down to normal form looks like this:

  Fix₂ : {A B : Set} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set
  Fix₂ {A} {B} F = λ x y ->
    IFix (λ Rec Spine -> Spine (F λ x′ y′ -> Rec (λ On -> On x′ y′))) (λ On -> On x y)

  -- `Fix₃` is the same, just an additional argument `z` (and `z′`) is added here and there:

  Fix₃ : {A B C : Set} -> ((A -> B -> C -> Set) -> A -> B -> C -> Set) -> A -> B -> C -> Set
  Fix₃ F = λ x y z ->
    IFix (λ Rec Spine -> Spine (F λ x′ y′ z′ -> Rec (λ On -> On x′ y′ z′))) (λ On -> On x y z)

  -- Correspondingly, `Fix₁` is `Fix₂` minus `y` (and `y′`):

  Fix₁ : {A : Set} -> ((A -> Set) -> A -> Set) -> A -> Set
  Fix₁ F = λ x ->
    IFix (λ Rec Spine -> Spine (F λ x′ -> Rec (λ On -> On x′))) (λ On -> On x)

  -- But `Fix₁` has the same signature as `IFix`, so we can just define it as

  Fix₁′ : {A : Set} -> ((A -> Set) -> A -> Set) -> A -> Set
  Fix₁′ = IFix

  -- `Fix₀` can be defined in the same manner as `Fix₂`, except we strip off all indices and encode
  -- the empty tuple as `λ On -> On`.

  Fix₀ : (Set -> Set) -> Set
  Fix₀ F =
    IFix (λ Rec spine -> spine (F (Rec (λ On -> On)))) (λ On -> On)

  -- There is another way to define `Fix₀`, we can just pass a dummy argument as an index:

  Fix₀′′ : (Set -> Set) -> Set
  Fix₀′′ F = IFix (λ Rec ⊥ -> F (Rec ⊥)) ((A : Set) -> A)

  -- The argument is never used and is only needed, because we have to provide *some* index.

  -- Another way is to pass `F` itself as an index rather than some dummy argument:

  Fix₀′ : (Set -> Set) -> Set
  Fix₀′ = IFix λ Rec F -> F (Rec F)

  -- This is perhaps the nicest way.

module Generic where
  -- In this section we'll define `FixBy` which generalizes all of `Fix₀`, `Fix₁`, `Fix₂`, etc.

  -- In

  -- Fix₂ : {A B : Set} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set
  -- Fix₂ {A} {B} F = λ x y ->
  --   IFix (λ Rec Spine -> Spine (F λ x′ y′ -> Rec (λ On -> On x′ y′))) (λ On -> On x y)

  -- we see that wherever `x` and `y` are bound, they're also packaged by `λ On -> On ...` and the
  -- entire thing is passed to something else. This holds for the inner

  -- λ x′ y′ -> Rec (λ On -> On x′ y′)

  -- as well as for the outer

  -- λ x y -> ... (λ On -> On x y)

  -- This pattern can be easily abstracted:

  FixBy : ∀ {κ φ} {K : Set κ} -> (((K -> Set φ) -> Set φ) -> K) -> (K -> K) -> K
  FixBy WithSpine F = WithSpine (IFix λ Rec Spine -> Spine (F (WithSpine Rec)))

  -- `WithSpine` encapsulates spine construction and feeds constructed spines to a continuation.

  -- Being equipped like that we can easily define an n-ary higher-kinded `fix` for any `n`:

  Fix₀ : ∀ {φ} -> (Set φ -> Set φ) -> Set φ
  Fix₀ = FixBy λ Cont -> Cont λ On -> On

  Fix₁ : ∀ {α φ} {A : Set α} -> ((A -> Set φ) -> A -> Set φ) -> A -> Set φ
  Fix₁ = FixBy λ Cont x -> Cont λ On -> On x

  Fix₂ : ∀ {α β φ} {A : Set α} {B : Set β}
       -> ((A -> B -> Set φ) -> A -> B -> Set φ) -> A -> B -> Set φ
  Fix₂ = FixBy λ Cont x y -> Cont λ On -> On x y

  Fix₃ : ∀ {α β γ φ} {A : Set α} {B : Set β} {C : Set γ}
       -> ((A -> B -> C -> Set φ) -> A -> B -> C -> Set φ) -> A -> B -> C -> Set φ
  Fix₃ = FixBy λ Cont x y z -> Cont λ On -> On x y z

module DirectGenericSame where
  open import Relation.Binary.PropositionalEquality

  -- The 'direct' and 'generic' encodings result in literally the same code. Here are a few examples:

  directIsGeneric₀ : ∀ {F} -> Direct.Fix₀ F ≡ Generic.Fix₀ F
  directIsGeneric₀ = refl

  directIsGeneric₁ : ∀ {A F} {x : A} -> Direct.Fix₁ F x ≡ Generic.Fix₁ F x
  directIsGeneric₁ = refl

  directIsGeneric₂ : ∀ {A B F} {x : A} {y : B} -> Direct.Fix₂ F x y ≡ Generic.Fix₂ F x y
  directIsGeneric₂ = refl

  directIsGeneric₃ : ∀ {A B C F} {x : A} {y : B} {z : C} -> Direct.Fix₃ F x y z ≡ Generic.Fix₃ F x y z
  directIsGeneric₃ = refl

-- Tests:

module Test where
  open import Data.Maybe.Base
  open Generic

  module Nat where
    Nat : Set
    Nat = Fix₀ Maybe

    pattern zero  = wrap nothing
    pattern suc n = wrap (just n)

    elimNat
        : {P : Nat -> Set}
        -> P zero
        -> (∀ n -> P n -> P (suc n))
        -> ∀ n
        -> P n
    elimNat z f  zero   = z
    elimNat z f (suc n) = f n (elimNat z f n)

  module List where
    data ListF (R : Set -> Set) A : Set where
      nilF  : ListF R A
      consF : A -> R A -> ListF R A

    List : Set -> Set
    List = Fix₁ ListF

    pattern []       = wrap nilF
    pattern _∷_ x xs = wrap (consF x xs)

    elimList
        : ∀ {A} {P : List A -> Set}
        -> P []
        -> (∀ x xs -> P xs -> P (x ∷ xs))
        -> ∀ xs
        -> P xs
    elimList z f  []      = z
    elimList z f (x ∷ xs) = f x xs (elimList z f xs)

  module InterleavedList where
    open import Data.Unit.Base
    open import Data.Bool.Base
    open import Data.Nat.Base
    open import Data.Sum.Base
    open import Data.Product

    InterleavedList : Set -> Set -> Set
    InterleavedList = Fix₂ λ Rec A B -> ⊤ ⊎ A × B × Rec B A

    pattern []          = wrap (inj₁ tt)
    pattern cons x y ps = wrap (inj₂ (x , y , ps))

    example_interleavedList : InterleavedList ℕ Bool
    example_interleavedList = cons 0 false ∘′ cons true 1 ∘′ cons 2 false $ []

    elimInterleavedList
        : ∀ {A B} {P : ∀ {A B} -> InterleavedList A B -> Set}
        -> (∀ {A B} -> P {A} {B} [])
        -> (∀ {A B} x y ps -> P {A} {B} ps -> P (cons x y ps))
        -> ∀ ps
        -> P {A} {B} ps
    elimInterleavedList z f  []           = z
    elimInterleavedList z f (cons x y ps) = f x y ps (elimInterleavedList z f ps)

module Unicode where
  -- This file uses the following unicode:
  -- ×̲ 0xD7 \x\_--
