-- This document shows how to encode GADTs using `IFix`.

{-# OPTIONS --type-in-type #-}

module ScottVec where

-- The kind of church-encoded type-level natural numbers.
Nat = (Set -> Set) -> Set -> Set

zero : Nat
zero = λ f z -> z

suc : Nat -> Nat
suc = λ n f z -> f (n f z)

plus : Nat -> Nat -> Nat
plus = λ n m f z -> n f (m f z)

-- Our old friend.
{-# NO_POSITIVITY_CHECK #-}
record IFix {I : Set} (F : (I -> Set) -> I -> Set) (i : I) : Set where
  constructor wrap
  field unwrap : F (IFix F) i
open IFix

-- Scott-encoded vectors (a vector is a list with statically-known length).

-- As usually the pattern vector of a Scott-encoded data type encodes pattern-matching.
VecF : Set -> (Nat -> Set) -> Nat -> Set
VecF
  = λ A Rec n
  -> (R : Nat -> Set)                  -- The type of the result depends on the vector's length.
  -> (∀ p -> A -> Rec p -> R (suc p))  -- The encoded `cons` constructor.
  -> R zero                            -- The encoded `nil` constructor.
  -> R n

Vec : Set -> Nat -> Set
Vec = λ (A : Set) -> IFix (VecF A)

nil : ∀ A -> Vec A zero
nil = λ A -> wrap λ R f z -> z

cons : ∀ A n -> A -> Vec A n -> Vec A (suc n)
cons = λ A n x xs -> wrap λ R f z -> f n x xs

open import Data.Empty
open import Data.Unit.Base
open import Data.Nat.Base using (ℕ; _+_)

-- Type-safe `head`.
head : ∀ A n -> Vec A (suc n) -> A
head A n xs =
  unwrap
    xs
    (λ p -> p (λ _ -> A) ⊤)  -- `p (λ _ -> A) ⊤` returns `A` when `p` is `suc p'` for some `p'`
                             -- and `⊤` when `p` is `zero`
    (λ p x xs' -> x)         -- In the `cons` case `suc p (λ _ -> A) ⊤` reduces to `A`,
                             -- hence we return the list element of type `A`.
    tt                       -- In the `nil` case `zero (λ _ -> A) ⊤` reduces to `⊤`,
                             -- hence we return the only value of that type.

{- Note [Type-safe `tail`]
It's not obvious if type-safe `tail` can be implemented with this setup. This is because even
though `Vec` is Scott-encoded, the type-level natural are Church-encoded (obviously we could
have Scott-encoded type-level naturals in Agda just as well, but not in Plutus Core), which
makes `pred` hard, which makes `tail` non-trivial.

I did try using Scott-encoded naturals in Agda, that makes `tail` even more straightforward
than `head`:

    tail : ∀ A n -> Vec A (suc n) -> Vec A n
    tail A n xs =
      unwrap
        xs
        (λ p -> ((B : ℕ -> Set) -> B (pred p) -> B n) -> Vec A n)
        (λ p x xs' coe -> coe (Vec A) xs')
        (λ coe -> coe (Vec A) (nil A))
        (λ B x -> x)
-}

-- Here we pattern-match on `xs` and if it's non-empty, i.e. of type `Vec ℕ (suc p)` for some `p`,
-- then we also get access to a coercion function that allows us to coerce the second list from
-- `Vec ℕ n` to the same `Vec ℕ (suc p)` and call the type-safe `head` over it.
-- Note that we don't even need to encode the `n ~ suc p` and `n ~ zero` equality constraints in
-- the definition of `vecF` and can recover coercions along those constraints by adding the
-- `Vec ℕ n -> Vec ℕ p` argument to the motive.
sumHeadsOr0 : ∀ n -> Vec ℕ n -> Vec ℕ n -> ℕ
sumHeadsOr0 n xs ys =
  unwrap
    xs
    (λ p -> (Vec ℕ n -> Vec ℕ p) -> ℕ)
    (λ p i _ coe -> i + head ℕ p (coe ys))
    (λ _ -> 0)
    (λ x -> x)
