module Lang where

open import Haskell.Prelude hiding (e)

data Exp (a : Set) : Set where
  Val : Nat → Exp a
  Var : a → Exp a
  Add : Exp a → Exp a → Exp a

variable
  e e1 e2 e3 e4 : Exp a

instance
  postulate
    expShow : ⦃ Show a ⦄ → Show (Exp a)

{-# COMPILE AGDA2HS Exp deriving Show #-}

eval : (a -> Nat) -> Exp a -> Nat
eval η (Var x) = η x
eval η (Val n) = n
eval η (Add e1 e2) = eval η e1 + eval η e2

{-# COMPILE AGDA2HS eval #-}

-- Equational Specification

data _≃_ : Exp a → Exp a → Set where
  reflE : e ≃ e
  symE  : e1 ≃ e2 → e2 ≃ e1
  transE : e1 ≃ e2 → e2 ≃ e3 → e1 ≃ e3

  congE : e1 ≃ e2 → e3 ≃ e4 → Add e1 e3 ≃ Add e2 e4

  lunit : Add (Val 0) e ≃ e
  runit : Add e (Val 0) ≃ e
  assoc : Add (Add e1 e2) e3 ≃ Add e1 (Add e2 e3)

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

-- Proof that eval implmenents the spec

eval-correct1 : ∀ η → e1 ≃ e2 → eval η e1 ≡ eval η e2
eval-correct1 η reflE = refl
eval-correct1 η (symE p) = sym (eval-correct1 η p)
eval-correct1 η (transE p q) = trans (eval-correct1 η p) (eval-correct1 η q)
eval-correct1 η (congE p q) = cong₂ _+_ (eval-correct1 η p) (eval-correct1 η q)
eval-correct1 η lunit = refl
eval-correct1 η runit = +-identityʳ _
eval-correct1 η (assoc {e1 = e1}{e2}{e3}) = +-assoc (eval η e1) (eval η e2) (eval η e3)


-- stability
eval-correct2 : ∀ (η : a → Nat) n → eval η (Val n) ≡ n
eval-correct2 η n = refl

eval-correct3 : ∀ (η : a → Nat) x → eval η (Var x) ≡ η x
eval-correct3 η n = refl
