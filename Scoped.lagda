\begin{code}
module Scoped where
\end{code}

\begin{code}
open import Data.Nat
open import Data.Fin
\end{code}

\begin{code}
data ScopedKind : Set where
  *   : ScopedKind
  _⇒_ : ScopedKind → ScopedKind → ScopedKind

data ScopedTy : ℕ → Set where
  `   : ∀{n} → Fin n → ScopedTy n
  _⇒_ : ∀{n} → ScopedTy n → ScopedTy n → ScopedTy n
  Π   : ∀{n} → ScopedKind → ScopedTy (suc n) → ScopedTy n
  ƛ   : ∀{n} → ScopedKind → ScopedTy (suc n) → ScopedTy n
  _·_ : ∀{n} → ScopedTy n → ScopedTy n → ScopedTy n

data Weirdℕ : Set where
  Z : Weirdℕ
  S : Weirdℕ → Weirdℕ
  T : Weirdℕ → Weirdℕ

data WeirdFin : Weirdℕ → Set where
  Z : ∀{n} → WeirdFin (S n)
  S : ∀{n} → WeirdFin n → WeirdFin (S n)
  T : ∀{n} → WeirdFin n → WeirdFin (T n)

∥_∥ : Weirdℕ → ℕ
∥ Z ∥   = zero
∥ S n ∥ = suc ∥ n ∥
∥ T n ∥ = ∥ n ∥

data ScopedTm : Weirdℕ → Set where
  `    : ∀{n} → WeirdFin n → ScopedTm n 
  Λ    : ∀{n} → ScopedTm (S n) → ScopedTm n
  _·⋆_ : ∀{n} → ScopedTm n → ScopedTy ∥ n ∥ → ScopedTm n
  ƛ    : ∀{n} → ScopedTm (S n) → ScopedTm n
  _·_  : ∀{n} → ScopedTm n → ScopedTm n → ScopedTm n


open import Raw
-- should just use ordinary kind for everything
deBruijnifyK : RawKind → ScopedKind
deBruijnifyK * = *
deBruijnifyK (K ⇒ J) = deBruijnifyK K ⇒ deBruijnifyK J


open import Data.Vec hiding (_>>=_; map)
open import Data.Maybe
open import Data.String
open import Relation.Nullary
open import Category.Monad
import Level
open RawMonad {f = Level.zero} monad

velemIndex : String → ℕ → ∀{n} → Vec String n → Maybe (Fin n)
velemIndex x n [] = nothing
velemIndex x n (x' ∷ xs) with x Data.String.≟ x'
velemIndex x zero    (x' ∷ xs) | yes p = just zero
velemIndex x (suc n) (x' ∷ xs) | yes p = map suc (velemIndex x n xs)
velemIndex x n       (x' ∷ xs) | no ¬p = map suc (velemIndex x n xs)

deBruijnifyTy : ∀{n} → Vec String n → RawTy → Maybe (ScopedTy n)
deBruijnifyTy g (` α) = map ` (velemIndex α 0 g)
deBruijnifyTy g (A ⇒ B) = do
  A ← deBruijnifyTy g A
  B ← deBruijnifyTy g B
  return (A ⇒ B)
deBruijnifyTy g (Π x K B) =
  map (Π (deBruijnifyK K)) (deBruijnifyTy (x ∷ g) B)
deBruijnifyTy g (ƛ x K B) =
  map (ƛ (deBruijnifyK K)) (deBruijnifyTy (x ∷ g) B)
deBruijnifyTy g (A · B) = do
  A ← deBruijnifyTy g A
  B ← deBruijnifyTy g B
  return (A · B)

