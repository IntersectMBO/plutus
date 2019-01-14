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
  Π   : ∀{n} → ScopedTy n → ScopedTy (suc n)
  ƛ   : ∀{n} → ScopedTy n → ScopedTy (suc n)
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
  
