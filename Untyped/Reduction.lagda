\begin{code}
module Untyped.Reduction where
\end{code}

\begin{code}
open import Untyped.Term
open import Data.Nat
open import Data.Product
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Maybe
\end{code}


\begin{code}
data _—→_ {n} : n ⊢ → n ⊢ → Set where

data Value : ∀{n} → n ⊢ → Set where
  V-ƛ : ∀{n} → (t : suc n ⊢) → Value (ƛ t)
\end{code}

\begin{code}
data _—→⋆_ {n} : n ⊢ → n ⊢ → Set where
  refl : {t : n ⊢} → t —→⋆ t
\end{code}

\begin{code}
progress : (t : 0 ⊢) → Σ (0 ⊢) λ t' → Value t ⊎ t —→ t'
progress = {!!}
\end{code}

\begin{code}
run : (t : 0 ⊢) → ℕ → Σ (0 ⊢) λ t' → t —→⋆ t' × Maybe (Value t') 
run t zero    = t , refl , nothing
run (` ()) (suc n)
run (ƛ t) (suc n) = ƛ t , (refl , (just (V-ƛ t)))
run (t · u) (suc n) with progress t
... | p = {!!}
run (con x) (suc n) = {!!}
run (builtin x) (suc n) = {!!}
run error (suc n) = {!!}

\end{code}
