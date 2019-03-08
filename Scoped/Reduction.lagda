\begin{code}
module Scoped.Reduction where
\end{code}

\begin{code}
open import Scoped

open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Product
\end{code}

\begin{code}
data Value : ∀{n} → ScopedTm n → Set where
data Error : ∀{n} → ScopedTm n → Set where

data _—→_ {n} : ScopedTm n → ScopedTm n → Set where
  
\end{code}

\begin{code}
data _—→⋆_ {n} : ScopedTm n → ScopedTm n → Set where
  refl  : {t : ScopedTm n} → t —→⋆ t
  trans : {t t' t'' : ScopedTm n} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}


\begin{code}
progress : (t : ScopedTm Z) → (Value {Z} t ⊎ Error t) ⊎ Σ (ScopedTm Z) λ t' → t —→ t'
progress (` ())
progress (Λ K t) = {!!}
progress (t ·⋆ A) = {!!}
progress (ƛ A t) = {!!}
progress (t · u) = {!!}
progress (con x) = {!!}
progress (error x) = {!!}
progress (builtin x) = {!!}
\end{code}

\begin{code}
open import Data.Nat
open import Data.Maybe

run : (t : ScopedTm Z) → ℕ → Σ (ScopedTm Z) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')
run t 0       = t , (refl , inl nothing)
run t (suc n) with progress t
run t (suc n) | inl (inl vt) = t , refl , inl (just vt)
run t (suc n) | inl (inr et) = t , refl , inr et
run t (suc n) | inr (t' , p) with run t' n
run t (suc n) | inr (t' , p) | t'' , q , mvt'' = t'' , trans p q , mvt''
\end{code}
