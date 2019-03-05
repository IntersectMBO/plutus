\begin{code}
module Untyped.Reduction where
\end{code}

\begin{code}
open import Untyped.Term
open import Untyped.RenamingSubstitution

open import Data.Nat
open import Data.Product
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Maybe
open import Data.List hiding ([_])
\end{code}

\begin{code}
infix 2 _—→_
\end{code}


\begin{code}
-- for untyped reduction, error also includes thing like impossible
-- applications
data Error {n} : n ⊢ → Set where
  E-error : Error error
\end{code}

\begin{code}
data _—→_ {n} : n ⊢ → n ⊢ → Set where
  ξ-· : {L L' : n ⊢}{M : n ⊢} → L —→ L' → L · M —→ L' · M
  E-· : {L : n ⊢}{M : n ⊢} → Error L → L · M —→ error
  E-con : {tcn : TermCon}{L : n ⊢} → con tcn · L —→ error

  β-ƛ : {L : suc n ⊢}{M : n ⊢} → ƛ L · M —→ L [ M ]

data Value {n} : ∀{n} → n ⊢ → Set where
  V-ƛ : (t : suc n ⊢) → Value (ƛ t)
  V-con : (tcn : TermCon) → Value (con {n} tcn)
\end{code}


\begin{code}
data _—→⋆_ {n} : n ⊢ → n ⊢ → Set where
  refl  : {t : n ⊢} → t —→⋆ t
  trans : {t t' t'' : n ⊢} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
progress : (t : 0 ⊢) → (Value {0} t ⊎ Error t) ⊎ Σ (0 ⊢) λ t' → t —→ t'
progressList : List (0 ⊢) → {!!}


progress (` ())
progress (ƛ t)        = inl (inl (V-ƛ t))
progress (t · u)      with progress t
progress (.(ƛ t) · u)     | inl (inl (V-ƛ t))     = inr (t [ u ] , β-ƛ)
progress (.(con tcn) · u) | inl (inl (V-con tcn)) = inr (error , E-con)
progress (t · u)      | inl (inr e)        = inr (error , E-· e)
progress (t · u)      | inr (t' , p) = inr (t' · u  , ξ-· p)
progress (con tcn)    = inl (inl (V-con tcn))
progress (builtin ts) = {! progressList ts !}
progress error        = inl (inr E-error)

progressList = {!!}
\end{code}

\begin{code}
run : (t : 0 ⊢) → ℕ → Σ (0 ⊢) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')
run t 0       = t , (refl , inl nothing)
run t (suc n) with progress t
run t (suc n) | inl (inl vt) = t , refl , inl (just vt)
run t (suc n) | inl (inr et) = t , refl , inr et
run t (suc n) | inr (t' , p) with run t' n
run t (suc n) | inr (t' , p) | t'' , q , mvt'' = t'' , trans p q , mvt''
\end{code}
