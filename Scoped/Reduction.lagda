\begin{code}
module Scoped.Reduction where
\end{code}

\begin{code}
open import Scoped
open import Scoped.RenamingSubstitution

open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Product
\end{code}

\begin{code}
infix 2 _—→_
\end{code}

\begin{code}
data Value {n} : ScopedTm n → Set where
  V-ƛ : (A : ScopedTy ∥ n ∥)(t : ScopedTm (S n)) → Value (ƛ A t)
  V-Λ : ∀ K (t : ScopedTm (T n)) → Value (Λ K t)
--  V-con : (tcn : TermCon) → Value (con {n} tcn)

-- a term that satisfies this predicate has an error term in it somewhere
-- or we encounter a type error
data Error {n} : ScopedTm n → Set where
   E-error : (A : ScopedTy ∥ n ∥) → Error (error A)
   E-·     : {L M : ScopedTm n} → Error L → Error (L · M)
   E-·⋆    : {L : ScopedTm n}{A : ScopedTy ∥ n ∥} → Error L → Error (L ·⋆ A)
   E-Λ·    : ∀{K}{L : ScopedTm (T n)}{M : ScopedTm n} → Error (Λ K L · M)
   E-ƛ·⋆   : ∀{B : ScopedTy ∥ n ∥}{L : ScopedTm (S n)}{A : ScopedTy ∥ n ∥}
           → Error (ƛ B L ·⋆ A)

   -- place holder for stuff that isn't implemented yet...
   todo : {M : ScopedTm n} → Error M
   
data _—→_ {n} : ScopedTm n → ScopedTm n → Set where
  ξ-· : {L L' M : ScopedTm n} → L —→ L' → L · M —→ L' · M
  ξ-·⋆ : {L L' : ScopedTm n}{A : ScopedTy ∥ n ∥} → L —→ L' → L ·⋆ A —→ L' ·⋆ A
  β-ƛ : {A : ScopedTy ∥ n ∥}{L : ScopedTm (S n)}{M : ScopedTm n}
      → (ƛ A L) · M —→ (L [ M ])
  β-Λ : ∀{K}{L : ScopedTm (T n)}{A : ScopedTy ∥ n ∥}
      → (Λ K L) ·⋆ A —→ (L [ A ]⋆)
\end{code}

\begin{code}
data _—→⋆_ {n} : ScopedTm n → ScopedTm n → Set where
  refl  : {t : ScopedTm n} → t —→⋆ t
  trans : {t t' t'' : ScopedTm n} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
progress : (t : ScopedTm Z)
         → (Value {Z} t ⊎ Error t) ⊎ Σ (ScopedTm Z) λ t' → t —→ t'
progress (` ())
progress (Λ K t) = inl (inl (V-Λ K t))
progress (t ·⋆ A) with progress t
progress (.(ƛ B t) ·⋆ A) | inl (inl (V-ƛ B t)) = inl (inr E-ƛ·⋆)
progress (.(Λ K t) ·⋆ A) | inl (inl (V-Λ K t)) = inr (t [ A ]⋆ , β-Λ)
progress (t ·⋆ A) | inl (inr p) = inl (inr (E-·⋆ p))
progress (t ·⋆ A) | inr (t' , p) = inr (t' ·⋆ A , ξ-·⋆ p)
progress (ƛ A t) = inl (inl (V-ƛ A t))
progress (t · u) with progress t
progress (.(ƛ A t) · u) | inl (inl (V-ƛ A t)) = inr (t [ u ] , β-ƛ)
progress (.(Λ K t) · u) | inl (inl (V-Λ K t)) = inl (inr E-Λ·)

progress (t · u) | inl (inr p) = inl (inr (E-· p))
progress (t · u) | inr (t' , p) = inr (t' · u , ξ-· p)
progress (con x) = inl (inr todo)
progress (error p) = inl (inr (E-error p))
progress (builtin b As ts) = inl (inr todo)
\end{code}

\begin{code}
open import Data.Nat
open import Data.Maybe

run : (t : ScopedTm Z) → ℕ
    → Σ (ScopedTm Z) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')
run t 0       = t , (refl , inl nothing) -- out of fuel
run t (suc n) with progress t
run t (suc n) | inl (inl vt) = t , refl , inl (just vt)
run t (suc n) | inl (inr et) = t , refl , inr et
run t (suc n) | inr (t' , p) with run t' n
run t (suc n) | inr (t' , p) | t'' , q , mvt'' = t'' , trans p q , mvt''
\end{code}
