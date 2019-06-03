\begin{code}
module Untyped.RenamingSubstitution where
\end{code}

\begin{code}
open import Untyped

open import Data.Nat
open import Data.Fin
open import Data.List
open import Relation.Binary.PropositionalEquality
\end{code}

\begin{code}
Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

ext : ∀{m n} → Ren m n → Ren (suc m) (suc n)
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

ren     : ∀{m n} → Ren m n → m ⊢ → n ⊢
renList : ∀{m n} → Ren m n → List (m ⊢) → List (n ⊢)

ren ρ (` x)          = ` (ρ x)
ren ρ (ƛ x t)        = ƛ x (ren (ext ρ) t)
ren ρ (t · u)        = ren ρ t · ren ρ u
ren ρ (con tcn)      = con tcn
ren ρ (builtin b ts) = builtin b (renList ρ ts)
ren ρ error          = error

renList ρ []       = []
renList ρ (t ∷ ts) = ren ρ t ∷ renList ρ ts

ext-cong : ∀{m n}{ρ ρ' : Ren m n}
  → (∀ α → ρ α ≡ ρ' α)
  → (α : Fin (suc m))
  → ext ρ α ≡ ext ρ' α
ext-cong p zero    = refl
ext-cong p (suc α) = cong suc (p α)

ren-cong : ∀{m n}{ρ ρ' : Ren m n}
  → (∀ α → ρ α ≡ ρ' α)
  → (t : m ⊢)
  → ren ρ t ≡ ren ρ' t

renList-cong : ∀{m n}{ρ ρ' : Ren m n}
  → (∀ α → ρ α ≡ ρ' α)
  → (ts : List(m ⊢))
  → renList ρ ts ≡ renList ρ' ts
renList-cong p []       = refl
renList-cong p (t ∷ ts) = cong₂ _∷_ (ren-cong p t) (renList-cong p ts)

ren-cong p (` x)          = cong ` (p x)
ren-cong p (ƛ x t)        = cong (ƛ x) (ren-cong (ext-cong p) t)
ren-cong p (t · u)        = cong₂ _·_ (ren-cong p t) (ren-cong p u)
ren-cong p (con c)        = refl
ren-cong p (builtin b ts) = cong (builtin b) (renList-cong p ts)
ren-cong p error          = refl

--

Sub : ℕ → ℕ → Set
Sub m n = Fin m → n ⊢

exts : ∀{m n} → Sub m n → Sub (suc m) (suc n)
exts ρ zero = ` zero
exts ρ (suc x) = ren suc (ρ x)

sub     : ∀{m n} → Sub m n → m ⊢ → n ⊢
subList : ∀{m n} → Sub m n → List (m ⊢) → List (n ⊢)

sub σ (` x)          = σ x
sub σ (ƛ x t)        = ƛ x (sub (exts σ) t) 
sub σ (t · u)        = sub σ t · sub σ u
sub σ (con tcn)      = con tcn
sub σ (builtin b ts) = builtin b (subList σ ts)
sub σ error          = error

subList σ []       = []
subList σ (t ∷ ts) = sub σ t ∷ subList σ ts

extend : ∀{m n} → Sub m n → n ⊢ → Sub (suc m) n
extend σ t zero    = t
extend σ t (suc x) = σ x

_[_] : ∀{n} → suc n ⊢ → n ⊢ → n ⊢
t [ u ] = sub (extend ` u) t
\end{code}
