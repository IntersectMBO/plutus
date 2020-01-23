\begin{code}
module Untyped.RenamingSubstitution where
\end{code}

\begin{code}
open import Untyped

open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Function
\end{code}

\begin{code}
Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

lift : ∀{m n} → Ren m n → Ren (suc m) (suc n)
lift ρ zero = zero
lift ρ (suc x) = suc (ρ x)

ren     : ∀{m n} → Ren m n → m ⊢ → n ⊢
renList : ∀{m n} → Ren m n → List (m ⊢) → List (n ⊢)

ren ρ (` x)          = ` (ρ x)
ren ρ (ƛ t)          = ƛ (ren (lift ρ) t)
ren ρ (t · u)        = ren ρ t · ren ρ u
ren ρ (con tcn)      = con tcn
ren ρ (builtin b ts) = builtin b (renList ρ ts)
ren ρ error          = error

renList ρ []       = []
renList ρ (t ∷ ts) = ren ρ t ∷ renList ρ ts

weaken : ∀{n} → n ⊢ → suc n ⊢
weaken t = ren suc t

lift-cong : ∀{m n}{ρ ρ' : Ren m n}
  → (∀ α → ρ α ≡ ρ' α)
  → (α : Fin (suc m))
  → lift ρ α ≡ lift ρ' α
lift-cong p zero    = refl
lift-cong p (suc α) = cong suc (p α)

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
ren-cong p (ƛ t)          = cong ƛ (ren-cong (lift-cong p) t)
ren-cong p (t · u)        = cong₂ _·_ (ren-cong p t) (ren-cong p u)
ren-cong p (con c)        = refl
ren-cong p (builtin b ts) = cong (builtin b) (renList-cong p ts)
ren-cong p error          = refl

ren-id : ∀{n} → (t : n ⊢) → t ≡ ren id t

renList-id : ∀{n} → (ts : List (n ⊢)) → ts ≡ renList id ts
renList-id []       = refl
renList-id (t ∷ ts) = cong₂ _∷_ (ren-id t) (renList-id ts)

lift-id : ∀{n} → (α : Fin (suc n)) → id α ≡ lift id α
lift-id zero    = refl
lift-id (suc α) = refl

ren-id (` x)           = refl
ren-id (ƛ t)           = cong
  ƛ
  (trans
    (ren-id t)
    (ren-cong lift-id t)) 
ren-id (t · u)         = cong₂ _·_ (ren-id t) (ren-id u)
ren-id (con c)         = refl
ren-id (builtin bn ts) = cong (builtin bn) (renList-id ts)
ren-id error           = refl

--

Sub : ℕ → ℕ → Set
Sub m n = Fin m → n ⊢

lifts : ∀{m n} → Sub m n → Sub (suc m) (suc n)
lifts ρ zero = ` zero
lifts ρ (suc x) = ren suc (ρ x)

sub     : ∀{m n} → Sub m n → m ⊢ → n ⊢
subList : ∀{m n} → Sub m n → List (m ⊢) → List (n ⊢)

sub σ (` x)          = σ x
sub σ (ƛ t)          = ƛ (sub (lifts σ) t) 
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

lifts-cong : ∀{m n}{σ σ' : Sub m n}
  → (∀ α → σ α ≡ σ' α)
  → (α : Fin (suc m))
  → lifts σ α ≡ lifts σ' α
lifts-cong p zero    = refl
lifts-cong p (suc α) = cong (ren suc) (p α) 

sub-cong : ∀{m n}{σ σ' : Sub m n}
  → (∀ α → σ α ≡ σ' α)
  → (t : m ⊢)
  → sub σ t ≡ sub σ' t

subList-cong : ∀{m n}{σ σ' : Sub m n}
  → (∀ α → σ α ≡ σ' α)
  → (ts : List (m ⊢))
  → subList σ ts ≡ subList σ' ts
subList-cong p []       = refl
subList-cong p (t ∷ ts) = cong₂ _∷_ (sub-cong p t) (subList-cong p ts)

sub-cong p (` x)           = p x
sub-cong p (ƛ t)           = cong ƛ (sub-cong (lifts-cong p) t)
sub-cong p (t · u)         = cong₂ _·_ (sub-cong p t) (sub-cong p u)
sub-cong p (con c)         = refl
sub-cong p (builtin bn ts) = cong (builtin bn) (subList-cong p ts)
sub-cong p error           = refl

lifts-id : ∀{n} → (α : Fin (suc n)) → ` α ≡ lifts ` α
lifts-id zero    = refl
lifts-id (suc α) = refl

sub-id : ∀{n} → (t : n ⊢) → t ≡ sub ` t

subList-id : ∀{n} → (ts : List (n ⊢)) → ts ≡ subList ` ts
subList-id []       = refl
subList-id (t ∷ ts) = cong₂ _∷_ (sub-id t) (subList-id ts)

sub-id (` x)           = refl
sub-id (ƛ t)           = cong ƛ (trans (sub-id t) (sub-cong lifts-id t))
sub-id (t · u)         = cong₂ _·_ (sub-id t) (sub-id u)
sub-id (con c)         = refl
sub-id (builtin bn ts) = cong (builtin bn) (subList-id ts)
sub-id error           = refl
\end{code}
