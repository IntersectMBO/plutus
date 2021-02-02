\begin{code}
module Untyped.RenamingSubstitution where
\end{code}

\begin{code}
open import Untyped

open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Function
open import Utils
\end{code}

\begin{code}
Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

lift : ∀{m n} → Ren m n → Ren (suc m) (suc n)
lift ρ zero = zero
lift ρ (suc x) = suc (ρ x)

ren     : ∀{m n} → Ren m n → m ⊢ → n ⊢
ren ρ (` x)       = ` (ρ x)
ren ρ (ƛ t)       = ƛ (ren (lift ρ) t)
ren ρ (t · u)     = ren ρ t · ren ρ u
ren ρ (force t)   = force (ren ρ t)
ren ρ (delay t)   = delay (ren ρ t)
ren ρ (con tcn)   = con tcn
ren ρ (builtin b) = builtin b
ren ρ error       = error

weaken : ∀{n} → n ⊢ → suc n ⊢
weaken t = ren suc t

lift-cong : ∀{m n}{ρ ρ' : Ren m n}
  → (∀ x → ρ x ≡ ρ' x)
  → (x : Fin (suc m))
  → lift ρ x ≡ lift ρ' x
lift-cong p zero    = refl
lift-cong p (suc x) = cong suc (p x)

ren-cong : ∀{m n}{ρ ρ' : Ren m n}
  → (∀ x → ρ x ≡ ρ' x)
  → (t : m ⊢)
  → ren ρ t ≡ ren ρ' t
ren-cong p (` x)       = cong ` (p x)
ren-cong p (ƛ t)       = cong ƛ (ren-cong (lift-cong p) t)
ren-cong p (t · u)     = cong₂ _·_ (ren-cong p t) (ren-cong p u)
ren-cong p (force t)   = cong force (ren-cong p t)
ren-cong p (delay t)   = cong delay (ren-cong p t)
ren-cong p (con c)     = refl
ren-cong p (builtin b) = refl
ren-cong p error       = refl

lift-id : ∀{n} → (x : Fin (suc n)) → id x ≡ lift id x
lift-id zero    = refl
lift-id (suc x) = refl

lift-comp : ∀{m n o}(g : Ren m n)(f : Ren n o)(x : Fin (suc m))
  → lift (f ∘ g) x ≡ lift f (lift g x)
lift-comp g f zero    = refl
lift-comp g f (suc x) = refl


ren-id : ∀{n} → (t : n ⊢) → t ≡ ren id t
ren-id (` x)       = refl
ren-id (ƛ t)       = cong ƛ (trans (ren-id t) (ren-cong lift-id t)) 
ren-id (t · u)     = cong₂ _·_ (ren-id t) (ren-id u)
ren-id (force t)   = cong force (ren-id t)
ren-id (delay t)   = cong delay (ren-id t) 
ren-id (con c)     = refl
ren-id (builtin b) = refl
ren-id error       = refl

ren-comp : ∀{m n o}(g : Ren m n)(f : Ren n o)(t : m ⊢)
  → ren (f ∘ g) t ≡ ren f (ren g t)
ren-comp ρ ρ' (` x)            = refl
ren-comp ρ ρ' (ƛ t)            = cong ƛ (trans
  (ren-cong (lift-comp ρ ρ') t)
  (ren-comp (lift ρ) (lift ρ') t))
ren-comp ρ ρ' (t · u)     = cong₂ _·_ (ren-comp ρ ρ' t) (ren-comp ρ ρ' u)
ren-comp ρ ρ' (force t)   = cong force (ren-comp ρ ρ' t)
ren-comp ρ ρ' (delay t)   = cong delay (ren-comp ρ ρ' t)
ren-comp ρ ρ' (con c)     = refl
ren-comp ρ ρ' (builtin b) = refl
ren-comp ρ ρ' error       = refl 

Sub : ℕ → ℕ → Set
Sub m n = Fin m → n ⊢

lifts : ∀{m n} → Sub m n → Sub (suc m) (suc n)
lifts ρ zero = ` zero
lifts ρ (suc x) = ren suc (ρ x)

sub    : ∀{m n} → Sub m n → m ⊢ → n ⊢
sub σ (` x)       = σ x
sub σ (ƛ t)       = ƛ (sub (lifts σ) t) 
sub σ (t · u)     = sub σ t · sub σ u
sub σ (force t)   = force (sub σ t)
sub σ (delay t)   = delay (sub σ t)
sub σ (con tcn)   = con tcn
sub σ (builtin b) = builtin b
sub σ error       = error

extend : ∀{m n} → Sub m n → n ⊢ → Sub (suc m) n
extend σ t zero    = t
extend σ t (suc x) = σ x

_[_] : ∀{n} → suc n ⊢ → n ⊢ → n ⊢
t [ u ] = sub (extend ` u) t

lifts-cong : ∀{m n}{σ σ' : Sub m n}
  → (∀ x → σ x ≡ σ' x)
  → (x : Fin (suc m))
  → lifts σ x ≡ lifts σ' x
lifts-cong p zero    = refl
lifts-cong p (suc x) = cong (ren suc) (p x) 

sub-cong : ∀{m n}{σ σ' : Sub m n}
  → (∀ x → σ x ≡ σ' x)
  → (t : m ⊢)
  → sub σ t ≡ sub σ' t

sub-cong p (` x)       = p x
sub-cong p (ƛ t)       = cong ƛ (sub-cong (lifts-cong p) t)
sub-cong p (t · u)     = cong₂ _·_ (sub-cong p t) (sub-cong p u)
sub-cong p (force t)   = cong force (sub-cong p t)
sub-cong p (delay t)   = cong delay (sub-cong p t)
sub-cong p (con c)     = refl
sub-cong p (builtin b) = refl
sub-cong p error       = refl

lifts-id : ∀{n} → (x : Fin (suc n)) → ` x ≡ lifts ` x
lifts-id zero    = refl
lifts-id (suc x) = refl

sub-id : ∀{n} → (t : n ⊢) → t ≡ sub ` t
sub-id (` x)       = refl
sub-id (ƛ t)       = cong ƛ (trans (sub-id t) (sub-cong lifts-id t))
sub-id (t · u)     = cong₂ _·_ (sub-id t) (sub-id u)
sub-id (force t)   = cong force (sub-id t)
sub-id (delay t)   = cong delay (sub-id t)
sub-id (con c)     = refl
sub-id (builtin b) = refl
sub-id error       = refl

lifts-lift : ∀{m n o}(g : Ren m n)(f : Sub n o)(x : Fin (suc m))
  → lifts (f ∘ g) x ≡ lifts f (lift g x)
lifts-lift g f zero    = refl
lifts-lift g f (suc x) = refl

sub-ren : ∀{m n o}(ρ : Ren m n)(σ : Sub n o)(t : m ⊢)
  → sub (σ ∘ ρ) t ≡ sub σ (ren ρ t)
sub-ren ρ σ (` x)       = refl
sub-ren ρ σ (ƛ t)       = cong ƛ (trans
  (sub-cong (lifts-lift ρ σ) t)
  (sub-ren (lift ρ) (lifts σ) t))
sub-ren ρ σ (t · u)     = cong₂ _·_ (sub-ren ρ σ t) (sub-ren ρ σ u) 
sub-ren ρ σ (force t)   = cong force (sub-ren ρ σ t)
sub-ren ρ σ (delay t)   = cong delay (sub-ren ρ σ t)
sub-ren ρ σ (con c)     = refl
sub-ren ρ σ (builtin b) = refl
sub-ren ρ σ error       = refl

ren-lift-lifts : ∀{m n o}(g : Sub m n)(f : Ren n o)(x : Fin (suc m))
  → lifts (ren f ∘ g) x ≡ ren (lift f) (lifts g x)
ren-lift-lifts g f zero = refl
ren-lift-lifts g f (suc x) = trans
  (sym (ren-comp f suc (g x)))
  (ren-comp suc (lift f) (g x))

ren-sub : ∀{m n o}(σ : Sub m n)(ρ : Ren n o)(t : m ⊢)
  → sub (ren ρ ∘ σ) t ≡ ren ρ (sub σ t)
ren-sub σ ρ (` x)               = refl
ren-sub σ ρ (ƛ t)               = cong ƛ (trans
  (sub-cong (ren-lift-lifts σ ρ) t)
  (ren-sub (lifts σ) (lift ρ) t))
ren-sub σ ρ (t · u)     = cong₂ _·_ (ren-sub σ ρ t) (ren-sub σ ρ u) 
ren-sub σ ρ (force t)   = cong force (ren-sub σ ρ t)
ren-sub σ ρ (delay t)   = cong delay (ren-sub σ ρ t)
ren-sub σ ρ (con c)     = refl
ren-sub σ ρ (builtin b) = refl
ren-sub σ ρ error       = refl

lifts-comp : ∀{m n o}(g : Sub m n)(f : Sub n o)(x : Fin (suc m))
  → lifts (sub f ∘ g) x ≡ sub (lifts f) (lifts g x)
lifts-comp g f zero    = refl
lifts-comp g f (suc x) = trans
  (sym (ren-sub f suc (g x)))
  (sub-ren suc (lifts f) (g x))

-- TODO: add sub-comp
