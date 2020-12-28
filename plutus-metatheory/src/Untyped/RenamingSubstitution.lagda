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
renTel : ∀{l m n} → Ren m n → Tel l m → Tel l n

ren ρ (` x)            = ` (ρ x)
ren ρ (ƛ t)            = ƛ (ren (lift ρ) t)
ren ρ (t · u)          = ren ρ t · ren ρ u
ren ρ (con tcn)        = con tcn
ren ρ (builtin b p ts) = builtin b p (renTel ρ ts)
ren ρ error            = error

renTel ρ []       = []
renTel ρ (t ∷ ts) = ren ρ t ∷ renTel ρ ts

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

renTel-cong : ∀{l m n}{ρ ρ' : Ren m n}
  → (∀ x → ρ x ≡ ρ' x)
  → (ts : Tel l m)
  → renTel ρ ts ≡ renTel ρ' ts
  
renTel-cong p []       = refl
renTel-cong p (t ∷ ts) = cong₂ _∷_ (ren-cong p t) (renTel-cong p ts)

ren-cong p (` x)            = cong ` (p x)
ren-cong p (ƛ t)            = cong ƛ (ren-cong (lift-cong p) t)
ren-cong p (t · u)          = cong₂ _·_ (ren-cong p t) (ren-cong p u)
ren-cong p (con c)          = refl
ren-cong p (builtin b q ts) = cong (builtin b q) (renTel-cong p ts)
ren-cong p error            = refl

lift-id : ∀{n} → (x : Fin (suc n)) → id x ≡ lift id x
lift-id zero    = refl
lift-id (suc x) = refl

lift-comp : ∀{m n o}(g : Ren m n)(f : Ren n o)(x : Fin (suc m))
  → lift (f ∘ g) x ≡ lift f (lift g x)
lift-comp g f zero    = refl
lift-comp g f (suc x) = refl


ren-id : ∀{n} → (t : n ⊢) → t ≡ ren id t

renTel-id : ∀{l n} → (ts : Tel l n) → ts ≡ renTel id ts

renTel-id []       = refl
renTel-id (t ∷ ts) = cong₂ _∷_ (ren-id t) (renTel-id ts)

ren-id (` x)             = refl
ren-id (ƛ t)             = cong ƛ (trans (ren-id t) (ren-cong lift-id t)) 
ren-id (t · u)           = cong₂ _·_ (ren-id t) (ren-id u)
ren-id (con c)           = refl
ren-id (builtin bn p ts) = cong (builtin bn p) (renTel-id ts)
ren-id error             = refl

ren-comp : ∀{m n o}(g : Ren m n)(f : Ren n o)(t : m ⊢)
  → ren (f ∘ g) t ≡ ren f (ren g t)

renTel-comp : ∀{l m n o}(g : Ren m n)(f : Ren n o)(ts : Tel l m)
  → renTel (f ∘ g) ts ≡ renTel f (renTel g ts)

renTel-comp g f []       = refl
renTel-comp g f (t ∷ ts) = cong₂ _∷_ (ren-comp g f t) (renTel-comp g f ts)

ren-comp ρ ρ' (` x)            = refl
ren-comp ρ ρ' (ƛ t)            = cong ƛ (trans
  (ren-cong (lift-comp ρ ρ') t)
  (ren-comp (lift ρ) (lift ρ') t))
ren-comp ρ ρ' (t · u)          = cong₂ _·_ (ren-comp ρ ρ' t) (ren-comp ρ ρ' u)
ren-comp ρ ρ' (con c)          = refl
ren-comp ρ ρ' (builtin b p ts) = cong (builtin b p) (renTel-comp ρ ρ' ts)
ren-comp ρ ρ' error            = refl 
--

Sub : ℕ → ℕ → Set
Sub m n = Fin m → n ⊢

lifts : ∀{m n} → Sub m n → Sub (suc m) (suc n)
lifts ρ zero = ` zero
lifts ρ (suc x) = ren suc (ρ x)

sub    : ∀{m n} → Sub m n → m ⊢ → n ⊢
subTel : ∀{l m n} → Sub m n → Tel l m → Tel l n

sub σ (` x)            = σ x
sub σ (ƛ t)            = ƛ (sub (lifts σ) t) 
sub σ (t · u)          = sub σ t · sub σ u
sub σ (con tcn)        = con tcn
sub σ (builtin b p ts) = builtin b p (subTel σ ts)
sub σ error            = error

subTel σ []       = []
subTel σ (t ∷ ts) = sub σ t ∷ subTel σ ts

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

subTel-cong : ∀{l m n}{σ σ' : Sub m n}
  → (∀ x → σ x ≡ σ' x)
  → (ts : Tel l m)
  → subTel σ ts ≡ subTel σ' ts

subTel-cong p []       = refl
subTel-cong p (t ∷ ts) = cong₂ _∷_ (sub-cong p t) (subTel-cong p ts)

sub-cong p (` x)                = p x
sub-cong p (ƛ t)                = cong ƛ (sub-cong (lifts-cong p) t)
sub-cong p (t · u)              = cong₂ _·_ (sub-cong p t) (sub-cong p u)
sub-cong p (con c)              = refl
sub-cong p (builtin bn q ts)    = cong (builtin bn q) (subTel-cong p ts)
sub-cong p error                = refl

lifts-id : ∀{n} → (x : Fin (suc n)) → ` x ≡ lifts ` x
lifts-id zero    = refl
lifts-id (suc x) = refl

sub-id : ∀{n} → (t : n ⊢) → t ≡ sub ` t

subTel-id : ∀{l n} → (ts : Tel l n) → ts ≡ subTel ` ts
subTel-id []       = refl
subTel-id (t ∷ ts) = cong₂ _∷_ (sub-id t) (subTel-id ts)

sub-id (` x)            = refl
sub-id (ƛ t)            = cong ƛ (trans (sub-id t) (sub-cong lifts-id t))
sub-id (t · u)          = cong₂ _·_ (sub-id t) (sub-id u)
sub-id (con c)          = refl
sub-id (builtin b p ts) = cong (builtin b p) (subTel-id ts)
sub-id error            = refl

lifts-lift : ∀{m n o}(g : Ren m n)(f : Sub n o)(x : Fin (suc m))
  → lifts (f ∘ g) x ≡ lifts f (lift g x)
lifts-lift g f zero    = refl
lifts-lift g f (suc x) = refl

sub-ren : ∀{m n o}(ρ : Ren m n)(σ : Sub n o)(t : m ⊢)
  → sub (σ ∘ ρ) t ≡ sub σ (ren ρ t)
subTel-renTel : ∀{l m n o}(g : Ren m n)(f : Sub n o)(ts : Tel l m)
  → subTel (f ∘ g) ts ≡ subTel f (renTel g ts)
subTel-renTel g f []       = refl
subTel-renTel g f (t ∷ ts) =
  cong₂ _∷_ (sub-ren g f t) (subTel-renTel g f ts)

sub-ren ρ σ (` x)            = refl
sub-ren ρ σ (ƛ t)            = cong ƛ (trans
  (sub-cong (lifts-lift ρ σ) t)
  (sub-ren (lift ρ) (lifts σ) t))
sub-ren ρ σ (t · u)          = cong₂ _·_ (sub-ren ρ σ t) (sub-ren ρ σ u) 
sub-ren ρ σ (con c)          = refl
sub-ren ρ σ (builtin b p ts) = cong (builtin b p) (subTel-renTel ρ σ ts)
sub-ren ρ σ error            = refl

ren-lift-lifts : ∀{m n o}(g : Sub m n)(f : Ren n o)(x : Fin (suc m))
  → lifts (ren f ∘ g) x ≡ ren (lift f) (lifts g x)
ren-lift-lifts g f zero = refl
ren-lift-lifts g f (suc x) = trans
  (sym (ren-comp f suc (g x)))
  (ren-comp suc (lift f) (g x))

ren-sub : ∀{m n o}(σ : Sub m n)(ρ : Ren n o)(t : m ⊢)
  → sub (ren ρ ∘ σ) t ≡ ren ρ (sub σ t)
renTel-subTel : ∀{l m n o}(g : Sub m n)(f : Ren n o)(ts : Tel l m)
  → subTel (ren f ∘ g) ts ≡ renTel f (subTel g ts)

ren-sub σ ρ (` x)               = refl
ren-sub σ ρ (ƛ t)               = cong ƛ (trans
  (sub-cong (ren-lift-lifts σ ρ) t)
  (ren-sub (lifts σ) (lift ρ) t))
ren-sub σ ρ (t · u)             = cong₂ _·_ (ren-sub σ ρ t) (ren-sub σ ρ u) 
ren-sub σ ρ (con c)             = refl
ren-sub σ ρ (builtin b p ts)    = cong (builtin b p) (renTel-subTel σ ρ ts)
ren-sub σ ρ error               = refl

renTel-subTel g f []       = refl
renTel-subTel g f (t ∷ ts) =
  cong₂ _∷_ (ren-sub g f t) (renTel-subTel g f ts)

lifts-comp : ∀{m n o}(g : Sub m n)(f : Sub n o)(x : Fin (suc m))
  → lifts (sub f ∘ g) x ≡ sub (lifts f) (lifts g x)
lifts-comp g f zero    = refl
lifts-comp g f (suc x) = trans
  (sym (ren-sub f suc (g x)))
  (sub-ren suc (lifts f) (g x))

-- some auxiliary properties
renTel++ : {l l' m n : ℕ}(ρ : Ren m n)
  → (ts : Tel l m)(ts' : Tel l' m)
  → renTel ρ (ts ++ ts') ≡ renTel ρ ts ++ renTel ρ ts'
renTel++ ρ []       ts' = refl
renTel++ ρ (t ∷ ts) ts' = cong (_ ∷_) (renTel++ ρ ts ts')

renTel:< : {l m n : ℕ}(ρ : Ren m n)
  → (ts : Tel l m)(t  : m ⊢)
  → renTel ρ (ts :< t) ≡ renTel ρ ts :< ren ρ t
renTel:< ρ []       t = refl
renTel:< ρ (_ ∷ ts) t = cong (_ ∷_) (renTel:< ρ ts t)

subTel++ : {l l' m n : ℕ}(σ : Sub m n)
  → (ts : Tel l m)(ts' : Tel l' m)
  → subTel σ (ts ++ ts') ≡ subTel σ ts ++ subTel σ ts'
subTel++ σ []       ts' = refl
subTel++ σ (t ∷ ts) ts' = cong (_ ∷_) (subTel++ σ ts ts')

subTel:< : {l m n : ℕ}(σ : Sub m n)
  → (ts : Tel l m)(t  : m ⊢)
  → subTel σ (ts :< t) ≡ subTel σ ts :< sub σ t
subTel:< σ []       t = refl
subTel:< σ (_ ∷ ts) t = cong (_ ∷_) (subTel:< σ ts t)
\end{code}
