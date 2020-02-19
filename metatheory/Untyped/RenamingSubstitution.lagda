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
  → (∀ x → ρ x ≡ ρ' x)
  → (x : Fin (suc m))
  → lift ρ x ≡ lift ρ' x
lift-cong p zero    = refl
lift-cong p (suc x) = cong suc (p x)

ren-cong : ∀{m n}{ρ ρ' : Ren m n}
  → (∀ x → ρ x ≡ ρ' x)
  → (t : m ⊢)
  → ren ρ t ≡ ren ρ' t

renList-cong : ∀{m n}{ρ ρ' : Ren m n}
  → (∀ x → ρ x ≡ ρ' x)
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


lift-id : ∀{n} → (x : Fin (suc n)) → id x ≡ lift id x
lift-id zero    = refl
lift-id (suc x) = refl

lift-comp : ∀{m n o}(g : Ren m n)(f : Ren n o)(x : Fin (suc m))
  → lift (f ∘ g) x ≡ lift f (lift g x)
lift-comp g f zero    = refl
lift-comp g f (suc x) = refl

ren-id : ∀{n} → (t : n ⊢) → t ≡ ren id t
renList-id : ∀{n} → (ts : List (n ⊢)) → ts ≡ renList id ts

renList-id []       = refl
renList-id (t ∷ ts) = cong₂ _∷_ (ren-id t) (renList-id ts)

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

ren-comp : ∀{m n o}(g : Ren m n)(f : Ren n o)(t : m ⊢)
  → ren (f ∘ g) t ≡ ren f (ren g t)

renList-comp : ∀{m n o}(g : Ren m n)(f : Ren n o)(ts : List (m ⊢))
  → renList (f ∘ g) ts ≡ renList f (renList g ts)

renList-comp g f []       = refl
renList-comp g f (t ∷ ts) = cong₂ _∷_ (ren-comp g f t) (renList-comp g f ts)

ren-comp g f (` x) = refl
ren-comp g f (ƛ t) = cong ƛ (trans
  (ren-cong (lift-comp g f) t)
  (ren-comp (lift g) (lift f) t))
ren-comp g f (t · u) = cong₂ _·_ (ren-comp g f t) (ren-comp g f u)
ren-comp g f (con c) = refl
ren-comp g f (builtin b tel) = cong (builtin b) (renList-comp g f tel)
ren-comp g f error = refl 

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
  → (∀ x → σ x ≡ σ' x)
  → (x : Fin (suc m))
  → lifts σ x ≡ lifts σ' x
lifts-cong p zero    = refl
lifts-cong p (suc x) = cong (ren suc) (p x) 

sub-cong : ∀{m n}{σ σ' : Sub m n}
  → (∀ x → σ x ≡ σ' x)
  → (t : m ⊢)
  → sub σ t ≡ sub σ' t

subList-cong : ∀{m n}{σ σ' : Sub m n}
  → (∀ x → σ x ≡ σ' x)
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

lifts-id : ∀{n} → (x : Fin (suc n)) → ` x ≡ lifts ` x
lifts-id zero    = refl
lifts-id (suc x) = refl

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

lifts-lift : ∀{m n o}(g : Ren m n)(f : Sub n o)(x : Fin (suc m))
  → lifts (f ∘ g) x ≡ lifts f (lift g x)
lifts-lift g f zero    = refl
lifts-lift g f (suc x) = refl

sub-ren : ∀{m n o}(g : Ren m n)(f : Sub n o)(t : m ⊢)
  → sub (f ∘ g) t ≡ sub f (ren g t)
subList-renList : ∀{m n o}(g : Ren m n)(f : Sub n o)(ts : List (m ⊢))
  → subList (f ∘ g) ts ≡ subList f (renList g ts)
subList-renList g f []       = refl
subList-renList g f (t ∷ ts) =
  cong₂ _∷_ (sub-ren g f t) (subList-renList g f ts)

sub-ren g f (` x)           = refl
sub-ren g f (ƛ t)           = cong ƛ (trans
  (sub-cong (lifts-lift g f) t)
  (sub-ren (lift g) (lifts f) t))
sub-ren g f (t · u)         = cong₂ _·_ (sub-ren g f t) (sub-ren g f u) 
sub-ren g f (con c)         = refl
sub-ren g f (builtin b tel) = cong (builtin b) (subList-renList g f tel)
sub-ren g f error           = refl

ren-lift-lifts : ∀{m n o}(g : Sub m n)(f : Ren n o)(x : Fin (suc m))
  → lifts (ren f ∘ g) x ≡ ren (lift f) (lifts g x)
ren-lift-lifts g f zero = refl
ren-lift-lifts g f (suc x) = trans
  (sym (ren-comp f suc (g x)))
  (ren-comp suc (lift f) (g x))

ren-sub : ∀{m n o}(g : Sub m n)(f : Ren n o)(t : m ⊢)
  → sub (ren f ∘ g) t ≡ ren f (sub g t)
renList-subList : ∀{m n o}(g : Sub m n)(f : Ren n o)(ts : List (m ⊢))
  → subList (ren f ∘ g) ts ≡ renList f (subList g ts)

ren-sub g f (` x)           = refl
ren-sub g f (ƛ t)           = cong ƛ (trans
  (sub-cong (ren-lift-lifts g f) t)
  (ren-sub (lifts g) (lift f) t))
ren-sub g f (t · u)         = cong₂ _·_ (ren-sub g f t) (ren-sub g f u) 
ren-sub g f (con c)         = refl
ren-sub g f (builtin b tel) = cong (builtin b) (renList-subList g f tel)
ren-sub g f error           = refl

renList-subList g f []       = refl
renList-subList g f (t ∷ ts) =
  cong₂ _∷_ (ren-sub g f t) (renList-subList g f ts)

lifts-comp : ∀{m n o}(g : Sub m n)(f : Sub n o)(x : Fin (suc m))
  → lifts (sub f ∘ g) x ≡ sub (lifts f) (lifts g x)
lifts-comp g f zero    = refl
lifts-comp g f (suc x) = trans
  (sym (ren-sub f suc (g x)))
  (sub-ren suc (lifts f) (g x))
\end{code}
