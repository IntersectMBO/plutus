\begin{code}
module Scoped.RenamingSubstitution where
\end{code}

\begin{code}
open import Scoped

open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.List
open import Function
\end{code}

\begin{code}
Ren⋆ : ℕ → ℕ → Set
Ren⋆ m n = Fin m → Fin n

lift⋆ : ∀{m n} → Ren⋆ m n → Ren⋆ (suc m) (suc n)
lift⋆ ρ zero    = zero
lift⋆ ρ (suc α) = suc (ρ α)

ren⋆ : ∀{m n} → Ren⋆ m n → ScopedTy m → ScopedTy n
ren⋆ ρ (` α) = ` (ρ α)
ren⋆ ρ (A ⇒ B) = ren⋆ ρ A ⇒ ren⋆ ρ B
ren⋆ ρ (Π x K A) = Π x K (ren⋆ (lift⋆ ρ) A)
ren⋆ ρ (ƛ x K A) = ƛ x K (ren⋆ (lift⋆ ρ) A)
ren⋆ ρ (A · B) = ren⋆ ρ A · ren⋆ ρ B
ren⋆ ρ (con x) = con x
ren⋆ ρ (size x) = size x
ren⋆ ρ (μ A B) = μ (ren⋆ ρ A) (ren⋆ ρ B)

ren⋆L : ∀{m n} → Ren⋆ m n → List (ScopedTy m) → List (ScopedTy n)
ren⋆L ρ⋆ []       = []
ren⋆L ρ⋆ (A ∷ As) = ren⋆ ρ⋆ A ∷ ren⋆L ρ⋆ As

Ren : Weirdℕ → Weirdℕ → Set
Ren m n = WeirdFin m → WeirdFin n

lift : ∀{m n} → Ren m n → Ren (S m) (S n)
lift ρ Z     = Z
lift ρ (S x) = S (ρ x)

⋆lift : ∀{m n} → Ren m n → Ren (T m) (T n)
⋆lift ρ (T x) = T (ρ x)

ren : ∀{m n} → Ren⋆ ∥ m ∥ ∥ n ∥ → Ren m n → ScopedTm m → ScopedTm n
renL : ∀{m n} → Ren⋆ ∥ m ∥ ∥ n ∥ → Ren m n
      → List (ScopedTm m) → List (ScopedTm n)

ren ρ⋆ ρ (` x) = ` (ρ x)
ren ρ⋆ ρ (Λ x K t) = Λ x K (ren (lift⋆ ρ⋆) (⋆lift ρ) t) 
ren ρ⋆ ρ (t ·⋆ A) = ren ρ⋆ ρ t ·⋆ ren⋆ ρ⋆ A
ren ρ⋆ ρ (ƛ x A t)  = ƛ x (ren⋆ ρ⋆ A) (ren ρ⋆ (lift ρ) t)
ren ρ⋆ ρ (t · u) = ren ρ⋆ ρ t · ren ρ⋆ ρ u
ren ρ⋆ ρ (con x) = con x
ren ρ⋆ ρ (error A) = error (ren⋆ ρ⋆ A)
ren ρ⋆ ρ (builtin b As ts) = builtin b (ren⋆L ρ⋆ As) (renL ρ⋆ ρ ts)
ren ρ⋆ ρ (wrap A B t) = wrap (ren⋆ ρ⋆ A) (ren⋆ ρ⋆ B) (ren ρ⋆ ρ t)
ren ρ⋆ ρ (unwrap t) = unwrap (ren ρ⋆ ρ t)

renL ρ⋆ ρ []       = []
renL ρ⋆ ρ (t ∷ ts) = ren ρ⋆ ρ t ∷ renL ρ⋆ ρ ts

-- substitution

Sub⋆ : ℕ → ℕ → Set
Sub⋆ m n = Fin m → ScopedTy n

slift⋆ : ∀{m n} → Sub⋆ m n → Sub⋆ (suc m) (suc n)
slift⋆ ρ zero    = ` zero
slift⋆ ρ (suc α) = ren⋆ suc (ρ α)

sub⋆ : ∀{m n} → Sub⋆ m n → ScopedTy m → ScopedTy n
sub⋆ σ (` α)   = σ α
sub⋆ σ (A ⇒ B) = sub⋆ σ A ⇒ sub⋆ σ B
sub⋆ σ (Π x K A) = Π x K (sub⋆ (slift⋆ σ) A)
sub⋆ σ (ƛ x K A) = ƛ x K (sub⋆ (slift⋆ σ) A)
sub⋆ σ (A · B) = sub⋆ σ A · sub⋆ σ B
sub⋆ σ (con c) = con c
sub⋆ σ (size n) = size n
sub⋆ σ (μ A B) = μ (sub⋆ σ A) (sub⋆ σ B)

sub⋆L : ∀{m n} → Sub⋆ m n → List (ScopedTy m) → List (ScopedTy n)
sub⋆L σ⋆ []       = []
sub⋆L σ⋆ (A ∷ As) = sub⋆ σ⋆ A ∷ sub⋆L σ⋆ As

Sub : Weirdℕ → Weirdℕ → Set
Sub m n = WeirdFin m → ScopedTm n

slift : ∀{m n} → Sub m n → Sub (S m) (S n)
slift σ Z     = ` Z
slift σ (S x) = ren id S (σ x)

⋆slift : ∀{m n} → Sub m n → Sub (T m) (T n)
⋆slift σ (T x) = ren suc T (σ x)

sub : ∀{m n} → Sub⋆ ∥ m ∥ ∥ n ∥ → Sub m n → ScopedTm m → ScopedTm n
subL : ∀{m n} → Sub⋆ ∥ m ∥ ∥ n ∥ → Sub m n
  → List (ScopedTm m) → List (ScopedTm n)

sub σ⋆ σ (` x) = σ x
sub σ⋆ σ (Λ x K t) = Λ x K (sub (slift⋆ σ⋆) (⋆slift σ) t)
sub σ⋆ σ (t ·⋆ A) = sub σ⋆ σ t ·⋆ sub⋆ σ⋆ A
sub σ⋆ σ (ƛ x A t) = ƛ x (sub⋆ σ⋆ A) (sub σ⋆ (slift σ) t)
sub σ⋆ σ (t · u) = sub σ⋆ σ t · sub σ⋆ σ u
sub σ⋆ σ (con c) = con c
sub σ⋆ σ (error A) = error (sub⋆ σ⋆ A)
sub σ⋆ σ (builtin b As ts) = builtin b (sub⋆L σ⋆ As) (subL σ⋆ σ ts)
sub σ⋆ σ (wrap A B t) = wrap (sub⋆ σ⋆ A) (sub⋆ σ⋆ B) (sub σ⋆ σ t)
sub σ⋆ σ (unwrap t) = unwrap (sub σ⋆ σ t)

subL σ⋆ σ []       = []
subL σ⋆ σ (t ∷ ts) = sub σ⋆ σ t ∷ subL σ⋆ σ ts

ext : ∀{m n} → Sub m n → ScopedTm n → Sub (S m) n
ext σ t Z = t
ext σ t (S x) = σ x

ext⋆ : ∀{m n} → Sub⋆ m n → ScopedTy n → Sub⋆ (suc m) n
ext⋆ σ A zero = A
ext⋆ σ A (suc α) = σ α

_[_] : ∀{n} → ScopedTm (S n) → ScopedTm n → ScopedTm n
t [ u ] = sub ` (ext ` u) t

_[_]⋆ : ∀{n} → ScopedTm (T n) → ScopedTy ∥ n ∥ → ScopedTm n
t [ A ]⋆ = sub (ext⋆ ` A) (λ { (T x) → ` x}) t
\end{code}

# Proofs

\begin{code}
open import Relation.Binary.PropositionalEquality

lift⋆-cong : ∀{m n}{ρ ρ' : Ren⋆ m n}
  → (∀ x → ρ x ≡ ρ' x)
  → ∀ x → lift⋆ ρ x ≡ lift⋆ ρ' x
lift⋆-cong p zero    = refl
lift⋆-cong p (suc x) = cong suc (p x)

ren⋆-cong : ∀{m n}{ρ ρ' : Ren⋆ m n}
  → (∀ x → ρ x ≡ ρ' x)
  → ∀ x → ren⋆ ρ x ≡ ren⋆ ρ' x
ren⋆-cong p (` x) = cong ` (p x)
ren⋆-cong p (A ⇒ B) = cong₂ _⇒_ (ren⋆-cong p A) (ren⋆-cong p B)
ren⋆-cong p (Π x K A) = cong (Π x K) (ren⋆-cong (lift⋆-cong p) A)
ren⋆-cong p (ƛ x K A) = cong (ƛ x K) (ren⋆-cong (lift⋆-cong p) A)
ren⋆-cong p (A · B) = cong₂ _·_ (ren⋆-cong p A) (ren⋆-cong p B)
ren⋆-cong p (con c) = refl
ren⋆-cong p (size s) = refl
ren⋆-cong p (μ pat arg) = cong₂ μ (ren⋆-cong p pat) (ren⋆-cong p arg)
\end{code}
