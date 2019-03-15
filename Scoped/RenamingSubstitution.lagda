\begin{code}
module Scoped.RenamingSubstitution where
\end{code}

\begin{code}
open import Scoped

open import Data.Nat
open import Data.Fin hiding (lift)
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
ren⋆ ρ (Π K A) = Π K (ren⋆ (lift⋆ ρ) A)
ren⋆ ρ (ƛ K A) = ƛ K (ren⋆ (lift⋆ ρ) A)
ren⋆ ρ (A · B) = ren⋆ ρ A · ren⋆ ρ B
ren⋆ ρ (con x) = con x
ren⋆ ρ (size x) = size x

Ren : Weirdℕ → Weirdℕ → Set
Ren m n = WeirdFin m → WeirdFin n

lift : ∀{m n} → Ren m n → Ren (S m) (S n)
lift ρ Z     = Z
lift ρ (S x) = S (ρ x)

⋆lift : ∀{m n} → Ren m n → Ren (T m) (T n)
⋆lift ρ (T x) = T (ρ x)

ren : ∀{m n} → Ren⋆ ∥ m ∥ ∥ n ∥ → Ren m n → ScopedTm m → ScopedTm n
ren ρ⋆ ρ (` x) = ` (ρ x)
ren ρ⋆ ρ (Λ K t) = Λ K (ren (lift⋆ ρ⋆) (⋆lift ρ) t) 
ren ρ⋆ ρ (t ·⋆ A) = ren ρ⋆ ρ t ·⋆ ren⋆ ρ⋆ A
ren ρ⋆ ρ (ƛ A t)  = ƛ (ren⋆ ρ⋆ A) (ren ρ⋆ (lift ρ) t)
ren ρ⋆ ρ (t · u) = ren ρ⋆ ρ t · ren ρ⋆ ρ u
ren ρ⋆ ρ (con x) = con x
ren ρ⋆ ρ (error A) = error (ren⋆ ρ⋆ A)
ren ρ⋆ ρ (builtin x) = builtin x

-- substitution

Sub⋆ : ℕ → ℕ → Set
Sub⋆ m n = Fin m → ScopedTy n

slift⋆ : ∀{m n} → Sub⋆ m n → Sub⋆ (suc m) (suc n)
slift⋆ ρ zero    = ` zero
slift⋆ ρ (suc α) = ren⋆ suc (ρ α)

sub⋆ : ∀{m n} → Sub⋆ m n → ScopedTy m → ScopedTy n
sub⋆ σ (` α)   = σ α
sub⋆ σ (A ⇒ B) = sub⋆ σ A ⇒ sub⋆ σ B
sub⋆ σ (Π K A) = Π K (sub⋆ (slift⋆ σ) A)
sub⋆ σ (ƛ K A) = ƛ K (sub⋆ (slift⋆ σ) A)
sub⋆ σ (A · B) = sub⋆ σ A · sub⋆ σ B
sub⋆ σ (con c) = con c
sub⋆ σ (size n) = size n

Sub : Weirdℕ → Weirdℕ → Set
Sub m n = WeirdFin m → ScopedTm n

slift : ∀{m n} → Sub m n → Sub (S m) (S n)
slift σ Z     = ` Z
slift σ (S x) = ren id S (σ x)

⋆slift : ∀{m n} → Sub m n → Sub (T m) (T n)
⋆slift σ (T x) = ren suc T (σ x)

sub : ∀{m n} → Sub⋆ ∥ m ∥ ∥ n ∥ → Sub m n → ScopedTm m → ScopedTm n
sub σ⋆ σ (` x) = σ x
sub σ⋆ σ (Λ K t) = Λ K (sub (slift⋆ σ⋆) (⋆slift σ) t)
sub σ⋆ σ (t ·⋆ A) = sub σ⋆ σ t ·⋆ sub⋆ σ⋆ A
sub σ⋆ σ (ƛ A t) = ƛ (sub⋆ σ⋆ A) (sub σ⋆ (slift σ) t)
sub σ⋆ σ (t · u) = sub σ⋆ σ t · sub σ⋆ σ u
sub σ⋆ σ (con c) = con c
sub σ⋆ σ (error A) = error (sub⋆ σ⋆ A)
sub σ⋆ σ (builtin b) = builtin b

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
