\begin{code}
module Scoped.RenamingSubstitution where
\end{code}

\begin{code}
open import Scoped

open import Data.Nat
open import Data.Fin hiding (lift)
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

Ren : (m n : Weirdℕ) → Set
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

postulate _[_] : ∀{n} → ScopedTm (S n) → ScopedTm n → ScopedTm n
postulate _[_]⋆ : ∀{n} → ScopedTm (T n) → ScopedTy ∥ n ∥ → ScopedTm n
\end{code}
