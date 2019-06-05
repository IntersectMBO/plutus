\begin{code}
module Declarative.StdLib.Nat where
\end{code}

\begin{code}
open import Type
open import Type.Equality
import Type.RenamingSubstitution as ⋆
open import Declarative
open import Declarative.StdLib.Function
\end{code}

\begin{code}
G : ∀{Φ} → Φ ,⋆  * ⊢⋆ *
G = Π "α" (` Z ⇒ (` (S Z) ⇒ ` Z) ⇒ ` Z)

M : ∀{Φ} → Φ ⊢⋆ *
M = μ0 · ƛ "x" G

N : ∀{Φ} → Φ ⊢⋆ *
N  =  G ⋆.[ M ]

Zero : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N
Zero = Λ "α" (ƛ "x" (ƛ "y" (` (S (Z )))))

-- succ = λ n : N . Λ R . λ x : R . λ y : M → R . y (in n)
-- : N → N

Succ : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N ⇒ N
Succ = ƛ "x" (Λ "α" (ƛ "y" (ƛ "z"
  (` Z · (wrap0 (ƛ "x" G) (conv (sym≡β (β≡β _ _)) (` (S (S (T Z))))))))))

--FoldNat : ∀{Φ}{Γ : Ctx Φ} → {!!}
--FoldNat = {!!}
\end{code}
