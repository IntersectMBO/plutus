\begin{code}
module Declarative.Examples.StdLib.Nat where
\end{code}

\begin{code}
open import Type
open import Type.Equality
import Type.RenamingSubstitution as ⋆
open import Declarative
open import Declarative.Examples.StdLib.Function
\end{code}

\begin{code}
G : ∀{Φ} → Φ ,⋆  * ⊢⋆ *
G = Π (` Z ⇒ (` (S Z) ⇒ ` Z) ⇒ ` Z)

M : ∀{Φ} → Φ ⊢⋆ *
M = μ0 · ƛ G

N : ∀{Φ} → Φ ⊢⋆ *
N  =  G ⋆.[ M ]

Zero : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N
Zero = Λ (ƛ (ƛ (` (S (Z )))))

-- succ = λ n : N . Λ R . λ x : R . λ y : M → R . y (in n)
-- : N → N

Succ : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N ⇒ N
Succ = ƛ (Λ (ƛ (ƛ 
  (` Z · (wrap0 (ƛ G) (conv (sym≡β (β≡β _ _)) (` (S (S (T Z))))))))))

--FoldNat : ∀{Φ}{Γ : Ctx Φ} → {!!}
--FoldNat = {!!}
\end{code}
