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
G : ∀{Γ} → Γ ,⋆  * ⊢⋆ *
G = Π (` Z ⇒ (` (S Z) ⇒ ` Z) ⇒ ` Z)

M : ∀{Γ} → Γ ⊢⋆ *
M {Γ} = μ0 · ƛ G

N : ∀{Γ} → Γ ⊢⋆ *
N  =  G ⋆.[ M ]

Zero : ∀{Γ} → Γ ⊢ N
Zero = Λ (ƛ (ƛ (` (S (Z )))))

-- succ = λ n : N . Λ R . λ x : R . λ y : M → R . y (in n)
-- : N → N

Succ : ∀{Γ} → Γ ⊢ N ⇒ N
Succ = ƛ (Λ (ƛ (ƛ
  (` Z · (wrap0 (ƛ G) (conv (sym≡β (β≡β _ _)) (` (S (S (T Z))))))))))

--FoldNat : ∀{Γ} → {!!}
--FoldNat = {!!}
\end{code}
