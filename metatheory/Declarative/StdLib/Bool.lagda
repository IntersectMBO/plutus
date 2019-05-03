\begin{code}
module Declarative.StdLib.Bool where
\end{code}

\begin{code}
open import Type
open import Declarative
\end{code}

# Term Abbreviations
\begin{code}
true : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ boolean
true = Λ (ƛ (ƛ (` (S Z))))

false : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ boolean
false = Λ (ƛ (ƛ (` Z)))

if : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ Π (boolean ⇒ ` Z ⇒ ` Z ⇒  ` Z)
if = Λ (ƛ (ƛ (ƛ (` (S (S Z)) ·⋆ ` Z · ` (S Z) · ` Z))))
\end{code}

