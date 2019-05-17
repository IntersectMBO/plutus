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
true = Λ "α" (ƛ "t" (ƛ "f" (` (S Z))))

false : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ boolean
false = Λ "α" (ƛ "t" (ƛ "f" (` Z)))

if : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ Π "α" (boolean ⇒ ` Z ⇒ ` Z ⇒  ` Z)
if = Λ "α" (ƛ "x" (ƛ "y" (ƛ "z" (` (S (S Z)) ·⋆ ` Z · ` (S Z) · ` Z))))
\end{code}

