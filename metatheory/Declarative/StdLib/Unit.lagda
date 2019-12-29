\begin{code}
module Declarative.StdLib.Unit where
\end{code}

\begin{code}
open import Type
open import Declarative
\end{code}

# Term Abbreviations
\begin{code}
void : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ unit
void = Λ (ƛ (` Z))
\end{code}
