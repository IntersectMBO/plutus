\begin{code}
module Declarative.StdLib.Unit where
\end{code}

\begin{code}
open import Type
open import Declarative.Term
\end{code}

# Term Abbreviations
\begin{code}
void : ∀{Γ} → Γ ⊢ unit
void = Λ (ƛ (` Z))
\end{code}
