\begin{code}
module Scoped.RenamingSubstitution where
\end{code}

\begin{code}
open import Scoped
\end{code}

\begin{code}
postulate _[_] : ∀{n} → ScopedTm (S n) → ScopedTm n → ScopedTm n
postulate _[_]⋆ : ∀{n} → ScopedTm (T n) → ScopedTy ∥ n ∥ → ScopedTm n
\end{code}
