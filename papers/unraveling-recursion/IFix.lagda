\begin{code}[hide]
module IFix where
open import Common
\end{code}
\begin{code}
{-# NO_POSITIVITY_CHECK #-}
data IFix {A : ∗} (B : (A → ∗) → A → ∗) (x : A) : ∗ where
  wrap : B (IFix B) x → IFix B x

unwrap : ∀ {A B} → {x : A} → IFix B x → B (IFix B) x
unwrap (wrap s) = s
\end{code}
