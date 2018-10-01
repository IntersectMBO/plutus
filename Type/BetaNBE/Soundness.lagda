\begin{code}
module Type.BetaNBE.Soundness where
\end{code}

\begin{code}
open import Type
open import Type.Equality
open import Type.BetaNormal
open import Type.BetaNBE
\end{code}

\begin{code}
postulate soundness : ∀ {Φ J} → (t : Φ ⊢⋆ J) → embNf (nf t) ≡β t
\end{code}
