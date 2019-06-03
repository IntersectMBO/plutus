\begin{code}
module Scoped.Erasure.Reduction where
\end{code}

\begin{code}
open import Scoped
import Scoped.Reduction as S

open import Untyped
open import Scoped.Erasure

import Untyped.Reduction as U
open import Data.Sum
open import Relation.Binary.PropositionalEquality
\end{code}

\begin{code}
erase—→ : ∀{n}{w : Weirdℕ n}{t t' : ScopedTm w}
  → t S.—→ t' → eraseTm t U.—→ eraseTm t' ⊎ eraseTm t ≡ eraseTm t'
erase—→ (S.ξ-·₁ p) = {!!}
erase—→ (S.ξ-·₂ p q) = {!!}
erase—→ (S.ξ-·⋆ p) = erase—→ p
erase—→ S.β-ƛ = inj₁ {!U.β-ƛ!}
erase—→ S.β-Λ = {!!}
erase—→ (S.ξ-builtin vs x telB) = {!!}
erase—→ (S.β-builtin vs) = {!!}
erase—→ S.sat-builtin = {!!}
erase—→ (S.ξ-unwrap p) = erase—→ p
erase—→ S.β-wrap = inj₂ refl
\end{code}
