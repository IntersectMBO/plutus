\begin{code}
module Scoped.Erasure.Reduction where
\end{code}

\begin{code}
open import Scoped
import Scoped.Reduction as S
import Scoped.RenamingSubstitution as S

open import Untyped
open import Scoped.Erasure
open import Scoped.Erasure.RenamingSubstitution

import Untyped.Reduction as U
import Untyped.RenamingSubstitution as U
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function
\end{code}

\begin{code}
erase—→ : ∀{n}{w : Weirdℕ n}{t t' : ScopedTm w}
  → t S.—→ t' → eraseTm t U.—→ eraseTm t' ⊎ eraseTm t ≡ eraseTm t'
erase—→ (S.ξ-·₁ p) = {!!}
erase—→ (S.ξ-·₂ p q) = {!!}
erase—→ (S.ξ-·⋆ p) = erase—→ p
erase—→ (S.β-ƛ {x = x}{L = t}{M = u}) = inj₁ (subst
  ((ƛ x (eraseTm t) · eraseTm u) U.—→_)
  (trans
    (U.sub-cong (sym ∘ erase-extend u) (eraseTm t))
    (sub-erase ` (S.ext ` u) t))
  U.β-ƛ)
erase—→ (S.β-Λ {L = t}{A = A}) = inj₂ (sym (lem[]⋆ t A))
erase—→ (S.ξ-builtin vs x telB) = {!!}
erase—→ (S.β-builtin {b = b} vs) = inj₁ {!!}
erase—→ S.sat-builtin = {!!}
erase—→ (S.ξ-unwrap p) = erase—→ p
erase—→ S.β-wrap = inj₂ refl
\end{code}
