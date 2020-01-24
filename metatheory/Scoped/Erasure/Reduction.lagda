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

eraseVal : ∀{n}{w : Weirdℕ n}{t : ScopedTm w}
  → S.Value t
  → U.Value (eraseTm t)
eraseVal (S.V-ƛ A t)           = U.V-ƛ (eraseTm t)
eraseVal (S.V-Λ t)             = U.V-ƛ (U.weaken (eraseTm t))
eraseVal (S.V-con tcn)         = U.V-con (eraseTC tcn)
eraseVal (S.V-wrap A B V)      = eraseVal V
eraseVal (S.V-builtin b As ts) = {!U.V-builtin!}

erase—→ (S.ξ-·₁ {M = u} p) = map U.ξ-·₁ (cong (_· eraseTm u)) (erase—→ p)
erase—→ (S.ξ-·₂ {L = t} p q) =
  map (U.ξ-·₂ (eraseVal p)) (cong (eraseTm t ·_)) (erase—→ q)
erase—→ (S.ξ-·⋆ p) = erase—→ p
erase—→ (S.β-ƛ {L = t}{M = u}) = inj₁ (subst
  ((ƛ (eraseTm t) · eraseTm u) U.—→_)
  (trans
    (U.sub-cong (sym ∘ erase-extend u) (eraseTm t))
    (sub-erase ` (S.ext ` u) t))
  U.β-ƛ)
erase—→ (S.β-Λ {L = t}{A = A}) = {!!} -- inj₂ (sym (lem[]⋆ t A))
erase—→ (S.ξ-builtin vs x telB) = {!!}
erase—→ (S.β-builtin {b = b} vs) = inj₁ {!!}
erase—→ S.sat-builtin = {!!}
erase—→ (S.ξ-unwrap p) = erase—→ p
erase—→ (S.ξ-wrap p) = erase—→ p
erase—→ S.β-wrap = inj₂ refl
\end{code}
