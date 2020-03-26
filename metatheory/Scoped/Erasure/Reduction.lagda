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
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Data.Fin
open import Data.List using (List;_++_;[_];_∷_;[])
open import Data.Product using (_,_)
open import Builtin
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
eraseVal (S.V-builtin b As ts) = U.V-builtin b (eraseList ts)

eraseVTel : ∀{n}{w : Weirdℕ n}(tel : S.Tel w) → S.VTel w tel
  → U.VTel (len w) (eraseList tel)
eraseVTel []        _          = _
eraseVTel (t ∷ tel) (v , vtel) = eraseVal v , eraseVTel tel vtel

erase++ : ∀{n}{w : Weirdℕ n}(ts : List (ScopedTm w))(ts' : List (ScopedTm w))
  → eraseList ts ++ eraseList ts' ≡ eraseList (ts ++ ts')
erase++ []       ts' = refl
erase++ (t ∷ ts) ts' = cong (eraseTm t ∷_) (erase++ ts ts') 

postulate
 eraseBUILTIN : ∀ b {n}(As : List (ScopedTy n)){w}(ts : List (ScopedTm w)) vs →
  U.BUILTIN b (eraseList ts) (eraseVTel ts vs) ≡ eraseTm (S.BUILTIN b As ts vs)

erase—→ (S.ξ-·₁ {M = u} p) = map U.ξ-·₁ (cong (_· eraseTm u)) (erase—→ p)
erase—→ (S.ξ-·₂ {L = t} p q) =
  map (U.ξ-·₂ (eraseVal p)) (cong (eraseTm t ·_)) (erase—→ q)
erase—→ (S.ξ-·⋆ p) = map U.ξ-·₁ (cong (_· plc_dummy)) (erase—→ p)
erase—→ (S.β-ƛ {L = t}{M = u} v) = inj₁ (subst
  ((ƛ (eraseTm t) · eraseTm u) U.—→_)
  (trans
    (U.sub-cong (sym ∘ erase-extend u) (eraseTm t))
    (sub-erase ` (S.ext ` u) t))
  (U.β-ƛ (eraseVal v)))
erase—→ {w = w} (S.β-Λ {L = t}{A = A}) = inj₁ (subst
  ((ƛ (U.weaken (eraseTm t)) · plc_dummy) U.—→_)
  (trans (sym (U.sub-ren suc (U.extend ` plc_dummy) (eraseTm t)))
         (trans (sym (U.sub-id (eraseTm t))) (sym (lem[]⋆ t A))) )
  (U.β-ƛ (eraseVal (S.voidVal w))))
erase—→ (S.ξ-builtin {b = b}{tel = tel}{telA = telA} vs p telB p') with erase—→ p
... | inj₁ q = inj₁ (subst (builtin b (eraseList tel) U.—→_) (cong (builtin b) (erase++ telA (_ ∷ telB))) (U.ξ-builtin b (eraseList tel) (eraseVTel telA vs) q (eraseList telB) (trans (cong eraseList p') (sym (erase++ telA (_ ∷ telB))))))
... | inj₂ q = inj₂ (cong (builtin b) (trans (cong eraseList p') (trans (sym (erase++ telA (_ ∷ telB))) (trans (cong (λ t → eraseList telA ++ t ∷ eraseList telB) q) (erase++ telA (_ ∷ telB))))))
erase—→ (S.β-builtin {b = b}{As = As}{ts = ts} vs) = inj₁ (subst
  (builtin b (eraseList ts) U.—→_)
  (eraseBUILTIN b As ts vs)
  (U.β-builtin (eraseList ts) (eraseVTel ts vs)))
erase—→ (S.sat-builtin {b = b}{ts = ts}{t = t}) = inj₁ (subst (builtin b (eraseList ts) · eraseTm t U.—→_) (cong (builtin b) (erase++ ts [ t ])) U.sat-builtin)
erase—→ (S.ξ-unwrap p) = erase—→ p
erase—→ (S.ξ-wrap p) = erase—→ p
erase—→ (S.β-wrap p) = inj₂ refl
\end{code}
