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
open import Builtin
open import Utils

open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Data.Fin hiding (_+_)
open import Data.List using (List;_∷_;[])
open import Data.Vec using (Vec;_++_)
open import Data.Product using (_,_)
open import Data.Nat
open import Data.Nat.Properties
\end{code}

\begin{code}
lem-≤‴-step : ∀{m n n'}(p : m <‴ n)(q : n ≡ n')
  → ≤‴-step (subst (suc m ≤‴_) q p) ≡ subst (m ≤‴_) q (≤‴-step p)
lem-≤‴-step p refl = refl

erase—→ : ∀{n}{w : Weirdℕ n}{t t' : ScopedTm w}
  → t S.—→ t' → eraseTm t U.—→ eraseTm t' ⊎ eraseTm t ≡ eraseTm t'

eraseVal : ∀{n}{w : Weirdℕ n}{t : ScopedTm w}
  → S.Value t
  → U.Value (eraseTm t)
eraseVal (S.V-ƛ A t)             = U.V-F (U.V-ƛ (eraseTm t))
eraseVal (S.V-Λ t)               = U.V-F (U.V-ƛ (U.weaken (eraseTm t)))
eraseVal (S.V-con tcn)           = U.V-con (eraseTC tcn)
eraseVal (S.V-wrap A B V)        = eraseVal V
eraseVal {w = w} (S.V-builtin b As p ts) = U.V-F (subst (λ p → U.FValue (builtin b p (eraseTel⋆ w As ++ eraseTel ts))) {!lem!} (U.V-builtin b (eraseTel⋆ w As ++ eraseTel ts) ((subst (suc (arity⋆ b) + _ ≤‴_) (lemma b) (subst (_≤‴ arity⋆ b + Scoped.arity b) (+-suc (arity⋆ b) _) (+-monoʳ-≤‴ (arity⋆ b) p))) )))
{- U.V-F (subst
  (λ p → U.FValue (builtin b p (eraseTel ts)))
  (lem-≤‴-step p (lemma b))
  (U.V-builtin b (eraseTel ts) (subst (_ ≤‴_) (lemma b) p))) 
-}
-- eraseVal (S.V-builtin⋆ b p As) = U.V-F {!U.V-builtin b []!}
{-
eraseVTel : ∀{n}{w : Weirdℕ n}(tel : S.Tel w) → S.VTel w tel
  → U.VTel (len w) (eraseTel tel)
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
erase—→ S.E-·₁ = inj₁ U.E-·₁
erase—→ (S.β-wrap p) = inj₂ refl
erase—→ (S.E-·₂ v) = inj₁ (U.E-·₂ (eraseVal v))
erase—→ S.E-·⋆ = inj₁ U.E-·₁
erase—→ S.E-unwrap = inj₂ refl
erase—→ S.E-wrap = inj₂ refl
erase—→ (S.E-builtin b As ts vtelA (error A) (S.E-error A) telB) = inj₁ (U.E-builtin b _ (eraseVTel _ vtelA) U.E-error (eraseList telB))

-- these are type errors that cease to be so...
erase—→ S.E-Λ· = inj₁ U.E-runtime
erase—→ S.E-ƛ·⋆ = inj₁ U.E-runtime
erase—→ S.E-con· = inj₁ U.E-con
erase—→ S.E-con·⋆ = inj₁ U.E-con
erase—→ S.E-wrap· = inj₁ U.E-runtime
erase—→ S.E-wrap·⋆ = inj₁ U.E-runtime
erase—→ S.E-ƛunwrap = inj₁ U.E-runtime
erase—→ S.E-Λunwrap = inj₁ U.E-runtime
erase—→ S.E-conunwrap = inj₁ U.E-runtime
erase—→ (S.E-builtin·⋆ _ _ _ _) = inj₁ U.E-runtime
erase—→ S.E-builtinunwrap = inj₁ U.E-runtime
-}
\end{code}
