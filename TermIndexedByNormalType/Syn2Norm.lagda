\begin{code}
module TermIndexedByNormalType.Syn2Norm where

open import Type
open import Type.RenamingSubstitution
import TermIndexedBySyntacticType.Term as Syn
import TermIndexedByNormalType.Term as Norm
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Completeness


open import Relation.Binary.PropositionalEquality renaming (subst to substEq)
open import Function

nfCtx : Syn.Ctx → Norm.Ctx
nfCtx∥ : ∀ Γ → Syn.∥ Γ ∥ ≡ Norm.∥ nfCtx Γ ∥

nfCtx Syn.∅ = Norm.∅
nfCtx (Γ Syn.,⋆ K) = nfCtx Γ Norm.,⋆ K
nfCtx (Γ Syn., A) = nfCtx Γ Norm., substEq (_⊢Nf⋆ _) (nfCtx∥ Γ) (nf A)

nfCtx∥ Syn.∅ = refl
nfCtx∥ (Γ Syn.,⋆ K) = cong (_,⋆ K) (nfCtx∥ Γ)
nfCtx∥ (Γ Syn., A)  = nfCtx∥ Γ

--lem∥ : ∀{Γ Γ'} → Γ ≡ Γ' → Norm.∥ Γ ∥ ≡ Norm.∥ Γ ∥
--lem∥ refl = refl

lemS : ∀{Γ Γ' K J}{A : Γ ⊢Nf⋆ K}{A' : Γ ,⋆ J ⊢Nf⋆ K}
 → (p : Γ ≡ Γ')
 → (q : Γ ,⋆ J ≡ Γ' ,⋆ J)
 → renameNf S A ≡ A'
 → renameNf S (substEq (_⊢Nf⋆ K) p A) ≡ substEq (_⊢Nf⋆ K) q A'
lemS refl refl p = p

subst∋ : ∀ {Γ Γ' K}{A : Norm.∥ Γ ∥ ⊢Nf⋆ K}{A' : Norm.∥ Γ' ∥ ⊢Nf⋆ K}
 → (p : Γ ≡ Γ')
 → substEq (_⊢Nf⋆ K) (cong Norm.∥_∥ p) A ≡ A' →
 (Γ Norm.∋ A) → Γ' Norm.∋ A'
subst∋ refl refl α = α

subst⊢ : ∀ {Γ Γ' K}{A : Norm.∥ Γ ∥ ⊢Nf⋆ K}{A' : Norm.∥ Γ' ∥ ⊢Nf⋆ K}
 → (p : Γ ≡ Γ')
 → substEq (_⊢Nf⋆ K) (cong Norm.∥_∥ p) A ≡ A' →
 (Γ Norm.⊢ A) → Γ' Norm.⊢ A'
subst⊢ refl refl α = α


nfTyVar : ∀{Γ K}
  → {A : Syn.∥ Γ ∥ ⊢⋆ K}
  → Γ Syn.∋ A
  → nfCtx Γ Norm.∋ substEq (_⊢Nf⋆ K) (nfCtx∥ Γ) (nf A)
nfTyVar Syn.Z = Norm.Z
nfTyVar (Syn.S α) =  Norm.S (nfTyVar α)
nfTyVar (Syn.T {Γ}{K}{J}{A} α) = subst∋
  refl
  (lemS
    (nfCtx∥ Γ)
    (cong (_,⋆ J) (nfCtx∥ Γ))
    -- this horrible thing proves: renameNf S (nf A) ≡ nf rename S A)
    (trans
      (rename-reify (idext idCR A) S)
      (reifyCR
        (transCR
          (transCR
            (renameVal-eval A idCR S)
            (idext (renameVal-reflect S ∘ `) A))
          (symCR (rename-eval A idCR S))))) ) 
  (Norm.T (nfTyVar α))

lemƛ : ∀{Γ Γ'}(p : Γ ≡ Γ')(A B : Γ ⊢Nf⋆ *)
   → substEq  (_⊢Nf⋆ *) p A ⇒ substEq  (_⊢Nf⋆ *) p B
     ≡
     substEq  (_⊢Nf⋆ *) p (A ⇒ B) 
lemƛ refl A B = refl

lemΠ : ∀{Γ Γ' K }(p : Γ ≡ Γ')(q : Γ ,⋆ K ≡ Γ' ,⋆ K)(B : Γ ,⋆ K ⊢Nf⋆ *) →
       Π (substEq (_⊢Nf⋆ *) q B) ≡ substEq (_⊢Nf⋆ *) p (Π B)
lemΠ refl refl B = refl

open import Type.BetaNBE.RenamingSubstitution

lemΠnf : ∀{Γ K}(B : Γ ,⋆ K ⊢⋆ *) → Π (nf B) ≡ nf (Π B)
lemΠnf B = cong Π (substNf-lemma' B)

lemμ : ∀{Γ Γ' K}(p : Γ ≡ Γ')(pat : Γ ⊢Nf⋆ _)(arg : Γ ⊢Nf⋆ _) →
      substEq (_⊢Nf⋆ *) p (nf (embNf pat · (μ1 · embNf pat) · embNf arg) ) ≡
      nf
      (embNf (substEq (_⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *) p pat) ·
       (μ1 ·
        embNf (substEq (_⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *) p pat))
       · embNf (substEq (_⊢Nf⋆ K) p arg))
lemμ refl pat arg = refl

{-
need this:
substEq (_⊢Nf⋆ *) (nfCtx∥ Γ) (nf (pat · (μ1 · pat) · arg)) ≡
nf
(embNf (substEq (_⊢Nf⋆ (.K ⇒ *) ⇒ .K ⇒ *) (nfCtx∥ Γ) (nf pat)) ·
 (μ1 ·
  embNf (substEq (_⊢Nf⋆ (.K ⇒ *) ⇒ .K ⇒ *) (nfCtx∥ Γ) (nf pat)))
 · embNf (substEq (_⊢Nf⋆ .K) (nfCtx∥ Γ) (nf arg)))
-}
open import Type.BetaNBE.Stability

lemμ' : ∀{Γ Γ' K}(p : Γ ≡ Γ')(pat : Γ ⊢Nf⋆ _)(arg : Γ ⊢Nf⋆ _) →
  ne ((μ1 · substEq (_⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *) p pat) · substEq (_⊢Nf⋆ K) p arg)
  ≡
  substEq (_⊢Nf⋆ *) p (ne (μ1 · pat · arg))
lemμ' refl pat arg = refl

nfType : ∀{Γ K}
  → {A : Syn.∥ Γ ∥ ⊢⋆ K}
  → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ substEq (_⊢Nf⋆ K) (nfCtx∥ Γ) (nf A)
nfType (Syn.` α) = Norm.` (nfTyVar α)
nfType {Γ} (Syn.ƛ t) =
  subst⊢ refl (lemƛ (nfCtx∥ Γ) _ _) (Norm.ƛ (nfType t))
nfType {Γ} (t Syn.· u) =
  subst⊢ refl (sym (lemƛ (nfCtx∥ Γ) _ _)) (nfType t)  Norm.· nfType u
nfType {Γ} (Syn.Λ {B = B} t)    = subst⊢
  refl
  (trans
    (lemΠ
      (nfCtx∥ Γ)
      (nfCtx∥ (Γ Syn.,⋆ _))
      (nf B))
    (cong (substEq (_⊢Nf⋆ *) (nfCtx∥ Γ)) (lemΠnf B)))
  (Norm.Λ (nfType t))
nfType {Γ} (t Syn.·⋆ A) = subst⊢
  refl
  {!!}
  (subst⊢ refl (sym (lemΠ (nfCtx∥ Γ) (cong (_,⋆ _) (nfCtx∥ Γ)) _)) (nfType t)
  Norm.·⋆
  -- is there another version where this is just nf A?
  substEq (_⊢Nf⋆ _) (nfCtx∥ Γ) (nf A)) 
nfType {Γ} (Syn.wrap1 pat arg t) =
  subst⊢ refl (lemμ' (nfCtx∥ Γ) (nf pat) (nf arg)) (Norm.wrap1 (substEq (_⊢Nf⋆ _) (nfCtx∥ Γ ) (nf pat)) (substEq (_⊢Nf⋆ _) (nfCtx∥ Γ) (nf arg)) (subst⊢ refl {!lemμ (nfCtx∥ Γ) (nf pat) (nf arg)!} (nfType t)))
nfType {Γ} (Syn.unwrap1 {pat = pat}{arg} t) = subst⊢ refl {!lemμ !} (Norm.unwrap1 (subst⊢ refl (sym (lemμ' (nfCtx∥ Γ) (nf pat) (nf arg))) (nfType t))) 
nfType (Syn.conv p t) rewrite sym (completeness p) = nfType t
nfType (Syn.con t) = subst⊢ refl {!!} (Norm.con {!t!})
nfType (Syn.builtin bn σ x) = Norm.builtin {!!} {!!} {!!}
nfType {Γ} (Syn.error A) = Norm.error (substEq  (_⊢Nf⋆ *) (nfCtx∥ Γ) (nf A))
\end{code}

substEq (_⊢Nf⋆ *) (nfCtx∥ Γ) (nf (pat · (μ1 · pat) · arg)) ≡
nf
(embNf (substEq (_⊢Nf⋆ (.K ⇒ *) ⇒ .K ⇒ *) (nfCtx∥ Γ) (nf pat)) ·
 (μ1 ·
  embNf (substEq (_⊢Nf⋆ (.K ⇒ *) ⇒ .K ⇒ *) (nfCtx∥ Γ) (nf pat)))
 · embNf (substEq (_⊢Nf⋆ .K) (nfCtx∥ Γ) (nf arg)))
