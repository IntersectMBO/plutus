\begin{code}
module Algorithmic.Completeness where

open import Type
open import Type.RenamingSubstitution
import Declarative as Syn
import Algorithmic as Norm
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Type.BetaNBE.RenamingSubstitution

open import Relation.Binary.PropositionalEquality renaming (subst to substEq) hiding ([_])
open import Function

nfCtx : ∀ {Φ} → Syn.Ctx Φ → Norm.Ctx Φ
nfCtx Syn.∅ = Norm.∅
nfCtx (Γ Syn.,⋆ K) = nfCtx Γ Norm.,⋆ K
nfCtx (Γ Syn., A) = nfCtx Γ Norm., nf A

conv∋ : ∀ {Φ Γ K}{A : Φ ⊢Nf⋆ K}{A' : Φ ⊢Nf⋆ K}
 → A ≡ A' →
 (Γ Norm.∋ A) → Γ Norm.∋ A'
conv∋ refl α = α


subst⊢ : ∀ {Φ Γ K}{A : Φ ⊢Nf⋆ K}{A' : Φ ⊢Nf⋆ K}
 → A ≡ A' →
 (Γ Norm.⊢ A) → Γ Norm.⊢ A'
subst⊢ refl α = α

nfTyVar : ∀{Φ Γ K}
  → {A : Φ ⊢⋆ K}
  → Γ Syn.∋ A
  → nfCtx Γ Norm.∋ nf A
nfTyVar Syn.Z = Norm.Z
nfTyVar (Syn.S α) =  Norm.S (nfTyVar α)
nfTyVar {Γ = Γ Syn.,⋆ K} (Syn.T {A = A} α) =
  conv∋ (rename-nf S A) (Norm.T (nfTyVar α))

lemΠ : ∀{Γ K }(B : Γ ,⋆ K ⊢⋆ *) →
       nf (Π B) ≡ Π (nf B)
lemΠ B = cong Π (sym (substNf-lemma' B))

open import Type.Equality
open import Type.BetaNBE.Soundness

lemXX : ∀{Φ K}(pat :  Φ ⊢⋆ _)(arg : Φ ⊢⋆ K) →
  nf (pat · (μ1 · pat) · arg) ≡
  nf
  (embNf (nf pat) ·
   (μ1 ·
    embNf (nf pat))
   · embNf (nf arg))
lemXX {Γ} pat arg = completeness
  (·≡β
    (·≡β (soundness pat) (·≡β (refl≡β μ1) (soundness pat)))
    (soundness arg))

open import Type.BetaNBE.Completeness
open import Type.BetaNBE.Soundness
open import Type.BetaNBE.Stability

lem[] : ∀{Γ K}(A : Γ ⊢⋆ K)(B : Γ ,⋆ K ⊢⋆ *) →
  nf B [ nf A ]Nf ≡ nf (B [ A ])
lem[] A B = trans (subst-eval (embNf (nf B)) idCR (embNf ∘ substNf-cons (ne ∘ `) (nf A))) (trans (fund (λ { Z → symCR (fund idCR (soundness A)) ; (S α) → idCR _}) (sym≡β (soundness B))) (sym (subst-eval B idCR (subst-cons ` A)))) 

import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con boolean
  as SSig
import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf
  as NSig
open import Builtin
import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con as STermCon
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as NTermCon


nfTypeTC : ∀{φ}{A : φ ⊢⋆ *} → STermCon.TermCon A → NTermCon.TermCon (nf A)
nfTypeTC (STermCon.integer i)    = NTermCon.integer i
nfTypeTC (STermCon.bytestring b) = NTermCon.bytestring b

open import Data.Product renaming (_,_ to _,,_)
open import Data.List

nfTypeSIG≡₁ : (bn : Builtin) → proj₁ (SSig.SIG bn) ≡ proj₁ (NSig.SIG bn)
nfTypeSIG≡₁ addInteger = refl
nfTypeSIG≡₁ subtractInteger = refl
nfTypeSIG≡₁ multiplyInteger = refl
nfTypeSIG≡₁ divideInteger = refl
nfTypeSIG≡₁ quotientInteger = refl
nfTypeSIG≡₁ remainderInteger = refl
nfTypeSIG≡₁ modInteger = refl
nfTypeSIG≡₁ lessThanInteger = refl
nfTypeSIG≡₁ lessThanEqualsInteger = refl
nfTypeSIG≡₁ greaterThanInteger = refl
nfTypeSIG≡₁ greaterThanEqualsInteger = refl
nfTypeSIG≡₁ equalsInteger = refl
nfTypeSIG≡₁ concatenate = refl
nfTypeSIG≡₁ takeByteString = refl
nfTypeSIG≡₁ dropByteString = refl
nfTypeSIG≡₁ sha2-256 = refl
nfTypeSIG≡₁ sha3-256 = refl
nfTypeSIG≡₁ verifySignature = refl
nfTypeSIG≡₁ equalsByteString = refl

lemσ : ∀{Γ Δ Δ'}
  → (σ : Sub Δ Γ)
  → (C : Δ ⊢⋆ *)
  → (C' : Δ' ⊢Nf⋆ *)
  → (q : Δ' ≡ Δ)
  → nf C ≡ substEq (_⊢Nf⋆ *) q C' →
  substNf
      (λ {J} α →
         nf
          (σ (substEq (_∋⋆ J) q α)))
      C'
      ≡
      nf (subst σ C)
lemσ σ C _ refl refl = trans
-- this should be a lemma in NBE/RenSubst
-- substNf (nf ∘ σ) (nf C) ≡ nf (subst σ C)
    (trans
      (subst-eval (embNf (nf C)) idCR (embNf ∘ nf ∘ σ))
      (fund (λ α → fund idCR (sym≡β (soundness (σ α)))) (sym≡β (soundness C))))
    (sym (subst-eval C idCR σ))

nfTypeSIG≡₂ : (bn : Builtin) →
  nf (proj₂ (proj₂ (SSig.SIG bn))) ≡
  substEq (_⊢Nf⋆ *) (sym (nfTypeSIG≡₁ bn))
  (proj₂ (proj₂ (NSig.SIG bn)))
nfTypeSIG≡₂ addInteger = refl
nfTypeSIG≡₂ subtractInteger = refl
nfTypeSIG≡₂ multiplyInteger = refl
nfTypeSIG≡₂ divideInteger = refl
nfTypeSIG≡₂ quotientInteger = refl
nfTypeSIG≡₂ remainderInteger = refl
nfTypeSIG≡₂ modInteger = refl
nfTypeSIG≡₂ lessThanInteger = refl
nfTypeSIG≡₂ lessThanEqualsInteger = refl
nfTypeSIG≡₂ greaterThanInteger = refl
nfTypeSIG≡₂ greaterThanEqualsInteger = refl
nfTypeSIG≡₂ equalsInteger = refl
nfTypeSIG≡₂ concatenate = refl
nfTypeSIG≡₂ takeByteString = refl
nfTypeSIG≡₂ dropByteString = refl
nfTypeSIG≡₂ sha2-256 = refl
nfTypeSIG≡₂ sha3-256 = refl
nfTypeSIG≡₂ verifySignature = refl
nfTypeSIG≡₂ equalsByteString = refl
open import Builtin.Constant.Type

lemcon : ∀{Γ Γ'}(p : Γ ≡ Γ')(tcn : TyCon)
  → con tcn ≡ substEq (_⊢Nf⋆ *) p (con tcn)
lemcon refl tcn = refl

substTC : ∀{Γ Γ' : Ctx⋆}(p : Γ ≡ Γ')(tcn : TyCon)
  → NTermCon.TermCon {Φ = Γ} (con tcn)
  → NTermCon.TermCon {Φ = Γ'}(con tcn)
substTC refl tcn t = t

nfList : ∀{Δ} → List (Δ ⊢⋆ *) → List (Δ ⊢Nf⋆ *)
nfList []       = []
nfList (A ∷ As) = nf A ∷ nfList As

lemList : (bn : Builtin)
  → substEq (λ Δ → List (Δ ⊢Nf⋆ *)) (sym (nfTypeSIG≡₁ bn))
    (proj₁ (proj₂ (NSig.SIG bn)))
    ≡ nfList (proj₁ (proj₂ (SSig.SIG bn)))
lemList addInteger = refl
lemList subtractInteger = refl
lemList multiplyInteger = refl
lemList divideInteger = refl
lemList quotientInteger = refl
lemList remainderInteger = refl
lemList modInteger = refl
lemList lessThanInteger = refl
lemList lessThanEqualsInteger = refl
lemList greaterThanInteger = refl
lemList greaterThanEqualsInteger = refl
lemList equalsInteger = refl
lemList concatenate = refl
lemList takeByteString = refl
lemList dropByteString = refl
lemList sha2-256 = refl
lemList sha3-256 = refl
lemList verifySignature = refl
lemList equalsByteString = refl

nfType : ∀{Φ Γ K}
  → {A : Φ ⊢⋆ K}
  → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ nf A
  
nfTypeTel : ∀{Φ Γ Δ}(σ : Sub Δ Φ)(As : List (Δ ⊢⋆ *))
  → Syn.Tel Γ Δ σ As
  → Norm.Tel (nfCtx Γ) Δ (nf ∘ σ) (nfList As)

nfTypeTel σ []        _ = _
nfTypeTel {Γ} σ (A ∷ As) (M ,, Ms) = subst⊢
  -- this should be a lemma in NBE/RenSubst
  -- substNf (nf ∘ σ) (nf C) ≡ nf (subst σ C)
  -- also it might go away if we simplify the builtins post size removal
  (sym (trans (trans
      (subst-eval (embNf (nf A)) idCR (embNf ∘ nf ∘ σ))
      (fund (λ α → fund idCR (sym≡β (soundness (σ α)))) (sym≡β (soundness A))))
    (sym (subst-eval A idCR σ))))
  (nfType M)
  ,,
  nfTypeTel σ As Ms


nfTypeTel' : ∀{Φ Γ Δ Δ'}(σ : Sub Δ Φ)(As : List (Δ ⊢⋆ *))
  → (q : Δ' ≡ Δ)
  → (As' : List (Δ' ⊢Nf⋆ *))
  → (substEq (λ Δ → List (Δ ⊢Nf⋆ *)) q As' ≡ nfList As)
  → Syn.Tel Γ Δ σ As
  → Norm.Tel
      (nfCtx Γ)
      Δ'
      (nf ∘ σ ∘ substEq (_∋⋆ _) q)
      As'
nfTypeTel' σ As refl .(nfList As) refl tel = nfTypeTel σ As tel

nfType (Syn.` α) = Norm.` (nfTyVar α)
nfType {Γ} (Syn.ƛ t) = Norm.ƛ (nfType t)
nfType {Γ} (t Syn.· u) = nfType t Norm.· nfType u
nfType {Γ} (Syn.Λ {B = B} t)    = Norm.Λ (subst⊢ (substNf-lemma' B) (nfType t))
nfType {Γ} (Syn._·⋆_ {B = B} t A) =
  subst⊢ (lem[] A B) (subst⊢ (lemΠ B) (nfType t) Norm.·⋆ nf A)
nfType {Γ} (Syn.wrap1 pat arg t) =
  Norm.wrap1 (nf pat) (nf arg) (subst⊢ (lemXX pat arg) (nfType t))
nfType {Γ} (Syn.unwrap1 {pat = pat}{arg} t) =
  subst⊢ (sym (lemXX pat arg)) (Norm.unwrap1 (nfType t))
nfType (Syn.conv p t) rewrite sym (completeness p) = nfType t
nfType {Γ} (Syn.con {tcn = tcn} t) = Norm.con (nfTypeTC t)
nfType {Γ} (Syn.builtin bn σ tel) = let
  Δ ,, As ,, C = SSig.SIG bn
  Δ' ,, As' ,, C' = NSig.SIG bn
  in subst⊢
    (lemσ σ C C' (sym (nfTypeSIG≡₁ bn)) (nfTypeSIG≡₂ bn))
    (Norm.builtin
      bn
      (nf ∘ σ ∘ substEq (_∋⋆ _) (sym (nfTypeSIG≡₁ bn)))
      (nfTypeTel' σ As (sym (nfTypeSIG≡₁ bn)) As' (lemList bn) tel))
nfType {Γ} (Syn.error A) = Norm.error (nf A)

completenessT : ∀{Φ Γ K}{A : Φ ⊢⋆ K} → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ nf A × (A ≡β embNf (nf A))
completenessT {A = A} t = nfType t ,, soundness A
\end{code}
