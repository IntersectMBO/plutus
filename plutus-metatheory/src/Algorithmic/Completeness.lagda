\begin{code}
module Algorithmic.Completeness where

open import Type
open import Type.Equality
open import Type.RenamingSubstitution
import Declarative as Syn
import Algorithmic as Norm
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Type.BetaNBE.RenamingSubstitution

open import Relation.Binary.PropositionalEquality renaming (subst to substEq) hiding ([_])
open import Function
open import Data.Vec hiding ([_];length)
open import Data.Sum

nfCtx : ∀ {Φ} → Syn.Ctx Φ → Norm.Ctx Φ
nfCtx Syn.∅ = Norm.∅
nfCtx (Γ Syn.,⋆ K) = nfCtx Γ Norm.,⋆ K
nfCtx (Γ Syn., A) = nfCtx Γ Norm., nf A

nfTyVar : ∀{Φ Γ}
  → {A : Φ ⊢⋆ *}
  → Γ Syn.∋ A
  → nfCtx Γ Norm.∋ nf A
nfTyVar Syn.Z             = Norm.Z
nfTyVar (Syn.S α)         = Norm.S (nfTyVar α)
nfTyVar (Syn.T {A = A} α) = Norm.conv∋ refl (ren-nf S A) (Norm.T (nfTyVar α)) 

open import Type.BetaNormal.Equality

lemΠ : ∀{Γ K }(B : Γ ,⋆ K ⊢⋆ *) →
       nf (Π B) ≡ Π (nf B)
lemΠ B = cong Π (sym (substNf-lemma' B))

open import Type.BetaNBE.Soundness

stability-μ : ∀{Φ K}(A :  Φ ⊢⋆ _)(B : Φ ⊢⋆ K) →
  nf (A · ƛ (μ (weaken A) (` Z)) · B)
  ≡
  nf (embNf (nf A) · ƛ (μ (embNf (weakenNf (nf A))) (` Z)) · embNf (nf B))
stability-μ A B = completeness
  (·≡β
    (·≡β
      (soundness A)
      (ƛ≡β (μ≡β (trans≡β
        (soundness (ren S A))
        (≡2β (sym (cong embNf (ren-nf S A))))) (refl≡β (` Z)))))
    (soundness B))

open import Type.BetaNBE.Completeness
open import Type.BetaNBE.Soundness
open import Type.BetaNBE.Stability


lem[] : ∀{Γ K}(A : Γ ⊢⋆ K)(B : Γ ,⋆ K ⊢⋆ *) →
  (nf B [ nf A ]Nf) ≡ nf (B [ A ])
lem[] A B = trans
  (subst-eval (embNf (nf B)) idCR (embNf ∘ substNf-cons (ne ∘ `) (nf A)))
  (trans
    (fund
      (λ {Z → symCR (fund idCR (soundness A)) ; (S α) → idCR _})
      (sym≡β (soundness B)))
    (sym (subst-eval B idCR (subst-cons ` A))))

import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con
  as SSig
import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
  as NSig
open import Builtin
import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con as STermCon
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as NTermCon


nfTypeTC : ∀{φ}{A : φ ⊢⋆ *} → STermCon.TermCon A → NTermCon.TermCon (nf A)
nfTypeTC (STermCon.integer i)    = NTermCon.integer i
nfTypeTC (STermCon.bytestring b) = NTermCon.bytestring b
nfTypeTC (STermCon.string s)     = NTermCon.string s
nfTypeTC (STermCon.bool b)       = NTermCon.bool b
nfTypeTC (STermCon.char c)       = NTermCon.char c
nfTypeTC STermCon.unit           = NTermCon.unit

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
nfTypeSIG≡₁ ifThenElse = refl

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
lemσ σ C _ refl q = trans
  (substNf-cong' (nf ∘ σ) (sym q))
  (trans
    (trans
      (subst-eval (embNf (nf C)) idCR (embNf ∘ nf ∘ σ))
      (fund (λ α → fund idCR (sym≡β (soundness (σ α)))) (sym≡β (soundness C))))
    (sym (subst-eval C idCR σ)))
    
-- this should be a lemma in NBE/RenSubst
-- substNf (nf ∘ σ) (nf C) ≡ nf (subst σ C)

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
nfTypeSIG≡₂ ifThenElse = refl

nfTypeSIG≡₃ : (bn : Builtin) → length (proj₁ (proj₂ (SSig.SIG bn))) ≡ length (proj₁ (proj₂ (NSig.SIG bn)))
nfTypeSIG≡₃ addInteger = refl
nfTypeSIG≡₃ subtractInteger = refl
nfTypeSIG≡₃ multiplyInteger = refl
nfTypeSIG≡₃ divideInteger = refl
nfTypeSIG≡₃ quotientInteger = refl
nfTypeSIG≡₃ remainderInteger = refl
nfTypeSIG≡₃ modInteger = refl
nfTypeSIG≡₃ lessThanInteger = refl
nfTypeSIG≡₃ lessThanEqualsInteger = refl
nfTypeSIG≡₃ greaterThanInteger = refl
nfTypeSIG≡₃ greaterThanEqualsInteger = refl
nfTypeSIG≡₃ equalsInteger = refl
nfTypeSIG≡₃ concatenate = refl
nfTypeSIG≡₃ takeByteString = refl
nfTypeSIG≡₃ dropByteString = refl
nfTypeSIG≡₃ sha2-256 = refl
nfTypeSIG≡₃ sha3-256 = refl
nfTypeSIG≡₃ verifySignature = refl
nfTypeSIG≡₃ equalsByteString = refl
nfTypeSIG≡₃ ifThenElse = refl

open import Builtin.Constant.Type

lemcon : ∀{Φ Φ'}(p : Φ ≡ Φ')(tcn : TyCon)
  → con tcn ≡ substEq (_⊢Nf⋆ *) p (con tcn)
lemcon refl tcn = refl

substTC : ∀{Φ Φ' : Ctx⋆}(p : Φ ≡ Φ')(tcn : TyCon)
  → NTermCon.TermCon {Φ = Φ} (con tcn)
  → NTermCon.TermCon {Φ = Φ'}(con tcn)
substTC refl tcn t = t

nfList : ∀{Δ} → List (Δ ⊢⋆ *) → List (Δ ⊢Nf⋆ *)
nfList []       = []
nfList (A ∷ As) = nf A ∷ nfList As

lemList : (bn : Builtin)
  → substEq (λ Φ → List (Φ ⊢Nf⋆ *)) (sym (nfTypeSIG≡₁ bn))
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
lemList ifThenElse = refl

nfType : ∀{Φ Γ}
  → {A : Φ ⊢⋆ *}
  → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ nf A
  
nfTypeTel : ∀{Φ Γ Δ}(σ : Sub Δ Φ)(As : List (Δ ⊢⋆ *))
  → Syn.Tel Γ Δ σ As
  → Norm.Tel (nfCtx Γ) Δ (nf ∘ σ) (nfList As)

nfTypeTel σ []           _            = Norm.[]
nfTypeTel {Γ} σ (A ∷ As) (M Syn.∷ Ms) =
  Norm.conv⊢
    refl
    (sym
      (trans
        (trans
          (subst-eval (embNf (nf A)) idCR (embNf ∘ nf ∘ σ))
          (fund
            (λ α → fund idCR (sym≡β (soundness (σ α))))
            (sym≡β (soundness A))))
        (sym (subst-eval A idCR σ)))) (nfType M)

  -- this should be a lemma in NBE/RenSubst
  -- substNf (nf ∘ σ) (nf C) ≡ nf (subst σ C)
  -- also it might go away if we simplify the builtins post size removal
  Norm.∷
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
nfType (Syn.ƛ t) = Norm.ƛ (nfType t)
nfType (t Syn.· u) = nfType t Norm.· nfType u
nfType (Syn.Λ {B = B} t) =
  Norm.Λ (Norm.conv⊢ refl (substNf-lemma' B) (nfType t))
nfType (Syn._·⋆_ {B = B} t A) = Norm.conv⊢
  refl
  (lem[] A B)
  (Norm._·⋆_ (Norm.conv⊢ refl (lemΠ B) (nfType t)) (nf A)) 
nfType (Syn.wrap A B t) = Norm.wrap
  (nf A)
  (nf B)
  (Norm.conv⊢ refl (stability-μ A B) (nfType t))
nfType (Syn.unwrap {A = A}{B = B} t) = Norm.conv⊢
  refl
  (sym (stability-μ A B))
  (Norm.unwrap (nfType t))
nfType (Syn.conv p t) = Norm.conv⊢ refl (completeness p) (nfType t)
nfType {Γ} (Syn.con {tcn = tcn} t) = Norm.con (nfTypeTC t)
nfType {Γ} (Syn.builtin bn σ tel) = let
  Δ ,, As ,, C = SSig.SIG bn
  Δ' ,, As' ,, C' = NSig.SIG bn
  in Norm.conv⊢
    refl
    (lemσ σ C C' (sym (nfTypeSIG≡₁ bn)) (nfTypeSIG≡₂ bn))
    (Norm.builtin
      bn
      ((nf ∘ σ ∘ substEq (_∋⋆ _) (sym (nfTypeSIG≡₁ bn))))
      (nfTypeTel' σ As (sym (nfTypeSIG≡₁ bn)) As' (lemList bn) tel))
nfType (Syn.pbuiltin b Ψ' σ As' (inj₁ (p ,, q)) ts) = Norm.conv⊢ refl {!!} (Norm.pbuiltin b Ψ' (nf ∘ σ) (nfList As') (inj₁ (substEq (Ψ' ≤C⋆'_) (nfTypeSIG≡₁ b) p ,, cong nfList q)) (nfTypeTel σ As' ts))
nfType (Syn.pbuiltin b Ψ' σ As' (inj₂ p) ts) = Norm.pbuiltin b Ψ' (nf ∘ σ) (nfList As') (inj₂ ({!!} ,, {!proj₂ p!}) ) (nfTypeTel σ As' ts)
nfType (Syn.ibuiltin b σ⋆ σ) = {!!}
nfType (Syn.ipbuiltin b Ψ' Δ' p σ⋆ σ) = {!!}
nfType (Syn.error A) = Norm.error (nf A)

completenessT : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ nf A × (A ≡β embNf (nf A))
completenessT {A = A} t = nfType t ,, soundness A
\end{code}
