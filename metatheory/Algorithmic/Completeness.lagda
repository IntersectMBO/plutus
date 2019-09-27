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

nfCtx : ∀ {Φ} → Syn.Ctx Φ → Norm.Ctx Φ
nfCtx Syn.∅ = Norm.∅
nfCtx (Γ Syn.,⋆ K) = nfCtx Γ Norm.,⋆ K
nfCtx (Γ Syn., A) = nfCtx Γ Norm., nf A

nfTyVar : ∀{Φ Γ}
  → {A : Φ ⊢⋆ *}
  → Γ Syn.∋ A
  → nfCtx Γ Norm.∋ nf A
nfTyVar (Syn.Z p)           = Norm.Z (completeness (α2β p))
nfTyVar (Syn.S α)           = Norm.S (nfTyVar α)
nfTyVar (Syn.T {A = A} α p) = Norm.T
  (nfTyVar α)
  (transNf (ren-nf S A) (completeness (α2β p)))

open import Type.BetaNormal.Equality

lemΠ : ∀{Γ K }(B : Γ ,⋆ K ⊢⋆ *){x} →
       nf (Π x B) ≡Nf Π x (nf B)
lemΠ B = Π≡Nf (symNf (substNf-lemma' B))

open import Type.BetaNBE.Soundness

lemXX : ∀{Φ K}(pat :  Φ ⊢⋆ _)(arg : Φ ⊢⋆ K) →
  nf (pat · (μ1 · pat) · arg) ≡Nf
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
  (nf B [ nf A ]Nf) ≡Nf nf (B [ A ])
lem[] A B = transNf
  (subst-eval (embNf (nf B)) idCR (embNf ∘ substNf-cons (ne ∘ `) (nf A)))
  (transNf
    (fund
      (λ {Z → symCR (fund idCR (soundness A)) ; (S α) → idCR _})
      (sym≡β (soundness B)))
    (symNf (subst-eval B idCR (subst-cons ` A))))

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
nfTypeTC (STermCon.string s)     = NTermCon.string s

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
  → nf C ≡Nf substEq (_⊢Nf⋆ *) q C' →
  substNf
      (λ {J} α →
         nf
          (σ (substEq (_∋⋆ J) q α)))
      C'
      ≡Nf
      nf (subst σ C)
lemσ σ C _ refl q = transNf
  (substNf-cong' (nf ∘ σ) (symNf q))
  (transNf
    (transNf
      (subst-eval (embNf (nf C)) idCR (embNf ∘ nf ∘ σ))
      (fund (λ α → fund idCR (sym≡β (soundness (σ α)))) (sym≡β (soundness C))))
    (symNf (subst-eval C idCR σ)))
    
-- this should be a lemma in NBE/RenSubst
-- substNf (nf ∘ σ) (nf C) ≡ nf (subst σ C)

nfTypeSIG≡₂ : (bn : Builtin) →
  nf (proj₂ (proj₂ (SSig.SIG bn))) ≡Nf
  substEq (_⊢Nf⋆ *) (sym (nfTypeSIG≡₁ bn))
  (proj₂ (proj₂ (NSig.SIG bn)))
nfTypeSIG≡₂ addInteger = reflNf
nfTypeSIG≡₂ subtractInteger = reflNf
nfTypeSIG≡₂ multiplyInteger = reflNf
nfTypeSIG≡₂ divideInteger = reflNf
nfTypeSIG≡₂ quotientInteger = reflNf
nfTypeSIG≡₂ remainderInteger = reflNf
nfTypeSIG≡₂ modInteger = reflNf
nfTypeSIG≡₂ lessThanInteger = reflNf
nfTypeSIG≡₂ lessThanEqualsInteger = reflNf
nfTypeSIG≡₂ greaterThanInteger = reflNf
nfTypeSIG≡₂ greaterThanEqualsInteger = reflNf
nfTypeSIG≡₂ equalsInteger = reflNf
nfTypeSIG≡₂ concatenate = reflNf
nfTypeSIG≡₂ takeByteString = reflNf
nfTypeSIG≡₂ dropByteString = reflNf
nfTypeSIG≡₂ sha2-256 = reflNf
nfTypeSIG≡₂ sha3-256 = reflNf
nfTypeSIG≡₂ verifySignature = reflNf
nfTypeSIG≡₂ equalsByteString = reflNf
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

nfType : ∀{Φ Γ}
  → {A : Φ ⊢⋆ *}
  → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ nf A
  
nfTypeTel : ∀{Φ Γ Δ}(σ : Sub Δ Φ)(As : List (Δ ⊢⋆ *))
  → Syn.Tel Γ Δ σ As
  → Norm.Tel (nfCtx Γ) Δ (nf ∘ σ) (nfList As)

nfTypeTel σ []        _ = _
nfTypeTel {Γ} σ (A ∷ As) (M ,, Ms) =
  Norm.conv⊢
    Norm.reflCtx
    (symNf
      (transNf
        (transNf
          (subst-eval (embNf (nf A)) idCR (embNf ∘ nf ∘ σ))
          (fund
            (λ α → fund idCR (sym≡β (soundness (σ α))))
            (sym≡β (soundness A))))
        (symNf (subst-eval A idCR σ)))) (nfType M)

  -- this should be a lemma in NBE/RenSubst
  -- substNf (nf ∘ σ) (nf C) ≡ nf (subst σ C)
  -- also it might go away if we simplify the builtins post size removal
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
nfType (Syn.ƛ x t) = Norm.ƛ x (nfType t)
nfType (t Syn.· u) = nfType t Norm.· nfType u
nfType (Syn.Λ {B = B} x t) =
  Norm.Λ x (Norm.conv⊢ Norm.reflCtx (substNf-lemma' B) (nfType t))
nfType (Syn.·⋆ {B = B} t A p) = Norm.·⋆
  (Norm.conv⊢ Norm.reflCtx (lemΠ B) (nfType t))
  (nf A)
  (transNf (lem[] A B) (completeness (α2β p)))
nfType (Syn.wrap1 pat arg t) = Norm.wrap1
  (nf pat)
  (nf arg)
  (Norm.conv⊢ Norm.reflCtx (lemXX pat arg) (nfType t))
nfType (Syn.unwrap1 {pat = pat}{arg = arg} t p) = Norm.unwrap1
  (nfType t)
  (transNf
    (symNf (lemXX pat arg))
    (completeness
      (α2β (·≡α (·≡α (reflα {A = pat}) (·≡α μ≡α p)) (reflα {A = arg})))))
nfType (Syn.conv p t) = Norm.conv⊢ Norm.reflCtx (completeness p) (nfType t)
nfType {Γ} (Syn.con {tcn = tcn} t) = Norm.con (nfTypeTC t)
nfType {Γ} (Syn.builtin bn σ tel p) = let
  Δ ,, As ,, C = SSig.SIG bn
  Δ' ,, As' ,, C' = NSig.SIG bn
  in Norm.builtin
    bn
    ((nf ∘ σ ∘ substEq (_∋⋆ _) (sym (nfTypeSIG≡₁ bn))))
    (nfTypeTel' σ As (sym (nfTypeSIG≡₁ bn)) As' (lemList bn) tel)
    (transNf
      (lemσ σ C C' (sym (nfTypeSIG≡₁ bn)) (nfTypeSIG≡₂ bn))
      (completeness (α2β p)))
nfType {Γ} (Syn.error A) = Norm.error (nf A)

completenessT : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ nf A × (A ≡β embNf (nf A))
completenessT {A = A} t = nfType t ,, soundness A
\end{code}
