\begin{code}
module Algorithmic.Completeness where



open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;sym;trans) 
                                                  renaming (subst to substEq) 
open import Function using (_∘_)
open import Data.Product using (_×_) renaming (_,_ to _,,_)
open import Data.List using (List;[];_∷_)

open import Utils using (Kind;*)
open import Type using (_⊢⋆_;_∋⋆_;Z;S;Ctx⋆;_,⋆_)
open _⊢⋆_

open import Type.Equality using (_≡β_;≡2β)
open _≡β_
open import Type.RenamingSubstitution using (weaken;ren;_[_];sub-cons;Sub;sub)
import Declarative as Syn
import Algorithmic as Norm
import Algorithmic.Signature as Norm
open import Type.BetaNormal using (embNf;weakenNf;ne;_⊢Nf⋆_;_⊢Ne⋆_)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.Completeness using (completeness;sub-eval;idCR;fund;symCR)
open import Type.BetaNBE.RenamingSubstitution using (ren-nf;subNf;subNf-cong';subNf-lemma';_[_]Nf;subNf-cons)
open import Type.BetaNBE.Soundness using (soundness)
import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con as STermCon
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as NTermCon

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


lemΠ : ∀{Γ K }(B : Γ ,⋆ K ⊢⋆ *) →
       nf (Π B) ≡ Π (nf B)
lemΠ B = cong Π (sym (subNf-lemma' B))



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

lem[] : ∀{Γ K}(A : Γ ⊢⋆ K)(B : Γ ,⋆ K ⊢⋆ *) →
  (nf B [ nf A ]Nf) ≡ nf (B [ A ])
lem[] A B = trans
  (sub-eval (embNf (nf B)) idCR (embNf ∘ subNf-cons (ne ∘ `) (nf A)))
  (trans
    (fund
      (λ {Z → symCR (fund idCR (soundness A)) ; (S α) → idCR _})
      (sym≡β (soundness B)))
    (sym (sub-eval B idCR (sub-cons ` A))))


nfTypeTC : ∀{φ}{A : φ ⊢⋆ *} → STermCon.TermCon A → NTermCon.TermCon (nf A)
nfTypeTC (STermCon.integer i)    = NTermCon.integer i
nfTypeTC (STermCon.bytestring b) = NTermCon.bytestring b
nfTypeTC (STermCon.string s)     = NTermCon.string s
nfTypeTC (STermCon.bool b)       = NTermCon.bool b
nfTypeTC STermCon.unit           = NTermCon.unit
nfTypeTC (STermCon.pdata d)       = NTermCon.pdata d

lemσ : ∀{Γ Δ Δ'}
  → (σ : Sub Δ Γ)
  → (C : Δ ⊢⋆ *)
  → (C' : Δ' ⊢Nf⋆ *)
  → (q : Δ' ≡ Δ)
  → nf C ≡ substEq (_⊢Nf⋆ *) q C' →
  subNf
      (λ {J} α →
         nf
          (σ (substEq (_∋⋆ J) q α)))
      C'
      ≡
      nf (sub σ C)
lemσ σ C _ refl q = trans
  (subNf-cong' (nf ∘ σ) (sym q))
  (trans
    (trans
      (sub-eval (embNf (nf C)) idCR (embNf ∘ nf ∘ σ))
      (fund (λ α → fund idCR (sym≡β (soundness (σ α)))) (sym≡β (soundness C))))
    (sym (sub-eval C idCR σ)))

-- this should be a lemma in NBE/RenSubst
-- subNf (nf ∘ σ) (nf C) ≡ nf (sub σ C)


nfList : ∀{Δ} → List (Δ ⊢⋆ *) → List (Δ ⊢Nf⋆ *)
nfList []       = []
nfList (A ∷ As) = nf A ∷ nfList As

postulate btype-lem : ∀ {Φ} b → Norm.btype {Φ} b ≡ nf (Syn.btype b)

nfType : ∀{Φ Γ}
  → {A : Φ ⊢⋆ *}
  → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ nf A
nfType (Syn.` α) = Norm.` (nfTyVar α)
nfType (Syn.ƛ t) = Norm.ƛ (nfType t)
nfType (t Syn.· u) = nfType t Norm.· nfType u
nfType (Syn.Λ {B = B} t) =
  Norm.Λ (Norm.conv⊢ refl (subNf-lemma' B) (nfType t))
nfType (Syn._·⋆_ {B = B} t A) = Norm.conv⊢
  refl
  (lem[] A B)
  (Norm._·⋆_/_ (Norm.conv⊢ refl (lemΠ B) (nfType t)) (nf A) refl)
nfType (Syn.wrap A B t) = Norm.wrap
  (nf A)
  (nf B)
  (Norm.conv⊢ refl (stability-μ A B) (nfType t))
nfType (Syn.unwrap {A = A}{B = B} t) = Norm.conv⊢
  refl
  (sym (stability-μ A B))
  (Norm.unwrap (nfType t) refl)
nfType (Syn.conv p t) = Norm.conv⊢ refl (completeness p) (nfType t)
nfType (Syn.con t) = Norm.con (nfTypeTC t)
nfType (Syn.builtin b) = Norm.conv⊢ refl (btype-lem b) (Norm.builtin b / refl)
nfType (Syn.error A) = Norm.error (nf A)

completenessT : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ nf A × (A ≡β embNf (nf A))
completenessT {A = A} t = nfType t ,, soundness A
\end{code}
