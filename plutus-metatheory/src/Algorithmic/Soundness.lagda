\begin{code}
module Algorithmic.Soundness where

open import Function using (_∘_)
open import Data.Empty using (⊥)
open import Data.List using (List;[];_∷_)
open import Data.Product using (_×_) renaming (_,_ to _,,_)
open import Data.Unit using (⊤;tt)
open import Relation.Binary.PropositionalEquality 
              using (_≡_;refl;sym;trans;cong)
              renaming (subst to substEq)

open import Utils using (Kind;*;_⇒_)
open import Type using (Ctx⋆;_,⋆_;_⊢⋆_;_∋⋆_;S;Z)
open _⊢⋆_

open import Type.RenamingSubstitution using (_[_];sub-cons;weaken;sub)
open import Type.Equality using (_≡β_;≡2β)
open _≡β_

import Declarative as Dec
import Algorithmic as Alg
import Algorithmic.Signature as Alg
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;embNf;ren-embNf;weakenNf)
open _⊢Nf⋆_
open _⊢Ne⋆_

open import Type.BetaNBE using (nf;eval;idEnv)
open import Type.BetaNBE.Completeness using (sub-eval;idCR;idext;reflectCR;fund)
open import Type.BetaNBE.Soundness using (soundness)
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf;subNf;subNf-cons)
open import Builtin using (Builtin)
import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con as STermCon
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as NTermCon
\end{code}

\begin{code}
embCtx : ∀{Φ} → Alg.Ctx Φ → Dec.Ctx Φ
embCtx Alg.∅       = Dec.∅
embCtx (Γ Alg.,⋆ K) = embCtx Γ Dec.,⋆ K
embCtx (Γ Alg., A)  = embCtx Γ Dec., embNf A
\end{code}

\begin{code}
embVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}
  → Γ Alg.∋ A
  → embCtx Γ Dec.∋ embNf A
embVar Alg.Z     = Dec.Z
embVar (Alg.S α) = Dec.S (embVar α)
embVar (Alg.T {A = A} α) =
  Dec.conv∋ refl (sym (ren-embNf S A)) (Dec.T (embVar α))
\end{code}

\begin{code}
emb[] : ∀{Γ K}(A : Γ ⊢Nf⋆ K)(B : Γ ,⋆ K ⊢Nf⋆ *) →
  (embNf B [ embNf A ]) ≡β embNf (B [ A ]Nf)
emb[] A B = trans≡β
  (soundness (embNf B [ embNf A ]))
  (≡2β (cong embNf
    (trans
      (trans
        (sub-eval (embNf B) idCR (sub-cons ` (embNf A)))
        (idext (λ { Z → idext idCR (embNf A)
                  ; (S α) → reflectCR (refl {x = ` α})}) (embNf B)))
      (sym (sub-eval (embNf B) idCR (embNf ∘ subNf-cons (ne ∘ `) A))))))
\end{code}

\begin{code}
soundness-μ : ∀{Φ Φ' K}(p : Φ ≡ Φ')(A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)(B : Φ ⊢Nf⋆ K) →
  embNf A · ƛ (μ (weaken (embNf A)) (` Z)) · embNf B ≡β
  embNf
    (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
soundness-μ p A B = trans≡β
  (soundness (embNf A · ƛ (μ (weaken (embNf A)) (` Z)) · embNf B))
  (≡2β (cong (λ X → embNf (nf (embNf A · ƛ (μ X (` Z)) · embNf B)))
             (sym (ren-embNf S A))))
\end{code}

\begin{code}

embTC : ∀{φ}{A : φ ⊢Nf⋆ *}
  → NTermCon.TermCon A
  → STermCon.TermCon (embNf A)
embTC (NTermCon.integer i)    = STermCon.integer i
embTC (NTermCon.bytestring b) = STermCon.bytestring b
embTC (NTermCon.string s)     = STermCon.string s
embTC (NTermCon.bool b)       = STermCon.bool b
embTC NTermCon.unit           = STermCon.unit
embTC (NTermCon.pdata d)       = STermCon.pdata d
embTC (NTermCon.bls12-381-g1-element e) = STermCon.bls12-381-g1-element e
embTC (NTermCon.bls12-381-g2-element e) = STermCon.bls12-381-g2-element e
embTC (NTermCon.bls12-381-mlresult r)   = STermCon.bls12-381-mlresult r
\end{code}

\begin{code}

lemσ' : ∀{Γ Γ' Δ Δ'}(bn : Builtin)(p : Γ ≡ Γ')
  → (C : Δ ⊢⋆ *)(C' : Δ' ⊢Nf⋆ *) → (q : Δ ≡ Δ')
  → (σ : {J : Kind} → Δ' ∋⋆ J → Γ ⊢Nf⋆ J)
  → nf C ≡ substEq (_⊢Nf⋆ *) (sym q) C' →
  sub
  (λ {J} α →
     substEq (_⊢⋆ J) p
     (embNf (σ (substEq (_∋⋆ J) q α))))
  C
  ≡β
  substEq (_⊢⋆ *) p
  (embNf
   (eval
    (sub (λ {J₁} x → embNf (σ x))
     (embNf C'))
    (idEnv Γ)))
lemσ' bn refl C C' refl σ p =  trans≡β
  (soundness (sub (embNf ∘ σ) C))
  (trans≡β
    (≡2β (cong embNf (sub-eval C idCR (embNf ∘ σ))))
    (trans≡β
      (≡2β (cong embNf (fund (λ α → idext  idCR (embNf (σ α))) (soundness C))))
      (trans≡β (≡2β (sym (cong embNf (sub-eval (embNf (nf C)) idCR (embNf ∘ σ))))) (≡2β (cong embNf (cong nf (cong (sub (embNf ∘ σ)) (cong embNf p))))))))

_≡βL_ : ∀{Δ} → (As As' : List (Δ ⊢⋆ *)) → Set
[]       ≡βL []         = ⊤
[]       ≡βL (A' ∷ As') = ⊥
(A ∷ As) ≡βL []         = ⊥
(A ∷ As) ≡βL (A' ∷ As') = (A ≡β A') × (As ≡βL As')

refl≡βL : ∀{Δ} → (As : List (Δ ⊢⋆ *)) → As ≡βL As
refl≡βL [] = tt
refl≡βL (x ∷ As) = (refl≡β x) ,, (refl≡βL As)

embList : ∀{Δ} → List (Δ ⊢Nf⋆ *) → List (Δ ⊢⋆ *)
embList []       = []
embList (A ∷ As) = embNf A ∷ embList As

lemsub : ∀{Γ Δ}(A : Δ ⊢Nf⋆ *)(A' : Δ ⊢⋆ *)
  → (σ : {J : Kind} → Δ ∋⋆ J → Γ ⊢Nf⋆ J)
  → embNf A ≡β A' →
  (embNf (subNf σ A)) ≡β
  sub (λ {J} α → embNf (σ α)) A'
lemsub A A' σ p = trans≡β
  (trans≡β
    (≡2β (cong embNf (sub-eval (embNf A) idCR (embNf ∘ σ))))
    (trans≡β
      (≡2β (cong embNf (fund (λ α → idext  idCR (embNf (σ α))) p)))
      ((≡2β (sym (cong embNf (sub-eval A' idCR (embNf ∘ σ))))))))
  (sym≡β (soundness (sub (embNf ∘ σ) A')))

postulate btype-lem≡β : ∀{Φ} b → Dec.btype {Φ} b ≡β embNf (Alg.btype b)

emb : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ Alg.⊢ A → embCtx Γ Dec.⊢ embNf A
emb (Alg.` α) = Dec.` (embVar α)
emb (Alg.ƛ {A = A}{B} t) = Dec.ƛ (emb t)
emb (Alg._·_ {A = A}{B} t u) = emb t Dec.· emb u
emb (Alg.Λ {B = B} t) = Dec.Λ (emb t)
emb (Alg._·⋆_/_ {B = B} t A refl) =
    Dec.conv (emb[] A B) (emb t Dec.·⋆ embNf A)
emb (Alg.wrap A B t) = Dec.wrap
  (embNf A)
  (embNf B)
  (Dec.conv (sym≡β (soundness-μ refl A B)) (emb t))
emb (Alg.unwrap {A = A}{B} t refl) =
  Dec.conv (soundness-μ refl A B) (Dec.unwrap (emb t))
emb (Alg.con  {tcn = tcn} t ) = Dec.con (embTC t)
emb (Alg.builtin b / refl) = Dec.conv (btype-lem≡β b) (Dec.builtin b)
emb (Alg.error A) = Dec.error (embNf A)

soundnessT : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ Alg.⊢ A → embCtx Γ Dec.⊢ embNf A
soundnessT = emb
\end{code}
