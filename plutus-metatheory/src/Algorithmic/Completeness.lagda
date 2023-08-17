\begin{code}
module Algorithmic.Completeness where

open import Data.Nat using (zero;suc)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec;[];_∷_;lookup) renaming (map to vmap)
open import Data.List.NonEmpty using (_∷_;toList)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;sym;trans;cong₂) 
                                                  renaming (subst to substEq) 
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_)
open import Data.Product using (_×_) renaming (_,_ to _,,_)


open import Utils using (Kind;*;♯)
open import Utils.List using (List;IList;[];_∷_)
open import Type using (_⊢⋆_;_∋⋆_;Z;S;Ctx⋆;∅;_,⋆_)
open _⊢⋆_

open import Type.Equality using (_≡β_;≡2β)
open _≡β_
open import Type.RenamingSubstitution using (weaken;ren;_[_];sub-cons;Sub;sub;sub∅;sub-cong)
open import Builtin using (signature)
open import Builtin.Signature using (Sig;sig;_⊢♯;_/_⊢⋆;mkCtx⋆)
open _/_⊢⋆
open import Builtin.Constant.Type

import Declarative as Syn
import Algorithmic as Norm
import Algorithmic.Signature as Norm
open import Type.BetaNormal using (embNf;weakenNf;ne;_⊢Nf⋆_;_⊢Ne⋆_)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.BetaNBE using (nf;idEnv;reify;eval;exte;eval-VecList;eval-List;lookup-eval-VecList)
open import Type.BetaNBE.Completeness using (completeness;sub-eval;idCR;fund;symCR;reifyCR;exte-lem;idext)
open import Type.BetaNBE.RenamingSubstitution using (ren-nf;subNf;subNf-cong;subNf-cong';subNf-lemma';_[_]Nf;subNf-cons;subNf∅;subNf∅≡subNf;subNf-nf)
open import Type.BetaNBE.Soundness using (soundness)
open import Type.BetaNBE.Stability using (stability)

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
 
\end{code}

We need to prove that the type of a builtin `b` for the Algorithmic system is the same as normalising the type
of the Declarative system
           Norm.btype b ≡ nf (Syn.btype b)
           
This involves doing an analogous proof for every function in the definition of btype

\begin{code}
subNf-sub∅ : ∀{Φ}{K} (A : ∅ ⊢⋆ K) → nf {Φ} (sub∅ A) ≡ subNf (λ()) (nf A)
subNf-sub∅ {Φ} A = begin
          nf (sub∅ A)
        ≡⟨⟩
          nf (sub (λ ()) A)
        ≡⟨ cong nf (sub-cong (λ ()) A) ⟩  
          nf (sub (embNf ∘ λ ()) A)
        ≡⟨ subNf-nf ((λ ())) A ⟩
          subNf (λ ()) (nf A)
        ∎

subNf∅-sub∅ : ∀{Φ}{K} (A : ∅ ⊢⋆ K) → nf {Φ} (sub∅ A) ≡ subNf∅ (nf A)
subNf∅-sub∅ A = trans (subNf-sub∅ A) (sym subNf∅≡subNf)

con-injective : ∀ {Φ}{n m : Φ ⊢Nf⋆ ♯} → _≡_ {_} {Φ ⊢Nf⋆ *} (con n) (con m) → n ≡ m
con-injective refl = refl

helper : ∀ {n⋆} {n♯} (x : n♯ ⊢♯) → ne (Norm.⊢♯2TyNe♯ x) ≡ eval (Syn.⊢♯2TyNe♯ x) (idEnv (Builtin.Signature.mkCtx⋆ n⋆ n♯))
helper (_⊢♯.` x) = refl
helper (_⊢♯.atomic x) = refl
helper (_⊢♯.list x) = cong ne (cong (^ list ·_) (helper x))
helper (_⊢♯.pair x y) = cong ne (cong₂ (λ x y → ^ pair · x · y) (helper x) (helper y))

mkTy-lem : ∀ {n⋆ n♯}(t : n⋆ / n♯ ⊢⋆) → Norm.mkTy t ≡ nf (Syn.mkTy t)
mkTy-lem (` x) = refl
mkTy-lem (x ↑) = cong con (helper x)

sig2type⇒-lem : ∀{n⋆ n♯}{algRes}{synRes} (args : List (n⋆ / n♯ ⊢⋆)) → (algRes ≡ nf synRes) →
                          Norm.sig2type⇒ args algRes ≡ nf (Syn.sig2type⇒ args synRes)
sig2type⇒-lem [] p = p
sig2type⇒-lem (x ∷ args) p = sig2type⇒-lem args (cong₂ _⇒_ (mkTy-lem x) p)

sig2typeΠ-lem : ∀{n⋆ n♯}{t : mkCtx⋆ n⋆ n♯ ⊢⋆ *}{at : mkCtx⋆ n⋆ n♯ ⊢Nf⋆ *} → (at ≡ nf t) →
                          Norm.sig2typeΠ at ≡ nf (Syn.sig2typeΠ t)
sig2typeΠ-lem {zero} {zero} p = p
sig2typeΠ-lem {zero} {suc n♯} {t} refl = sig2typeΠ-lem {_} {n♯} (cong Π (sym (reifyCR (idext exte-lem t))))
sig2typeΠ-lem {suc n} {n♯} {t} refl = sig2typeΠ-lem {n} (cong Π (sym (reifyCR (idext exte-lem t))))

sig2type-lem : ∀ s → Norm.sig2type s ≡ nf (Syn.sig2type s) 
sig2type-lem (sig zero zero a r) = sig2type⇒-lem (toList a) (mkTy-lem r)

sig2type-lem (sig zero (suc n) (head ∷ tail) r) = sig2typeΠ-lem {t = Π (Syn.sig2type⇒ tail (Syn.mkTy head ⇒ Syn.mkTy r))}
                  {Π (Norm.sig2type⇒ tail (Norm.mkTy head ⇒ Norm.mkTy r))}
                  (cong Π (trans (sig2type⇒-lem {zero} {suc n} {Norm.mkTy r} {Syn.mkTy r} (head ∷ tail) (mkTy-lem r)) 
                                 (sym (reifyCR (idext exte-lem (Syn.sig2type⇒ tail (Syn.mkTy head ⇒ Syn.mkTy r)))))
                   )) 
sig2type-lem (sig (suc n) n♯ (head ∷ tail) r) = sig2typeΠ-lem {t = Π (Syn.sig2type⇒ tail (Syn.mkTy head ⇒ Syn.mkTy r))}
                  {Π (Norm.sig2type⇒ tail (Norm.mkTy head ⇒ Norm.mkTy r))}
                  (cong Π (trans (sig2type⇒-lem {suc n} {n♯} {Norm.mkTy r} {Syn.mkTy r} (head ∷ tail) (mkTy-lem r)) 
                                 (sym (reifyCR (idext exte-lem (Syn.sig2type⇒ tail (Syn.mkTy head ⇒ Syn.mkTy r)))))
                   )) 

btype-lem : ∀ {Φ} b → Norm.btype {Φ} b ≡ nf (Syn.btype b)
btype-lem b = begin 
        Norm.btype b
      ≡⟨⟩
        subNf∅ (Norm.sig2type (signature b))
      ≡⟨ cong subNf∅ (sig2type-lem (signature  b)) ⟩
        subNf∅ (nf (Syn.sig2type (signature b)))
      ≡⟨ sym (subNf∅-sub∅ (Syn.sig2type (signature b))) ⟩
         nf (sub∅ (Syn.sig2type (signature b)))
      ≡⟨⟩
       nf (Syn.btype b)
      ∎
\end{code}

\begin{code}
nfType : ∀{Φ Γ}
  → {A : Φ ⊢⋆ *}
  → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ nf A  

nfType-ConstrArgs : ∀ {Φ} {Γ : Syn.Ctx Φ} 
                  {TS : List (Φ ⊢⋆ *)}
                → (cs : Syn.ConstrArgs Γ TS) 
                → Norm.ConstrArgs (nfCtx Γ) (eval-List TS (idEnv Φ))
nfType-ConstrArgs [] = []
nfType-ConstrArgs (c ∷ cs) = (nfType c) ∷ (nfType-ConstrArgs cs)

lemma-mkCaseType : ∀{Φ}{B} AS → 
   nf (Syn.mkCaseType B AS) ≡ Norm.mkCaseType (nf B) (eval-List AS (idEnv Φ))
lemma-mkCaseType [] = refl
lemma-mkCaseType (A ∷ AS) = cong (eval A (idEnv _) ⇒_) (lemma-mkCaseType AS)

nfType-Cases : ∀ {Φ} {Γ : Syn.Ctx Φ} {A : Φ ⊢⋆ *} {n}
                 {tss : Vec (List (Φ ⊢⋆ *)) n} 
                 (cases : Syn.Cases Γ A tss) →
               Norm.Cases (nfCtx Γ) (nf A) (eval-VecList tss (idEnv Φ))
nfType-Cases Syn.[] = Norm.[]
nfType-Cases (Syn._∷_ {AS = AS} c cases) = substEq (nfCtx _ Norm.⊢_) (lemma-mkCaseType AS)  (nfType c) 
                                           Norm.∷ (nfType-Cases cases)

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
nfType (Syn.con {A} t p) = Norm.con {A = nf A} t (trans (completeness p) (subNf∅-sub∅ A))
nfType (Syn.builtin b) = Norm.conv⊢ refl (btype-lem b) (Norm.builtin b / refl)
nfType (Syn.error A) = Norm.error (nf A)
nfType (Syn.constr e TSS refl cs) = Norm.constr e (eval-VecList TSS (idEnv _)) (sym (lookup-eval-VecList e TSS (idEnv _))) (nfType-ConstrArgs cs)
nfType (Syn.case t cases) = Norm.case (nfType t) (nfType-Cases cases)

completenessT : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ nf A × (A ≡β embNf (nf A))
completenessT {A = A} t = nfType t ,, soundness A
\end{code}
