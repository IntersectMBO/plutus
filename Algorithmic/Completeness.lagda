\begin{code}
module Algorithmic.Completeness where

open import Type
open import Type.RenamingSubstitution
import Declarative.Term as Syn
import Algorithmic.Term as Norm
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Type.BetaNBE.RenamingSubstitution

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

lemT : ∀{Γ Γ' K J}(A : Γ ⊢⋆ K)
  → (p : Γ ≡ Γ')
  → (q : Γ ,⋆ J ≡ Γ' ,⋆ J)
  → weakenNf (substEq (_⊢Nf⋆ K) p (nf A)) ≡
    substEq (_⊢Nf⋆ K) q (nf (rename S A))
lemT A refl refl = rename-nf S A

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
nfTyVar {Γ Syn.,⋆ K} (Syn.T {A = A} α) = subst∋
  refl
  (lemT A (nfCtx∥ Γ) (nfCtx∥ (Γ Syn.,⋆ K)))
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

lemX : ∀{Γ Γ' K}(p : Γ ≡ Γ')(pat : Γ ⊢Nf⋆ _)(arg : Γ ⊢Nf⋆ _) →
  substEq (_⊢Nf⋆ *) p (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
  ≡
  nf (embNf (substEq (_⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *) p pat) · (μ1 · embNf (substEq (_⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *) p pat)) · embNf (substEq (_⊢Nf⋆ K) p arg))
lemX refl pat arg = refl

open import Type.Equality
open import Type.BetaNBE.Soundness

lemXX : ∀{Γ K}(pat : Syn.∥ Γ ∥ ⊢⋆ _)(arg : Syn.∥ Γ ∥ ⊢⋆ _) →
  substEq (_⊢Nf⋆ *) (nfCtx∥ Γ) (nf (pat · (μ1 · pat) · arg)) ≡
  nf
  (embNf (substEq (_⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *) (nfCtx∥ Γ) (nf pat)) ·
   (μ1 ·
    embNf (substEq (_⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *) (nfCtx∥ Γ) (nf pat)))
   · embNf (substEq (_⊢Nf⋆ K) (nfCtx∥ Γ) (nf arg)))
lemXX {Γ} pat arg = trans
  (cong (substEq (_⊢Nf⋆ *) (nfCtx∥ Γ))  (completeness (·≡β (·≡β (soundness pat) (·≡β (refl≡β μ1) (soundness pat))) (soundness arg))))
  (lemX (nfCtx∥ Γ) (nf pat) (nf arg))

open import Type.BetaNBE.Stability

lemμ' : ∀{Γ Γ' K}(p : Γ ≡ Γ')(pat : Γ ⊢Nf⋆ _)(arg : Γ ⊢Nf⋆ _) →
  ne ((μ1 · substEq (_⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *) p pat) · substEq (_⊢Nf⋆ K) p arg)
  ≡
  substEq (_⊢Nf⋆ *) p (ne (μ1 · pat · arg))
lemμ' refl pat arg = refl


lem[] : ∀{Γ Γ' K}(p : Γ ≡ Γ')(q : Γ ,⋆ K ≡ Γ' ,⋆ K)(A : Γ ⊢Nf⋆ K)(B : Γ ,⋆ K ⊢Nf⋆ *) →
  (substEq (_⊢Nf⋆ *) q B [ substEq (_⊢Nf⋆ K) p A ]Nf)
  ≡ substEq (_⊢Nf⋆ *) p (nf (subst (subst-cons ` (embNf A)) (embNf B)))
lem[] refl refl A B =  evalCRSubst idCR (subst-cong (λ { Z → refl ; (S α) → refl}) (embNf B)) 

lem[]' : ∀{Γ K}(A : Syn.∥ Γ ∥ ⊢⋆ K)(B : Syn.∥ Γ ∥ ,⋆ K ⊢⋆ *) → (substEq (_⊢Nf⋆ *) (cong (_,⋆ K) (nfCtx∥ Γ))
 (eval B (exte (idEnv Syn.∥ Γ ∥)))
 [ substEq (_⊢Nf⋆ K) (nfCtx∥ Γ) (nf A) ]Nf)
  ≡ substEq (_⊢Nf⋆ *) (nfCtx∥ Γ) (nf (subst (subst-cons ` A) B))
lem[]' {Γ} A B = trans
  (lem[] (nfCtx∥ Γ) (cong (_,⋆ _) (nfCtx∥ Γ)) (nf A) (eval B (exte (idEnv _))))
  (cong
    (substEq (_⊢Nf⋆ *) (nfCtx∥ Γ))
    (trans
      (trans
        (subst-eval
          (embNf (eval B (exte (idEnv _))))
          idCR
          (subst-cons ` (embNf (nf A))))
        (trans
          (fund
            (λ x → idext idCR (subst-cons ` (embNf (nf A)) x))
            (sym≡β (evalSR B (SRweak idSR))))
          (trans
            (subst-eval
              B
              (λ x → idext idCR (subst-cons ` (embNf (nf A)) x))
              (exts `))
            (idext (λ { Z → symCR (fund idCR (soundness A))
                      ; (S α) → idCR α}) B))))
      (sym (subst-eval B idCR (subst-cons ` A)))))

import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * # _∋⋆_ Z S _⊢⋆_ ` con boolean size⋆
  as SSig
import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * # _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con Norm.booleanNf size⋆
  as NSig
open import Builtin
import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆ as STermCon 
import Builtin.Constant.Term Ctx⋆ Kind * # _⊢Nf⋆_ con size⋆ as NTermCon 


nfTypeTC : ∀{φ}{A : φ ⊢⋆ *} → STermCon.TermCon A → NTermCon.TermCon (nf A)
nfTypeTC (STermCon.integer s i p)    = NTermCon.integer s i p
nfTypeTC (STermCon.bytestring s b p) = NTermCon.bytestring s b p 
nfTypeTC (STermCon.size s)           = NTermCon.size s

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
nfTypeSIG≡₁ resizeInteger = refl
nfTypeSIG≡₁ sizeOfInteger = refl
nfTypeSIG≡₁ intToByteString = refl
nfTypeSIG≡₁ concatenate = refl
nfTypeSIG≡₁ takeByteString = refl
nfTypeSIG≡₁ dropByteString = refl
nfTypeSIG≡₁ sha2-256 = refl
nfTypeSIG≡₁ sha3-256 = refl
nfTypeSIG≡₁ verifySignature = refl
nfTypeSIG≡₁ resizeByteString = refl
nfTypeSIG≡₁ equalsByteString = refl
nfTypeSIG≡₁ txh = refl
nfTypeSIG≡₁ blocknum = refl

lemσ : ∀{Γ Γ' Δ Δ'}
  → (σ : Sub Δ Γ)
  → (p : Γ ≡ Γ')
  → (C : Δ ⊢⋆ *)
  → (C' : Δ' ⊢Nf⋆ *)
  → (q : Δ' ≡ Δ)
  → nf C ≡ substEq (_⊢Nf⋆ *) q C' → 
  substNf
      (λ {J} α →
         nf
         (substEq (_⊢⋆ J) p
          (σ (substEq (_∋⋆ J) q α))))
      C'
      ≡
      substEq (_⊢Nf⋆ *) p
      (nf (subst σ C))
lemσ σ refl C _ refl refl = trans
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
nfTypeSIG≡₂ resizeInteger = refl
nfTypeSIG≡₂ sizeOfInteger = refl
nfTypeSIG≡₂ intToByteString = refl
nfTypeSIG≡₂ concatenate = refl
nfTypeSIG≡₂ takeByteString = refl
nfTypeSIG≡₂ dropByteString = refl
nfTypeSIG≡₂ sha2-256 = refl
nfTypeSIG≡₂ sha3-256 = refl
nfTypeSIG≡₂ verifySignature = refl
nfTypeSIG≡₂ resizeByteString = refl
nfTypeSIG≡₂ equalsByteString = refl
nfTypeSIG≡₂ txh = refl
nfTypeSIG≡₂ blocknum = refl
open import Builtin.Constant.Type

lemcon : ∀{Γ Γ'}(p : Γ ≡ Γ')(tcn : TyCon)(s : Γ ⊢Nf⋆ #)
  → con tcn (substEq (_⊢Nf⋆ #) p s) ≡ substEq (_⊢Nf⋆ *) p (con tcn s)
lemcon refl tcn s = refl

substTC : ∀{Γ Γ'}(p : Γ ≡ Γ')(s : Γ ⊢Nf⋆ #)(tcn : TyCon)
  → NTermCon.TermCon (con tcn s)
  → NTermCon.TermCon (con tcn (substEq (_⊢Nf⋆ #) p s))
substTC refl s tcn t = t

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
lemList resizeInteger = refl
lemList sizeOfInteger = refl
lemList intToByteString = refl
lemList concatenate = refl
lemList takeByteString = refl
lemList dropByteString = refl
lemList sha2-256 = refl
lemList sha3-256 = refl
lemList verifySignature = refl
lemList resizeByteString = refl
lemList equalsByteString = refl
lemList txh = refl
lemList blocknum = refl

nfType : ∀{Γ K}
  → {A : Syn.∥ Γ ∥ ⊢⋆ K}
  → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ substEq (_⊢Nf⋆ K) (nfCtx∥ Γ) (nf A)
  
nfTypeTel : ∀{Γ Δ}(σ : Sub Δ Syn.∥ Γ ∥)(As : List (Δ ⊢⋆ *))
  → Syn.Tel Γ Δ σ As
  → Norm.Tel (nfCtx Γ) Δ (nf ∘ substEq (_⊢⋆ _) (nfCtx∥ Γ) ∘ σ) (nfList As)
  
nfTypeTel σ []        _ = _
nfTypeTel {Γ} σ (A ∷ As) (M ,, Ms) =
  subst⊢ refl (sym (lemσ σ (nfCtx∥ Γ) A (nf A) refl refl)) (nfType M)
  ,,
  nfTypeTel σ As Ms

nfTypeTel' : ∀{Γ Δ Δ'}(σ : Sub Δ Syn.∥ Γ ∥)(As : List (Δ ⊢⋆ *))
  → (q : Δ' ≡ Δ)
  → (As' : List (Δ' ⊢Nf⋆ *))
  → (substEq (λ Δ → List (Δ ⊢Nf⋆ *)) q As' ≡ nfList As)
  → Syn.Tel Γ Δ σ As
  → Norm.Tel
      (nfCtx Γ)
      Δ'
      (nf ∘ substEq (_⊢⋆ _) (nfCtx∥ Γ) ∘ σ ∘ substEq (_∋⋆ _) q)
      As'
nfTypeTel' σ As refl .(nfList As) refl tel = nfTypeTel σ As tel

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
nfType {Γ} (Syn._·⋆_ {B = B} t A) = subst⊢
  refl
  (lem[]' {Γ} A B)
  (subst⊢ refl (sym (lemΠ (nfCtx∥ Γ) (cong (_,⋆ _) (nfCtx∥ Γ)) _)) (nfType t)
  Norm.·⋆
  -- is there another version where this is just nf A?
  substEq (_⊢Nf⋆ _) (nfCtx∥ Γ) (nf A)) 
nfType {Γ} (Syn.wrap1 pat arg t) = subst⊢
  refl
  (lemμ' (nfCtx∥ Γ) (nf pat) (nf arg))
  (Norm.wrap1
    (substEq (_⊢Nf⋆ _) (nfCtx∥ Γ ) (nf pat))
    (substEq (_⊢Nf⋆ _) (nfCtx∥ Γ) (nf arg))
    (subst⊢ refl (lemXX {Γ} pat arg) (nfType t)))
nfType {Γ} (Syn.unwrap1 {pat = pat}{arg} t) = subst⊢
  refl
  (sym (lemXX {Γ} pat arg))
  (Norm.unwrap1
    (subst⊢ refl (sym (lemμ' (nfCtx∥ Γ) (nf pat) (nf arg))) (nfType t))) 
nfType (Syn.conv p t) rewrite sym (completeness p) = nfType t
nfType {Γ} (Syn.con {s = s}{tcn = tcn} t) = subst⊢
  refl
  (lemcon (nfCtx∥ Γ) tcn (nf s))
  (Norm.con (substTC (nfCtx∥ Γ) (nf s) tcn (nfTypeTC t) ))
nfType {Γ} (Syn.builtin bn σ tel) = let
  Δ ,, As ,, C = SSig.SIG bn
  Δ' ,, As' ,, C' = NSig.SIG bn
  in subst⊢
  refl
  (lemσ σ (nfCtx∥ Γ) C C'  (sym (nfTypeSIG≡₁ bn)) (nfTypeSIG≡₂ bn))
  (Norm.builtin
    bn
    (λ α → nf
      (substEq
        (_⊢⋆ _)
        (nfCtx∥ Γ)
        (σ (substEq (_∋⋆ _) (sym (nfTypeSIG≡₁ bn)) α))))
        (nfTypeTel' σ As (sym (nfTypeSIG≡₁ bn)) As' (lemList bn) tel ))
nfType {Γ} (Syn.error A) = Norm.error (substEq  (_⊢Nf⋆ *) (nfCtx∥ Γ) (nf A))

completenessT : ∀{Γ K}
  → {A : Syn.∥ Γ ∥ ⊢⋆ K}
  → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ substEq (_⊢Nf⋆ K) (nfCtx∥ Γ) (nf A) × (A ≡β embNf (nf A))
completenessT {A = A} t = nfType t ,, soundness A
\end{code}

