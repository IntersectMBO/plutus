\begin{code}
module Algorithmic.Soundness where

open import Function
open import Data.Product renaming (_,_ to _,,_)
open import Data.List hiding ([_])
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) hiding ([_])
open import Data.Sum

open import Type
open import Type.RenamingSubstitution
open import Type.Equality
import Declarative as Dec
import Algorithmic as Alg
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Type.BetaNBE.Soundness
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Builtin
import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con as STermCon
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as NTermCon
import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con
  as SSig
import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
  as NSig
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
        (subst-eval (embNf B) idCR (subst-cons ` (embNf A)))
        (idext (λ { Z → idext idCR (embNf A)
                  ; (S α) → reflectCR (refl {x = ` α})}) (embNf B)))
      (sym (subst-eval (embNf B) idCR (embNf ∘ substNf-cons (ne ∘ `) A))))))
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
embTC (NTermCon.char c)       = STermCon.char c
embTC NTermCon.unit           = STermCon.unit
\end{code}

\begin{code}
open import Algorithmic.Completeness

lemσ' : ∀{Γ Γ' Δ Δ'}(bn : Builtin)(p : Γ ≡ Γ')
  → (C : Δ ⊢⋆ *)(C' : Δ' ⊢Nf⋆ *) → (q : Δ ≡ Δ')
  → (σ : {J : Kind} → Δ' ∋⋆ J → Γ ⊢Nf⋆ J)
  → nf C ≡ substEq (_⊢Nf⋆ *) (sym q) C' →
  subst
  (λ {J} α →
     substEq (_⊢⋆ J) p
     (embNf (σ (substEq (_∋⋆ J) q α))))
  C
  ≡β
  substEq (_⊢⋆ *) p
  (embNf
   (eval
    (subst (λ {J₁} x → embNf (σ x))
     (embNf C'))
    (idEnv Γ)))
lemσ' bn refl C C' refl σ p =  trans≡β
  (soundness (subst (embNf ∘ σ) C))
  (trans≡β
    (≡2β (cong embNf (subst-eval C idCR (embNf ∘ σ))))
    (trans≡β
      (≡2β (cong embNf (fund (λ α → idext  idCR (embNf (σ α))) (soundness C))))
      (trans≡β (≡2β (sym (cong embNf (subst-eval (embNf (nf C)) idCR (embNf ∘ σ))))) (≡2β (cong embNf (cong nf (cong (subst (embNf ∘ σ)) (cong embNf p))))))))

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

open import Algorithmic.Completeness

lemList' : (bn : Builtin)
  → embList (proj₁ (proj₂ (NSig.SIG bn))) ≡βL
    substEq (λ Δ₁ → List (Δ₁ ⊢⋆ *)) (nfTypeSIG≡₁ bn)
    (proj₁ (proj₂ (SSig.SIG bn)))
lemList' addInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' subtractInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' multiplyInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' divideInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' quotientInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' remainderInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' modInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' lessThanInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' lessThanEqualsInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' greaterThanInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' greaterThanEqualsInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' equalsInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' concatenate = refl≡β _ ,, refl≡β _ ,, _
lemList' takeByteString = refl≡β _ ,, refl≡β _ ,, _
lemList' dropByteString = refl≡β _ ,, refl≡β _ ,, _
lemList' sha2-256 = refl≡β _ ,, _
lemList' sha3-256 = refl≡β _ ,, _
lemList' verifySignature = refl≡β _ ,, refl≡β _ ,, refl≡β _ ,, _
lemList' equalsByteString = refl≡β _ ,, refl≡β _ ,, _
lemList' ifThenElse = refl≡β _ ,, refl≡β _ ,, refl≡β _ ,, _
lemList' charToString = refl≡β _ ,, _
lemList' append = refl≡β _ ,, refl≡β _ ,, _
lemList' trace = refl≡β _ ,, _

lemsub : ∀{Γ Δ}(A : Δ ⊢Nf⋆ *)(A' : Δ ⊢⋆ *)
  → (σ : {J : Kind} → Δ ∋⋆ J → Γ ⊢Nf⋆ J)
  → embNf A ≡β A' →
  (embNf (substNf σ A)) ≡β
  subst (λ {J} α → embNf (σ α)) A'
lemsub A A' σ p = trans≡β
  (trans≡β
    (≡2β (cong embNf (subst-eval (embNf A) idCR (embNf ∘ σ))))
    (trans≡β
      (≡2β (cong embNf (fund (λ α → idext  idCR (embNf (σ α))) p)))
      ((≡2β (sym (cong embNf (subst-eval A' idCR (embNf ∘ σ))))))))
  (sym≡β (soundness (subst (embNf ∘ σ) A')))

embTel : ∀{Φ Γ Δ Δ'}(q : Δ' ≡ Δ)
  → (As  : List (Δ ⊢Nf⋆ *))
  → (As' : List (Δ' ⊢⋆ *))
  → embList As ≡βL substEq (λ Δ → List (Δ ⊢⋆ *)) q As'
  → (σ : {J : Kind} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)
  → Alg.Tel Γ Δ σ As
  → Dec.Tel (embCtx Γ) Δ' (λ {J} α → (embNf (σ (substEq (_∋⋆ J) q α)))) As'

emb : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ Alg.⊢ A → embCtx Γ Dec.⊢ embNf A

embTel refl [] [] p σ x = Dec.[]
embTel refl [] (A' ∷ As') () σ x
embTel refl (A ∷ As) [] () σ x
embTel refl (A ∷ As) (A' ∷ As') (p ,, p') σ (t Alg.∷ tel) =
  Dec.conv (lemsub A A' σ p) (emb t) Dec.∷ embTel refl As As' p' σ tel

emb (Alg.` α) = Dec.` (embVar α)
emb (Alg.ƛ {A = A}{B} t) = Dec.ƛ (emb t)
emb (Alg._·_ {A = A}{B} t u) = emb t Dec.· emb u
emb (Alg.Λ {B = B} t) = Dec.Λ (emb t)
emb (Alg._·⋆_ {B = B} t A) =
    Dec.conv (emb[] A B) (emb t Dec.·⋆ embNf A)
emb (Alg.wrap A B t) = Dec.wrap
  (embNf A)
  (embNf B)
  (Dec.conv (sym≡β (soundness-μ refl A B)) (emb t))
emb (Alg.unwrap {A = A}{B} t) =
  Dec.conv (soundness-μ refl A B) (Dec.unwrap (emb t))
emb (Alg.con  {tcn = tcn} t ) = Dec.con (embTC t)
emb (Alg.builtin bn σ tel) = let
  Δ  ,, As  ,, C  = SSig.SIG bn
  Δ' ,, As' ,, C' = NSig.SIG bn
  in Dec.conv
       (lemσ' bn refl C C' (nfTypeSIG≡₁ bn) σ (nfTypeSIG≡₂ bn))
       (Dec.builtin
         bn
         (embNf ∘ σ ∘ substEq (_∋⋆ _) (nfTypeSIG≡₁ bn))
         (embTel (nfTypeSIG≡₁ bn) As' As (lemList' bn) σ tel))
emb (Alg.ibuiltin b) = ?
emb (Alg.error A) = Dec.error (embNf A)

soundnessT : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ Alg.⊢ A → embCtx Γ Dec.⊢ embNf A
soundnessT = emb
\end{code}
