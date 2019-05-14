\begin{code}
module Algorithmic.Soundness where

open import Type
open import Type.RenamingSubstitution
import Declarative as Dec
import Algorithmic as Alg
open import Type.BetaNormal
open import Type.Equality
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Type.BetaNBE.Soundness
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) hiding ([_])

open import Function
\end{code}

\begin{code}
embCtx : ∀{Φ} → Alg.Ctx Φ → Dec.Ctx Φ
--embCtx∥ : ∀ Γ → Alg.∥ Γ ∥ ≡ Dec.∥ embCtx Γ ∥

embCtx Alg.∅       = Dec.∅
embCtx (Γ Alg.,⋆ K) = embCtx Γ Dec.,⋆ K
embCtx (Γ Alg., A)  = embCtx Γ Dec., embNf A
\end{code}

\begin{code}
lemT' : ∀{Γ Γ' J K}(A :  Γ ⊢Nf⋆ K)
 → (p : Γ ≡ Γ')
 → (q : Γ ,⋆ J ≡ Γ' ,⋆ J)
  → weaken (substEq (_⊢⋆ K) p (embNf A))
    ≡
    substEq (_⊢⋆ K) q (embNf (renameNf S A))
lemT' A refl refl = sym (rename-embNf S A)
\end{code}

\begin{code}
conv∋ : ∀ {Φ Γ K}{A : Φ ⊢⋆ K}{A' : Φ ⊢⋆ K}
 → A ≡ A' →
 (Γ Dec.∋ A) → Γ Dec.∋ A'
conv∋ refl α = α
\end{code}

\begin{code}
embVar : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K}
  → Γ Alg.∋ A
  → embCtx Γ Dec.∋ embNf A
embVar Alg.Z     = Dec.Z
embVar (Alg.S α) = Dec.S (embVar α)
embVar {Γ = Γ Alg.,⋆ K} (Alg.T {A = A} α) =
  conv∋ (sym (rename-embNf S A)) (Dec.T (embVar α))
\end{code}

\begin{code}
conv⊢ : ∀ {Φ Γ K}{A : Φ ⊢⋆ K}{A' : Φ ⊢⋆ K}
 → A ≡ A' →
 (Γ Dec.⊢ A) → Γ Dec.⊢ A'
conv⊢ refl α = α
\end{code}

\begin{code}
lem[]'' : ∀{Γ K}(A : Γ ⊢Nf⋆ K)(B : Γ ,⋆ K ⊢Nf⋆ *) →
  embNf B [ embNf A ] ≡β embNf (B [ A ]Nf)
lem[]'' A B = substEq
  (embNf B [ embNf A ] ≡β_)
  (cong
    embNf
    (trans
      (trans
        (subst-eval (embNf B) idCR (subst-cons ` (embNf A)))
        (idext (λ { Z → idext idCR (embNf A)
                  ; (S α) → reflectCR (refl {x = ` α})}) (embNf B)))
      (sym (subst-eval (embNf B) idCR (embNf ∘ substNf-cons (ne ∘ `) A)))))
  (soundness (embNf B [ embNf A ]))
\end{code}

\begin{code}
open import Data.Sum
lemμ''' : ∀{Γ Γ' K}(p : Γ ≡ Γ')(pat : Γ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)(arg : Γ ⊢Nf⋆ K) →
  substEq (_⊢⋆ (K ⇒ *) ⇒ K ⇒ *) p (embNf pat) ·
  (μ1 · substEq (_⊢⋆ (K ⇒ *) ⇒ K ⇒ *) p (embNf pat))
  · substEq (_⊢⋆ K) p (embNf arg)
  ≡β
  substEq (_⊢⋆ *) p
  (embNf
   ((eval (embNf pat) (idEnv Γ) ·V
     inj₁
     (μ1 · reify (eval (embNf pat) (idEnv Γ))))
    ·V eval (embNf arg) (idEnv Γ)))
lemμ''' refl pat arg = soundness (embNf pat · (μ1 · embNf pat) · embNf arg)
\end{code}

\begin{code}
import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con boolean
  as SSig
import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf
  as NSig
open import Builtin
import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con as STermCon
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as NTermCon

embTC : ∀{φ}{A : φ ⊢Nf⋆ *}
  → NTermCon.TermCon A
  → STermCon.TermCon (embNf A)
embTC (NTermCon.integer i)    = STermCon.integer i
embTC (NTermCon.bytestring b) = STermCon.bytestring b
\end{code}

\begin{code}
open import Data.Product renaming (_,_ to _,,_)
open import Data.List

open import Type.Equality

≡2≡β : ∀{Γ K}{A A' : Γ ⊢⋆ K} → A ≡ A' → A ≡β A'
≡2≡β refl = refl≡β _

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
lemσ' bn refl C C' refl σ refl = trans≡β
  (soundness (subst (embNf ∘ σ) C))
  (trans≡β
    (≡2≡β (cong embNf (subst-eval C idCR (embNf ∘ σ))))
    (trans≡β
      (≡2≡β (cong embNf (fund (λ α → idext  idCR (embNf (σ α))) (soundness C))))
      (≡2≡β (sym (cong embNf (subst-eval (embNf (nf C)) idCR (embNf ∘ σ)))))))

open import Data.Unit
open import Data.Empty

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

lemsub : ∀{Γ Δ}(A : Δ ⊢Nf⋆ *)(A' : Δ ⊢⋆ *)
  → (σ : {J : Kind} → Δ ∋⋆ J → Γ ⊢Nf⋆ J)
  → embNf A ≡β A' →
  (embNf (substNf σ A)) ≡β
  subst (λ {J} α → embNf (σ α)) A'
lemsub A A' σ p = trans≡β
  (trans≡β
    (≡2≡β (cong embNf (subst-eval (embNf A) idCR (embNf ∘ σ))))
    (trans≡β
      (≡2≡β (cong embNf (fund (λ α → idext  idCR (embNf (σ α))) p)))
      ((≡2≡β (sym (cong embNf (subst-eval A' idCR (embNf ∘ σ))))))))
  (sym≡β (soundness (subst (embNf ∘ σ) A')))

embTel : ∀{Φ Γ Δ Δ'}(q : Δ' ≡ Δ)
  → (As  : List (Δ ⊢Nf⋆ *))
  → (As' : List (Δ' ⊢⋆ *))
  → embList As ≡βL substEq (λ Δ → List (Δ ⊢⋆ *)) q As'
  → (σ : {J : Kind} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)
  → Alg.Tel Γ Δ σ As
  → Dec.Tel (embCtx Γ) Δ' (λ {J} α → (embNf (σ (substEq (_∋⋆ J) q α)))) As'

emb : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K} → Γ Alg.⊢ A → embCtx Γ Dec.⊢ embNf A

embTel refl [] [] p σ x = tt
embTel refl [] (A' ∷ As') () σ x
embTel refl (A ∷ As) [] () σ x
embTel refl (A ∷ As) (A' ∷ As') (p ,, p') σ (t ,, tel) =
  Dec.conv (lemsub A A' σ p) (emb t) ,, embTel refl As As' p' σ tel

emb (Alg.` α) = Dec.` (embVar α)
emb (Alg.ƛ {A = A}{B} t) = Dec.ƛ (emb t)
emb (Alg._·_ {A = A}{B} t u) = emb t Dec.· emb u
emb (Alg.Λ {B = B} t) = Dec.Λ (emb t)
emb (Alg._·⋆_ {K = K}{B = B} t A) =
  Dec.conv (lem[]'' A B) (emb t Dec.·⋆ embNf A)
emb (Alg.wrap1 pat arg t) =
  Dec.wrap1
    (embNf pat)
    (embNf arg)
    (Dec.conv (sym≡β (lemμ''' refl pat arg)) (emb t))
emb (Alg.unwrap1 {pat = pat}{arg} t) =
  Dec.conv (lemμ''' refl pat arg) (Dec.unwrap1 (emb t))
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
emb (Alg.error A) = Dec.error (embNf A)

soundnessT : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K} → Γ Alg.⊢ A → embCtx Γ Dec.⊢ embNf A
soundnessT = emb
\end{code}
