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
open import Algorithmic.Completeness

open import Function
\end{code}

\begin{code}
embCtx : Alg.Ctx → Dec.Ctx
embCtx∥ : ∀ Γ → Alg.∥ Γ ∥ ≡ Dec.∥ embCtx Γ ∥

embCtx Alg.∅       = Dec.∅
embCtx (Γ Alg.,⋆ K) = embCtx Γ Dec.,⋆ K
embCtx (Γ Alg., A)  = embCtx Γ Dec., substEq (_⊢⋆ _) (embCtx∥ Γ) (embNf A)

embCtx∥ Alg.∅       = refl
embCtx∥ (Γ Alg.,⋆ K) = cong (_,⋆ K) (embCtx∥ Γ)
embCtx∥ (Γ Alg., A)  = embCtx∥ Γ
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
subst∋' : ∀ {Γ Γ' K}{A : Dec.∥ Γ ∥ ⊢⋆ K}{A' : Dec.∥ Γ' ∥ ⊢⋆ K}
 → (p : Γ ≡ Γ')
 → substEq (_⊢⋆ K) (cong Dec.∥_∥ p) A ≡ A' →
 (Γ Dec.∋ A) → Γ' Dec.∋ A'
subst∋' refl refl α = α
\end{code}

\begin{code}
embVar : ∀{Γ K}{A : Alg.∥ Γ ∥ ⊢Nf⋆ K}
  → Γ Alg.∋ A
  → embCtx Γ Dec.∋ substEq (_⊢⋆ K) (embCtx∥ Γ) (embNf A)
embVar Alg.Z     = Dec.Z
embVar (Alg.S α) = Dec.S (embVar α)
embVar {Γ Alg.,⋆ K} (Alg.T {A = A} α) = subst∋'
  refl
  (lemT' A (embCtx∥ Γ) (embCtx∥ (Γ Alg.,⋆ K)))
  (Dec.T (embVar α))
\end{code}

\begin{code}
subst⊢' : ∀ {Γ Γ' K}{A : Dec.∥ Γ ∥ ⊢⋆ K}{A' : Dec.∥ Γ' ∥ ⊢⋆ K}
 → (p : Γ ≡ Γ')
 → substEq (_⊢⋆ K) (cong Dec.∥_∥ p) A ≡ A' →
 (Γ Dec.⊢ A) → Γ' Dec.⊢ A'
subst⊢' refl refl α = α
\end{code}

\begin{code}
lemƛ' : ∀{Γ Γ'}(A B : Γ ⊢Nf⋆ *) →
      (p : Γ ≡ Γ') → 
      substEq (_⊢⋆ *) p (embNf A ⇒ embNf B)
      ≡
      substEq (_⊢⋆ *) p (embNf A) ⇒ substEq (_⊢⋆ *) p (embNf B)
lemƛ' A B refl = refl
\end{code}

\begin{code}
lemΠ' :  ∀{Γ Γ' K }(p : Γ ≡ Γ')(q : Γ ,⋆ K ≡ Γ' ,⋆ K)(B : Γ ,⋆ K ⊢Nf⋆ *) → 
  Π (substEq (_⊢⋆ *) q (embNf B)) ≡
  substEq (_⊢⋆ *) p (Π (embNf B))
lemΠ' refl refl B = refl
\end{code}

\begin{code}
lem[]'' : ∀{Γ Γ' K}
  → (p : Γ ≡ Γ')
  → (q : Γ ,⋆ K ≡ Γ' ,⋆ K)
  → (A : Γ ⊢Nf⋆ K)
  → (B : Γ ,⋆ K ⊢Nf⋆ *) →
  (((substEq (_⊢⋆ *) q (embNf B)) [ (substEq (_⊢⋆ K) p (embNf A)) ])
  ≡β
  substEq (_⊢⋆ *) p
  (embNf
   (eval
    (subst
     (λ x →
        embNf
        (substNf-cons
         (λ {K₁} x₁ → ne (` x₁)) A x))
     (embNf B))
    (idEnv Γ))))
lem[]'' refl refl A B = substEq
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
lemμ'' : ∀{Γ Γ' K}(p : Γ ≡ Γ')(pat : Γ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)(arg : Γ ⊢Nf⋆ K) → 
  substEq (_⊢⋆ *) p (μ1 · embNf pat · embNf arg) ≡
  μ1 · substEq (_⊢⋆ _) p (embNf pat) · substEq (_⊢⋆ _) p (embNf arg)
lemμ'' refl pat arg = refl
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
open import Builtin.Constant.Type

lemcon' : ∀{Γ Γ'}(p : Γ ≡ Γ')(tcn : TyCon)(s : Γ ⊢Nf⋆ #)
  → con tcn (substEq (_⊢⋆ #) p (embNf s)) ≡
    substEq (_⊢⋆ *) p (con tcn (embNf s))
lemcon' refl tcn s = refl
\end{code}

\begin{code}
import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * # _∋⋆_ Z S _⊢⋆_ ` con boolean size⋆
  as SSig
import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * # _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf size⋆
  as NSig
open import Builtin
import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆ as STermCon 
import Builtin.Constant.Term Ctx⋆ Kind * # _⊢Nf⋆_ con size⋆ as NTermCon 


substTC' : ∀{Γ Γ'}(p : Γ ≡ Γ')(s : Γ ⊢⋆ #)(tcn : TyCon)
  → STermCon.TermCon (con tcn s)
  → STermCon.TermCon (con tcn (substEq (_⊢⋆ #) p s))
substTC' refl s tcn t = t

embTC : ∀{φ}{A : φ ⊢Nf⋆ *}
  → NTermCon.TermCon A
  → STermCon.TermCon (embNf A)
embTC (NTermCon.integer s i p)    = STermCon.integer s i p
embTC (NTermCon.bytestring s b p) = STermCon.bytestring s b p 
embTC (NTermCon.size s)           = STermCon.size s
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

embList : ∀{Δ} → List (Δ ⊢Nf⋆ *) → List (Δ ⊢⋆ *)
embList []       = []
embList (A ∷ As) = embNf A ∷ embList As

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
lemList' resizeInteger = refl≡β _ ,, refl≡β _ ,, _
lemList' sizeOfInteger = refl≡β _ ,, _
lemList' intToByteString = refl≡β _ ,, refl≡β _ ,, _
lemList' concatenate = refl≡β _ ,, refl≡β _ ,, _
lemList' takeByteString = refl≡β _ ,, refl≡β _ ,, _
lemList' dropByteString = refl≡β _ ,, refl≡β _ ,, _
lemList' sha2-256 = refl≡β _ ,, _
lemList' sha3-256 = refl≡β _ ,, _
lemList' verifySignature = refl≡β _ ,, refl≡β _ ,, refl≡β _ ,, _
lemList' resizeByteString = refl≡β _ ,, refl≡β _ ,, _
lemList' equalsByteString = refl≡β _ ,, refl≡β _ ,, _

lemsub : ∀{Γ Γ' Δ}(A : Δ ⊢Nf⋆ *)(A' : Δ ⊢⋆ *)(p : Γ ≡ Γ')
  → (σ : {J : Kind} → Δ ∋⋆ J → Γ ⊢Nf⋆ J)
  → embNf A ≡β A' → 
  substEq (_⊢⋆ *) p (embNf (substNf σ A)) ≡β
  subst (λ {J} α → substEq (_⊢⋆ J) p (embNf (σ α))) A'
lemsub A A' refl σ p = trans≡β
  (trans≡β
    (≡2≡β (cong embNf (subst-eval (embNf A) idCR (embNf ∘ σ))))
    (trans≡β
      (≡2≡β (cong embNf (fund (λ α → idext  idCR (embNf (σ α))) p)))
      ((≡2≡β (sym (cong embNf (subst-eval A' idCR (embNf ∘ σ))))))))
  (sym≡β (soundness (subst (embNf ∘ σ) A')))

embTel : ∀{Γ Δ Δ'}(q : Δ' ≡ Δ)
  → (As  : List (Δ ⊢Nf⋆ *))
  → (As' : List (Δ' ⊢⋆ *))
  → embList As ≡βL substEq (λ Δ → List (Δ ⊢⋆ *)) q As'
  → (σ : {J : Kind} → Δ ∋⋆ J → Alg.∥ Γ ∥ ⊢Nf⋆ J)
  → Alg.Tel Γ Δ σ As
  → Dec.Tel (embCtx Γ) Δ'
      (λ {J} α →
         substEq (_⊢⋆ J) (embCtx∥ Γ)
         (embNf (σ (substEq (_∋⋆ J) q α))))
      As'

emb : ∀{Γ K}{A : Alg.∥ Γ ∥ ⊢Nf⋆ K}
  → Γ Alg.⊢ A
  → embCtx Γ Dec.⊢ substEq (_⊢⋆ K) (embCtx∥ Γ) (embNf A)

embTel refl [] [] p σ x = tt
embTel refl [] (A' ∷ As') () σ x
embTel refl (A ∷ As) [] () σ x
embTel {Γ} refl (A ∷ As) (A' ∷ As') (p ,, p') σ (t ,, tel) =
  Dec.conv (lemsub A A' (embCtx∥ Γ)  σ p) (emb t)
  ,,
  embTel refl As As' p' σ tel

emb (Alg.` α) = Dec.` (embVar α)
emb {Γ} (Alg.ƛ {A = A}{B} t) =
  subst⊢' refl (sym (lemƛ' A B (embCtx∥ Γ)) ) (Dec.ƛ (emb t))
emb {Γ} (Alg._·_ {A = A}{B} t u) =
  subst⊢' refl (lemƛ' A B (embCtx∥ Γ)) (emb t) Dec.· emb u
emb {Γ} (Alg.Λ {B = B} t) =
  subst⊢' refl (lemΠ' (embCtx∥ Γ) (embCtx∥ (Γ Alg.,⋆ _)) B) (Dec.Λ (emb t))
emb {Γ}(Alg._·⋆_ {K = K}{B = B} t A) = Dec.conv
  (lem[]'' (embCtx∥ Γ) (embCtx∥ (Γ Alg.,⋆ K)) A B)
  (Dec._·⋆_
    (subst⊢' refl (sym (lemΠ' (embCtx∥ Γ) (embCtx∥ (Γ Alg.,⋆ K)) B)) (emb t))
    (substEq (_⊢⋆ K) (embCtx∥ Γ) (embNf A)))
emb {Γ} (Alg.wrap1 pat arg t) = subst⊢'
  refl
  (sym (lemμ'' (embCtx∥ Γ) pat arg))
  (Dec.wrap1
    (substEq (_⊢⋆ _) (embCtx∥ Γ) (embNf pat))
    (substEq (_⊢⋆ _) (embCtx∥ Γ) (embNf arg))
    (Dec.conv (sym≡β (lemμ''' (embCtx∥ Γ) pat arg)) (emb t)))
emb {Γ} (Alg.unwrap1 {pat = pat}{arg} t) = Dec.conv
  (lemμ'''
    (embCtx∥ Γ) pat arg)
    (Dec.unwrap1 (subst⊢' refl (lemμ'' (embCtx∥ Γ) pat arg) (emb t)))
emb {Γ} (Alg.con  {s = s}{tcn = tcn} t ) = subst⊢'
  refl
  (lemcon' (embCtx∥ Γ) tcn s)
  (Dec.con (substTC' (embCtx∥ Γ) (embNf s) tcn (embTC t)))
emb {Γ} (Alg.builtin bn σ tel) = let
  Δ  ,, As  ,, C  = SSig.SIG bn
  Δ' ,, As' ,, C' = NSig.SIG bn
  in Dec.conv
    (lemσ' bn (embCtx∥ Γ) C C' (nfTypeSIG≡₁ bn) σ (nfTypeSIG≡₂ bn))
    (Dec.builtin
      bn
      (λ {J} α → substEq
        (_⊢⋆ J)
        (embCtx∥ Γ)
        (embNf (σ (substEq (_∋⋆ J) (nfTypeSIG≡₁ bn) α))))
      (embTel (nfTypeSIG≡₁ bn) As' As (lemList' bn) σ tel))
emb {Γ} (Alg.error A) = Dec.error (substEq (_⊢⋆ _) (embCtx∥ Γ) (embNf A) )

soundnessT : ∀{Γ K}{A : Alg.∥ Γ ∥ ⊢Nf⋆ K}
  → Γ Alg.⊢ A
  → embCtx Γ Dec.⊢ substEq (_⊢⋆ K) (embCtx∥ Γ) (embNf A)
soundnessT = emb
\end{code}
