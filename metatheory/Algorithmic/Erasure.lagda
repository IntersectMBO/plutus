\begin{code}
module Algorithmic.Erasure where
\end{code}

\begin{code}
open import Algorithmic as A
open import Untyped
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Type
open import Function hiding (_∋_)
open import Builtin
import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con as DC renaming (TermCon to TyTermCon)
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as AC renaming (TermCon to TyTermCon)
import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con boolean as DS
import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf as AS


open import Data.Nat
open import Data.Fin
open import Data.List
\end{code}

\begin{code}
len : ∀{Φ} → Ctx Φ → ℕ
len ∅ = 0
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = suc (len Γ)
\end{code}

\begin{code}
eraseVar : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K} → Γ ∋ A → Fin (len Γ)
eraseVar Z     = zero
eraseVar (S α) = suc (eraseVar α) 
eraseVar (T α) = eraseVar α

eraseTC : ∀{Φ}{A : Φ ⊢Nf⋆ *} → AC.TyTermCon A → TermCon
eraseTC (AC.integer i)    = integer i
eraseTC (AC.bytestring b) = bytestring b

open import Type.BetaNBE.RenamingSubstitution

eraseTel : ∀{Φ Γ Δ}{σ : SubNf Δ Φ}{As : List (Δ ⊢Nf⋆ *)}
  → Tel Γ Δ σ As
  → List (len Γ ⊢)
erase : ∀{Φ Γ K}{A : Φ ⊢Nf⋆ K} → Γ ⊢ A → len Γ ⊢

erase (` α)             = ` (eraseVar α)
erase (ƛ t)             = ƛ (erase t) 
erase (t · u)           = erase t · erase u
erase (Λ t)             = erase t
erase (t ·⋆ A)          = erase t
erase (wrap1 pat arg t) = erase t
erase (unwrap1 t)       = erase t
erase {Γ} (con t)       = con (eraseTC {Γ} t)
erase (builtin bn σ ts) = builtin bn (eraseTel ts)
erase (error A)         = error

open import Data.Product renaming (_,_ to _,,_)

eraseTel {As = []}     _          = []
eraseTel {As = x ∷ As} (t ,, tel) = erase t ∷ eraseTel tel
\end{code}

Porting this from declarative required basically deleting one line but
I don't think I can fully exploit this by parameterizing the module as
I need to pattern match on the term constructors

# Erasing decl/alg terms agree

\begin{code}
open import Relation.Binary.PropositionalEquality
import Declarative as D
import Declarative.Erasure as D
open import Algorithmic.Completeness

lenLemma : ∀ {Φ}(Γ : D.Ctx Φ) → len (nfCtx Γ) ≡ D.len Γ
lenLemma D.∅        = refl
lenLemma (Γ D.,⋆ J) = lenLemma Γ
lenLemma (Γ D., A)  = cong suc (lenLemma Γ)

-- these lemmas for each clause of eraseVar and erase below could be
-- avoided by using with but it would involve doing with on a long
-- string of arguments, both contexts, equality proof above, and
-- before and after versions of all arguments and all recursive calls

lemzero : ∀{n n'}(p : suc n ≡ suc n') → zero ≡ subst Fin p zero
lemzero refl = refl

lemsuc : ∀{n n'}(p : suc n ≡ suc n')(q : n ≡ n')(i : Fin n) →
  suc (subst Fin q i) ≡ subst Fin p (suc i)
lemsuc refl refl i = refl

lemT : ∀{Φ J K}{Γ : Ctx Φ}{A A' : Φ ⊢Nf⋆ J}{A'' : Φ ,⋆ K ⊢Nf⋆ J}
  → (p : weakenNf {K = K} A ≡ A'')(q : A ≡ A')(x : Γ ∋ A)
  → eraseVar x ≡ eraseVar (conv∋ p (T x))
lemT refl refl x = refl

open import Function

sameTC : ∀{Φ Γ}{A : Φ ⊢⋆ *}(tcn : DC.TyTermCon A)
  → D.eraseTC {Γ = Γ} tcn ≡ eraseTC (nfTypeTC tcn)
sameTC (DC.integer i)    = refl
sameTC (DC.bytestring b) = refl

sameVar : ∀{Φ Γ J}{A : Φ ⊢⋆ J}(x : Γ D.∋ A)
  → D.eraseVar x ≡ subst Fin (lenLemma Γ) (eraseVar (nfTyVar x))
sameVar {Γ = Γ D., _} D.Z = lemzero (cong suc (lenLemma Γ))
sameVar {Γ = Γ D., _} (D.S x) = trans
  (cong suc (sameVar x))
  (lemsuc (cong suc (lenLemma Γ)) (lenLemma Γ) (eraseVar (nfTyVar x)))
sameVar {Γ = Γ D.,⋆ _} (D.T {A = A} x) = trans
  (sameVar x)
  (cong (subst Fin (lenLemma Γ)) (lemT (rename-nf S A) refl (nfTyVar x)))

lemVar : ∀{n n'}(p : n ≡ n')(i : Fin n) →  ` (subst Fin p i) ≡ subst _⊢ p (` i)
lemVar refl i = refl

lemƛ : ∀{n n'}(p : n ≡ n')(q : suc n ≡ suc n')(t : suc n ⊢)
  → ƛ (subst _⊢ q t) ≡ subst _⊢ p (ƛ t)  
lemƛ refl refl t = refl

lem· : ∀{n n'}(p : n ≡ n')(t u : n ⊢) → subst _⊢ p t · subst _⊢ p u ≡ subst _⊢ p (t · u)
lem· refl t u = refl

lem-erase : ∀{Φ Γ}{A A' : Φ ⊢Nf⋆ *}(p : A ≡ A')(t : Γ A.⊢ A)
  → erase t ≡ erase (subst⊢ p t)
lem-erase refl t = refl

lem[]' : ∀{n n'}(p : n ≡ n') →
  [] ≡ subst (List ∘ _⊢) p []
lem[]' refl = refl

lem∷ : ∀{n n'}(p : n ≡ n')(t : n ⊢)(ts : List (n ⊢))
  → subst _⊢ p t ∷ subst (List ∘ _⊢) p ts ≡ subst (List ∘ _⊢) p (t ∷ ts) 
lem∷ refl t ts = refl

lemcon' : ∀{n n'}(p : n ≡ n')(tcn : TermCon) → con tcn ≡ subst _⊢ p (con tcn)
lemcon' refl tcn = refl

lemerror : ∀{n n'}(p : n ≡ n') →  error ≡ subst _⊢ p error
lemerror refl = refl

open import Type.RenamingSubstitution renaming (subst to sub)
open import Type.Equality
open import Type.BetaNBE.Soundness

same : ∀{Φ Γ J}{A : Φ ⊢⋆ J}(t : Γ D.⊢ A)
  → D.erase t ≡ subst _⊢ (lenLemma Γ) (erase (nfType t)) 

sameTel : ∀{Φ Γ Δ}(σ : Sub Δ Φ)(As : List (Δ ⊢⋆ *))(tel : D.Tel Γ Δ σ As)
  → D.eraseTel tel
    ≡
    subst (List ∘ _⊢) (lenLemma Γ) (eraseTel (nfTypeTel σ As tel)) 
sameTel {Γ = Γ} σ [] tel = lem[]' (lenLemma Γ)
-- if the proof in nfTypeTel was pulled out as a lemma this would be shorter
sameTel {Γ = Γ} σ (A ∷ As) (t ,, ts) = trans (cong₂ _∷_ (trans (same t) (cong (subst _⊢ (lenLemma Γ)) (lem-erase (sym (trans (trans (subst-eval (embNf (nf A)) idCR (embNf ∘ nf ∘ σ)) (fund (λ α → fund idCR (sym≡β (soundness (σ α)))) (sym≡β (soundness A)))) (sym (subst-eval A idCR σ)))) (nfType t)))) (sameTel σ As ts)) (lem∷ (lenLemma Γ) (erase (subst⊢ (sym (trans (trans (subst-eval (embNf (nf A)) idCR (embNf ∘ nf ∘ σ)) (fund (λ α → fund idCR (sym≡β (soundness (σ α)))) (sym≡β (soundness A)))) (sym (subst-eval A idCR σ)))) (nfType t))) (eraseTel (nfTypeTel σ As ts)))

open import Data.Unit

lemTel : ∀{n n'}(p : n ≡ n')(bn : Builtin)(ts : List (n ⊢))
  → builtin bn (subst (List ∘ _⊢) p ts) ≡ subst _⊢ p (builtin bn ts)
lemTel refl bn ts = refl


same {Γ = Γ}(D.` x) =
  trans (cong ` (sameVar x)) (lemVar (lenLemma Γ) (eraseVar (nfTyVar x)))
same {Γ = Γ} (D.ƛ t) = trans
  (cong ƛ (same t))
  (lemƛ (lenLemma Γ) (cong suc (lenLemma Γ)) (erase (nfType t)))
same {Γ = Γ} (t D.· u) = trans
  (cong₂ _·_ (same t) (same u))
  (lem· (lenLemma Γ) (erase (nfType t)) (erase (nfType u)))
same {Γ = Γ} (D.Λ {B = B} t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase (substNf-lemma' B) (nfType t)))
same {Γ = Γ} (D._·⋆_ {B = B} t A) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ))
        (trans (lem-erase (lemΠ B) (nfType t))
               (lem-erase (lem[] A B) (subst⊢ (lemΠ B) (nfType t) ·⋆ nf A))))
same {Γ = Γ} (D.wrap1 pat arg t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase (lemXX pat arg) (nfType t)))
same {Γ = Γ} (D.unwrap1 {pat = pat}{arg} t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ))
        (lem-erase (sym (lemXX pat arg)) (unwrap1 (nfType t))))
same {Γ = Γ} (D.conv p t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase (completeness p) (nfType t)))
same {Γ = Γ} (D.con tcn) = trans
  (cong con (sameTC {Γ = Γ} tcn))
  (lemcon' (lenLemma Γ) (eraseTC (nfTypeTC tcn)))
same {Γ = Γ} (D.builtin addInteger σ ts) = trans (cong (builtin addInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG addInteger))) ts)) (lemTel (lenLemma Γ) addInteger _)
same {Γ = Γ} (D.builtin subtractInteger σ ts) = trans (cong (builtin subtractInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG subtractInteger))) ts)) (lemTel (lenLemma Γ) subtractInteger _)
same {Γ = Γ} (D.builtin multiplyInteger σ ts) = trans (cong (builtin multiplyInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG multiplyInteger))) ts)) (lemTel (lenLemma Γ) multiplyInteger _)
same {Γ = Γ} (D.builtin divideInteger σ ts) = trans (cong (builtin divideInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG divideInteger))) ts)) (lemTel (lenLemma Γ) divideInteger _)
same {Γ = Γ} (D.builtin quotientInteger σ ts) = trans (cong (builtin quotientInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG quotientInteger))) ts)) (lemTel (lenLemma Γ) quotientInteger _)
same {Γ = Γ} (D.builtin remainderInteger σ ts) = trans (cong (builtin remainderInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG remainderInteger))) ts)) (lemTel (lenLemma Γ) remainderInteger _)
same {Γ = Γ} (D.builtin modInteger σ ts) = trans (cong (builtin modInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG modInteger))) ts)) (lemTel (lenLemma Γ) modInteger _)
same {Γ = Γ} (D.builtin lessThanInteger σ ts) = trans (cong (builtin lessThanInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG lessThanInteger))) ts)) (lemTel (lenLemma Γ) lessThanInteger _)
same {Γ = Γ} (D.builtin lessThanEqualsInteger σ ts) = trans (cong (builtin lessThanEqualsInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG lessThanEqualsInteger))) ts)) (lemTel (lenLemma Γ) lessThanEqualsInteger _)
same {Γ = Γ} (D.builtin greaterThanInteger σ ts) = trans (cong (builtin greaterThanInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG greaterThanInteger))) ts)) (lemTel (lenLemma Γ) greaterThanInteger _)
same {Γ = Γ} (D.builtin greaterThanEqualsInteger σ ts) = trans (cong (builtin greaterThanEqualsInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG greaterThanEqualsInteger))) ts)) (lemTel (lenLemma Γ) greaterThanEqualsInteger _)
same {Γ = Γ} (D.builtin equalsInteger σ ts) = trans (cong (builtin equalsInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG equalsInteger))) ts)) (lemTel (lenLemma Γ) equalsInteger _)
same {Γ = Γ} (D.builtin concatenate σ ts) = trans (cong (builtin concatenate) (sameTel σ (proj₁ (proj₂ (DS.SIG concatenate))) ts)) (lemTel (lenLemma Γ) concatenate _)
same {Γ = Γ} (D.builtin takeByteString σ ts) = trans (cong (builtin takeByteString) (sameTel σ (proj₁ (proj₂ (DS.SIG takeByteString))) ts)) (lemTel (lenLemma Γ) takeByteString _)
same {Γ = Γ} (D.builtin dropByteString σ ts) = trans (cong (builtin dropByteString) (sameTel σ (proj₁ (proj₂ (DS.SIG dropByteString))) ts)) (lemTel (lenLemma Γ) dropByteString _)
same {Γ = Γ} (D.builtin sha2-256 σ ts) = trans (cong (builtin sha2-256) (sameTel σ (proj₁ (proj₂ (DS.SIG sha2-256))) ts)) (lemTel (lenLemma Γ) sha2-256 _)
same {Γ = Γ} (D.builtin sha3-256 σ ts) = trans (cong (builtin sha3-256) (sameTel σ (proj₁ (proj₂ (DS.SIG sha3-256))) ts)) (lemTel (lenLemma Γ) sha3-256 _)
same {Γ = Γ} (D.builtin verifySignature σ ts) = trans (cong (builtin verifySignature) (sameTel σ (proj₁ (proj₂ (DS.SIG verifySignature))) ts)) (lemTel (lenLemma Γ) verifySignature _)
same {Γ = Γ} (D.builtin equalsByteString σ ts) = trans (cong (builtin equalsByteString) (sameTel σ (proj₁ (proj₂ (DS.SIG equalsByteString))) ts)) (lemTel (lenLemma Γ) equalsByteString _)
same {Γ = Γ} (D.error A) = lemerror (lenLemma Γ)
\end{code}
