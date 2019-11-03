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
eraseVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ∋ A → Fin (len Γ)
eraseVar (Z p)   = zero
eraseVar (S α)   = suc (eraseVar α) 
eraseVar (T α p) = eraseVar α

eraseTC : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *} → AC.TyTermCon A → TermCon
eraseTC (AC.integer i)    = integer i
eraseTC (AC.bytestring b) = bytestring b
eraseTC (AC.string s)     = string s

open import Type.BetaNBE.RenamingSubstitution

eraseTel : ∀{Φ Γ Δ}{σ : SubNf Δ Φ}{As : List (Δ ⊢Nf⋆ *)}
  → A.Tel Γ Δ σ As
  → Untyped.Tel (len Γ)
erase : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢ A → len Γ ⊢
erase (` α)               = ` (eraseVar α)
erase (ƛ x t)             = ƛ x (erase t) 
erase (t · u)             = erase t · erase u
erase (Λ x t)             = erase t
erase (·⋆ t A p)          = erase t
erase (wrap1 pat arg t)   = erase t
erase (unwrap1 t p)       = erase t
erase {Γ = Γ} (con t)     = con (eraseTC {Γ = Γ} t)
erase (builtin bn σ ts p) = builtin bn (eraseTel ts)
erase (error A)           = error

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

open import Type.BetaNormal.Equality
open import Function

sameTC : ∀{Φ Γ}{A : Φ ⊢⋆ *}(tcn : DC.TyTermCon A)
  → D.eraseTC {Γ = Γ} tcn ≡ eraseTC {Γ = nfCtx Γ} (nfTypeTC tcn)
sameTC (DC.integer i)    = refl
sameTC (DC.bytestring b) = refl
sameTC (DC.string s)     = refl

sameVar : ∀{Φ Γ}{A : Φ ⊢⋆ *}(x : Γ D.∋ A)
  → D.eraseVar x ≡ subst Fin (lenLemma Γ) (eraseVar (nfTyVar x))
sameVar {Γ = Γ D., _} (D.Z p) = lemzero (cong suc (lenLemma Γ))
sameVar {Γ = Γ D., _} (D.S x) = trans
  (cong suc (sameVar x))
  (lemsuc (cong suc (lenLemma Γ)) (lenLemma Γ) (eraseVar (nfTyVar x)))
sameVar {Γ = Γ D.,⋆ _} (D.T {A = A} x p) = sameVar x

lemVar : ∀{n n'}(p : n ≡ n')(i : Fin n) →  ` (subst Fin p i) ≡ subst _⊢ p (` i)
lemVar refl i = refl

lemƛ : ∀{n n'}{x}(p : n ≡ n')(q : suc n ≡ suc n')(t : suc n ⊢)
  → ƛ x (subst _⊢ q t) ≡ subst _⊢ p (ƛ x t)  
lemƛ refl refl t = refl

lem· : ∀{n n'}(p : n ≡ n')(t u : n ⊢) → subst _⊢ p t · subst _⊢ p u ≡ subst _⊢ p (t · u)
lem· refl t u = refl

lemcon' : ∀{n n'}(p : n ≡ n')(tcn : TermCon) → con tcn ≡ subst _⊢ p (con tcn)
lemcon' refl tcn = refl

lemerror : ∀{n n'}(p : n ≡ n') →  error ≡ subst _⊢ p error
lemerror refl = refl

lem≡Ctx : ∀{Φ}{Γ Γ' : Ctx Φ} → Γ ≡Ctx Γ' → len Γ ≡ len Γ'
lem≡Ctx ∅        = refl
lem≡Ctx (p ,⋆ K) = lem≡Ctx p
lem≡Ctx (p , p') = cong suc (lem≡Ctx p)

lem[]' : ∀{n n'}(p : n ≡ n') →
  [] ≡ subst (List ∘ _⊢) p []
lem[]' refl = refl

lem∷ : ∀{n n'}(p : n ≡ n')(t : n ⊢)(ts : List (n ⊢))
  → subst _⊢ p t ∷ subst (List ∘ _⊢) p ts ≡ subst (List ∘ _⊢) p (t ∷ ts) 
lem∷ refl t ts = refl

lemTel : ∀{n n'}(p : n ≡ n')(bn : Builtin)(ts : List (n ⊢))
  → builtin bn (subst (List ∘ _⊢) p ts) ≡ subst _⊢ p (builtin bn ts)
lemTel refl bn ts = refl

lem-convTel : ∀{Φ Γ Γ' Δ}(As : List (Δ ⊢Nf⋆ *))(p : Γ ≡Ctx Γ')
  → (σ : ∀{J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)
  → (tel : A.Tel Γ Δ σ As)
  → subst (List ∘ _⊢) (lem≡Ctx p) (eraseTel tel)
    ≡ eraseTel (convTel p σ As tel)

lem-conv∋ : ∀{Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}(p : Γ ≡Ctx Γ')(q : A ≡Nf A')(x : Γ A.∋ A)
  → subst Fin (lem≡Ctx p) (eraseVar x)  ≡ eraseVar (conv∋ p q x)
lem-conv∋ (p , p') q (Z r) = sym (lemzero (cong suc (lem≡Ctx p)))
lem-conv∋ (p , p') q (S x) = trans
  (sym (lemsuc (cong suc (lem≡Ctx p)) (lem≡Ctx p) (eraseVar x)))
  (cong suc (lem-conv∋ p q x))
lem-conv∋ (p ,⋆ K) q (T x r) = lem-conv∋ p reflNf x

lem-erase : ∀{Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}(p : Γ ≡Ctx Γ')(q : A ≡Nf A')(t : Γ A.⊢ A)
  → subst _⊢ (lem≡Ctx p) (erase t)  ≡ erase (conv⊢ p q t)
lem-erase p q (` x) = trans
  (sym (lemVar (lem≡Ctx p) (eraseVar x)))
  (cong ` (lem-conv∋ p q x))
lem-erase p (⇒≡Nf q q') (ƛ x t) = trans
  (sym (lemƛ (lem≡Ctx p) (lem≡Ctx (p , q)) (erase t)))
  (cong (ƛ x) (lem-erase (p , q) q' t))
lem-erase p q (t · u) = trans
  (sym (lem· (lem≡Ctx p) (erase t) (erase u)))
  (cong₂ _·_ (lem-erase p (⇒≡Nf reflNf q) t) (lem-erase p reflNf u))
lem-erase p (Π≡Nf q) (Λ x t) = lem-erase (p ,⋆ _) q t
lem-erase p q (·⋆ t A x) = lem-erase p reflNf t
lem-erase p (ne≡Nf (·≡Ne (·≡Ne μ≡Ne q) q')) (wrap1 pat arg t) = lem-erase p _ t
lem-erase p q (unwrap1 t x) = lem-erase p _ t
lem-erase p con≡Nf (con c) = sym (lemcon' (lem≡Ctx p) _)
lem-erase p q (builtin bn σ tel r) = trans
  (sym (lemTel (lem≡Ctx p) bn (eraseTel tel)))
  (cong (builtin bn) (lem-convTel _ p σ tel))
lem-erase p q (error A) = sym (lemerror (lem≡Ctx p))

lem-convTel []       p σ _         = sym (lem[]' (lem≡Ctx p))
lem-convTel (A ∷ As) p σ (t ,, ts) = trans
  (sym (lem∷ (lem≡Ctx p) (erase t) (eraseTel ts)))
  (cong₂ _∷_ (lem-erase p reflNf t) (lem-convTel As p σ ts))

lem-subst : ∀{n}(t : n ⊢)(p : n ≡ n) → subst _⊢ p t ≡ t
lem-subst t refl = refl

lem-erase' : ∀{Φ Γ}{A A' : Φ ⊢Nf⋆ *}(q : A ≡Nf A')(t : Γ A.⊢ A)
  → erase t  ≡ erase (conv⊢ reflCtx q t)
lem-erase' {Γ = Γ} p t = trans
  (sym (lem-subst (erase t) (lem≡Ctx {Γ = Γ} reflCtx)))
  (lem-erase reflCtx p t)

open import Type.RenamingSubstitution renaming (subst to sub)
open import Type.Equality
open import Type.BetaNBE.Soundness

same : ∀{Φ Γ}{A : Φ ⊢⋆ *}(t : Γ D.⊢ A)
  → D.erase t ≡ subst _⊢ (lenLemma Γ) (erase (nfType t)) 

sameTel : ∀{Φ Γ Δ}(σ : Sub Δ Φ)(As : List (Δ ⊢⋆ *))(tel : D.Tel Γ Δ σ As)
  → D.eraseTel tel
    ≡
    subst (List ∘ _⊢) (lenLemma Γ) (eraseTel (nfTypeTel σ As tel)) 
sameTel {Γ = Γ} σ [] tel = lem[]' (lenLemma Γ)
-- if the proof in nfTypeTel was pulled out as a lemma this would be shorter
sameTel {Γ = Γ} σ (A ∷ As) (t ,, ts) = trans (cong₂ _∷_ (trans (same t) ((cong (subst _⊢ (lenLemma Γ)) (trans (sym (lem-subst (erase (nfType t)) (lem≡Ctx {Γ = nfCtx Γ} reflCtx))) ( lem-erase reflCtx (symNf (transNf (transNf (subst-eval (embNf (nf A)) idCR (embNf ∘ nf ∘ σ)) (fund (λ α → fund idCR (sym≡β (soundness (σ α)))) (sym≡β (soundness A)))) (symNf (subst-eval A idCR σ)))) (nfType t)))))) (sameTel σ As ts))  (lem∷ _ _ _)

open import Data.Unit

same {Γ = Γ}(D.` x) =
  trans (cong ` (sameVar x)) (lemVar (lenLemma Γ) (eraseVar (nfTyVar x)))
same {Γ = Γ} (D.ƛ x t) = trans
  (cong (ƛ x) (same t))
  (lemƛ (lenLemma Γ) (cong suc (lenLemma Γ)) (erase (nfType t)))
same {Γ = Γ} (t D.· u) = trans
  (cong₂ _·_ (same t) (same u))
  (lem· (lenLemma Γ) (erase (nfType t)) (erase (nfType u)))
same {Γ = Γ} (D.Λ {B = B} x t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (substNf-lemma' B) (nfType t)))
same {Γ = Γ} (D.·⋆ {B = B} t A p) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (lemΠ B) (nfType t)))
same {Γ = Γ} (D.wrap1 pat arg t) = trans (same t) (cong (subst _⊢ (lenLemma Γ)) (lem-erase' _ (nfType t)))
same {Γ = Γ} (D.unwrap1 {pat = pat}{arg = arg} t p) = same t
same {Γ = Γ} (D.conv p t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (completeness p) (nfType t)))
same {Γ = Γ} (D.con tcn) = trans
  (cong con (sameTC {Γ = Γ} tcn))
  (lemcon' (lenLemma Γ) (eraseTC {Γ = nfCtx Γ} (nfTypeTC tcn)))
same {Γ = Γ} (D.builtin addInteger σ ts p) = trans (cong (builtin addInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG addInteger))) ts)) (lemTel (lenLemma Γ) addInteger _)
same {Γ = Γ} (D.builtin subtractInteger σ ts p) = trans (cong (builtin subtractInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG subtractInteger))) ts)) (lemTel (lenLemma Γ) subtractInteger _)
same {Γ = Γ} (D.builtin multiplyInteger σ ts p) = trans (cong (builtin multiplyInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG multiplyInteger))) ts)) (lemTel (lenLemma Γ) multiplyInteger _)
same {Γ = Γ} (D.builtin divideInteger σ ts p) = trans (cong (builtin divideInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG divideInteger))) ts)) (lemTel (lenLemma Γ) divideInteger _)
same {Γ = Γ} (D.builtin quotientInteger σ ts p) = trans (cong (builtin quotientInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG quotientInteger))) ts)) (lemTel (lenLemma Γ) quotientInteger _)
same {Γ = Γ} (D.builtin remainderInteger σ ts p) = trans (cong (builtin remainderInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG remainderInteger))) ts)) (lemTel (lenLemma Γ) remainderInteger _)
same {Γ = Γ} (D.builtin modInteger σ ts p) = trans (cong (builtin modInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG modInteger))) ts)) (lemTel (lenLemma Γ) modInteger _)
same {Γ = Γ} (D.builtin lessThanInteger σ ts p) = trans (cong (builtin lessThanInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG lessThanInteger))) ts)) (lemTel (lenLemma Γ) lessThanInteger _)
same {Γ = Γ} (D.builtin lessThanEqualsInteger σ ts p) = trans (cong (builtin lessThanEqualsInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG lessThanEqualsInteger))) ts)) (lemTel (lenLemma Γ) lessThanEqualsInteger _)
same {Γ = Γ} (D.builtin greaterThanInteger σ ts p) = trans (cong (builtin greaterThanInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG greaterThanInteger))) ts)) (lemTel (lenLemma Γ) greaterThanInteger _)
same {Γ = Γ} (D.builtin greaterThanEqualsInteger σ ts p) = trans (cong (builtin greaterThanEqualsInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG greaterThanEqualsInteger))) ts)) (lemTel (lenLemma Γ) greaterThanEqualsInteger _)
same {Γ = Γ} (D.builtin equalsInteger σ ts p) = trans (cong (builtin equalsInteger) (sameTel σ (proj₁ (proj₂ (DS.SIG equalsInteger))) ts)) (lemTel (lenLemma Γ) equalsInteger _)
same {Γ = Γ} (D.builtin concatenate σ ts p) = trans (cong (builtin concatenate) (sameTel σ (proj₁ (proj₂ (DS.SIG concatenate))) ts)) (lemTel (lenLemma Γ) concatenate _)
same {Γ = Γ} (D.builtin takeByteString σ ts p) = trans (cong (builtin takeByteString) (sameTel σ (proj₁ (proj₂ (DS.SIG takeByteString))) ts)) (lemTel (lenLemma Γ) takeByteString _)
same {Γ = Γ} (D.builtin dropByteString σ ts p) = trans (cong (builtin dropByteString) (sameTel σ (proj₁ (proj₂ (DS.SIG dropByteString))) ts)) (lemTel (lenLemma Γ) dropByteString _)
same {Γ = Γ} (D.builtin sha2-256 σ ts p) = trans (cong (builtin sha2-256) (sameTel σ (proj₁ (proj₂ (DS.SIG sha2-256))) ts)) (lemTel (lenLemma Γ) sha2-256 _)
same {Γ = Γ} (D.builtin sha3-256 σ ts p) = trans (cong (builtin sha3-256) (sameTel σ (proj₁ (proj₂ (DS.SIG sha3-256))) ts)) (lemTel (lenLemma Γ) sha3-256 _)
same {Γ = Γ} (D.builtin verifySignature σ ts p) = trans (cong (builtin verifySignature) (sameTel σ (proj₁ (proj₂ (DS.SIG verifySignature))) ts)) (lemTel (lenLemma Γ) verifySignature _)
same {Γ = Γ} (D.builtin equalsByteString σ ts p) = trans (cong (builtin equalsByteString) (sameTel σ (proj₁ (proj₂ (DS.SIG equalsByteString))) ts)) (lemTel (lenLemma Γ) equalsByteString _)
same {Γ = Γ} (D.error A) = lemerror (lenLemma Γ)


open import Algorithmic.Soundness

same'Len : ∀ {Φ}(Γ : A.Ctx Φ) → D.len (embCtx Γ) ≡ len Γ
same'Len ∅          = refl
same'Len (Γ ,⋆ J)   = same'Len Γ
same'Len (Γ , A)    = cong suc (same'Len Γ)

same'Var : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ A.∋ A)
  →  eraseVar x ≡ subst Fin (same'Len Γ) (D.eraseVar (embVar x))
same'Var {Γ = Γ , _} (Z p) = lemzero (cong suc (same'Len Γ))
same'Var {Γ = Γ , _} (S x) = trans
  (cong suc (same'Var x))
  (lemsuc (cong suc (same'Len Γ)) (same'Len Γ) (D.eraseVar (embVar x)))
same'Var {Γ = Γ ,⋆ _} (T {A = A} x p) = same'Var x

same'TC : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(tcn : AC.TyTermCon A)
  → eraseTC {Γ = Γ} tcn ≡ D.eraseTC {Φ}{Γ = embCtx Γ} (embTC tcn)
same'TC (AC.integer i)    = refl
same'TC (AC.bytestring b) = refl
same'TC (AC.string s)     = refl

same' : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ A.⊢ A)
  →  erase x ≡ subst _⊢ (same'Len Γ) (D.erase (emb x))

same'Tel : ∀{Φ Γ Δ}(σ : SubNf Δ Φ)(As : List (Δ ⊢Nf⋆ *))(tel : A.Tel Γ Δ σ As)
  → eraseTel tel
    ≡
    subst (List ∘ _⊢) (same'Len Γ) (D.eraseTel (embTel refl As (embList As) (refl≡βL (embList As)) σ tel)) 
same'Tel {Γ = Γ} σ [] tel = lem[]' (same'Len Γ)
same'Tel {Γ = Γ} σ (A ∷ As) (t ,, ts) = trans (cong₂ _∷_ (same' t) (same'Tel σ As ts)) (lem∷ (same'Len Γ) (D.erase (emb t)) (D.eraseTel (embTel refl As (embList As) (refl≡βL (embList As)) σ ts)))
same' {Γ = Γ} (` x) =
  trans (cong ` (same'Var x)) (lemVar (same'Len Γ) (D.eraseVar (embVar x)))
same' {Γ = Γ} (ƛ x t)      = trans
  (cong (ƛ x) (same' t))
  (lemƛ (same'Len Γ) (cong suc (same'Len Γ)) (D.erase (emb t)))
same' {Γ = Γ} (t · u)    = trans
  (cong₂ _·_ (same' t) (same' u))
  (lem· (same'Len Γ) (D.erase (emb t)) (D.erase (emb u)))
same' {Γ = Γ} (Λ x t)    = same' t
same' {Γ = Γ} (·⋆ t A p)   = same' t
same' {Γ = Γ} (wrap1 pat arg t)   = same' t
same' {Γ = Γ} (unwrap1 t p) = same' t
same' {Γ = Γ} (con x) = trans (cong con (same'TC {Γ = Γ} x)) (lemcon' (same'Len Γ) (D.eraseTC {Γ = embCtx Γ}(embTC x))) 
same' {Γ = Γ} (builtin addInteger σ ts p) = trans
  (cong (builtin addInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG addInteger))) ts))
  (lemTel (same'Len Γ) addInteger _)
same' {Γ = Γ} (builtin subtractInteger σ ts p) = trans
  (cong (builtin subtractInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG subtractInteger))) ts))
  (lemTel (same'Len Γ) subtractInteger _)
same' {Γ = Γ} (builtin multiplyInteger σ ts p) = trans
  (cong (builtin multiplyInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG multiplyInteger))) ts))
  (lemTel (same'Len Γ) multiplyInteger _)
same' {Γ = Γ} (builtin divideInteger σ ts p) = trans
  (cong (builtin divideInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG divideInteger))) ts))
  (lemTel (same'Len Γ) divideInteger _)
same' {Γ = Γ} (builtin quotientInteger σ ts p) = trans
  (cong (builtin quotientInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG quotientInteger))) ts))
  (lemTel (same'Len Γ) quotientInteger _)
same' {Γ = Γ} (builtin remainderInteger σ ts p) = trans
  (cong (builtin remainderInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG remainderInteger))) ts))
  (lemTel (same'Len Γ) remainderInteger _)
same' {Γ = Γ} (builtin modInteger σ ts p) = trans
  (cong (builtin modInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG modInteger))) ts))
  (lemTel (same'Len Γ) modInteger _)
same' {Γ = Γ} (builtin lessThanInteger σ ts p) = trans
  (cong (builtin lessThanInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG lessThanInteger))) ts))
  (lemTel (same'Len Γ) lessThanInteger _)
same' {Γ = Γ} (builtin lessThanEqualsInteger σ ts p) = trans
  (cong (builtin lessThanEqualsInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG lessThanEqualsInteger))) ts))
  (lemTel (same'Len Γ) lessThanEqualsInteger _)
same' {Γ = Γ} (builtin greaterThanInteger σ ts p) = trans
  (cong (builtin greaterThanInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG greaterThanInteger))) ts))
  (lemTel (same'Len Γ) greaterThanInteger _)
same' {Γ = Γ} (builtin greaterThanEqualsInteger σ ts p) = trans
  (cong (builtin greaterThanEqualsInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG greaterThanEqualsInteger))) ts))
  (lemTel (same'Len Γ) greaterThanEqualsInteger _)
same' {Γ = Γ} (builtin equalsInteger σ ts p) = trans
  (cong (builtin equalsInteger)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG equalsInteger))) ts))
  (lemTel (same'Len Γ) equalsInteger _)
same' {Γ = Γ} (builtin concatenate σ ts p) = trans
  (cong (builtin concatenate)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG concatenate))) ts))
  (lemTel (same'Len Γ) concatenate _)
same' {Γ = Γ} (builtin takeByteString σ ts p) = trans
  (cong (builtin takeByteString)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG takeByteString))) ts))
  (lemTel (same'Len Γ) takeByteString _)
same' {Γ = Γ} (builtin dropByteString σ ts p) = trans
  (cong (builtin dropByteString)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG dropByteString))) ts))
  (lemTel (same'Len Γ) dropByteString _)
same' {Γ = Γ} (builtin sha2-256 σ ts p) = trans
  (cong (builtin sha2-256)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG sha2-256))) ts))
  (lemTel (same'Len Γ) sha2-256 _)
same' {Γ = Γ} (builtin sha3-256 σ ts p) = trans
  (cong (builtin sha3-256)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG sha3-256))) ts))
  (lemTel (same'Len Γ) sha3-256 _)
same' {Γ = Γ} (builtin verifySignature σ ts p) = trans
  (cong (builtin verifySignature)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG verifySignature))) ts))
  (lemTel (same'Len Γ) verifySignature _)
same' {Γ = Γ} (builtin equalsByteString σ ts p) = trans
  (cong (builtin equalsByteString)
        (same'Tel σ (proj₁ (proj₂ (AS.SIG equalsByteString))) ts))
  (lemTel (same'Len Γ) equalsByteString _)
same' {Γ = Γ} (error A) = lemerror (same'Len Γ)
\end{code}
