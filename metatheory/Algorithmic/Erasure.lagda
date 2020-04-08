\begin{code}
module Algorithmic.Erasure where
\end{code}

\begin{code}
open import Algorithmic as A
open import Untyped
open import Untyped.RenamingSubstitution as U
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Type
open import Type.BetaNBE.RenamingSubstitution
open import Function hiding (_∋_)
open import Builtin
import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con as DC renaming (TermCon to TyTermCon)
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as AC renaming (TermCon to TyTermCon)
import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con as DS
import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con as AS
open import Type.RenamingSubstitution as T renaming (subst to sub) 
open import Type.Equality
open import Type.BetaNBE.Soundness



open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
open import Data.List
open import Data.Vec
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
\end{code}

\begin{code}
len : ∀{Φ} → Ctx Φ → ℕ
len ∅ = 0
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = suc (len Γ)

lemma : (b : Builtin) →  length (proj₁ (proj₂ (AS.SIG b))) ≡ arity b
lemma addInteger = refl
lemma subtractInteger = refl
lemma multiplyInteger = refl
lemma divideInteger = refl
lemma quotientInteger = refl
lemma remainderInteger = refl
lemma modInteger = refl
lemma lessThanInteger = refl
lemma lessThanEqualsInteger = refl
lemma greaterThanInteger = refl
lemma greaterThanEqualsInteger = refl
lemma equalsInteger = refl
lemma concatenate = refl
lemma takeByteString = refl
lemma dropByteString = refl
lemma sha2-256 = refl
lemma sha3-256 = refl
lemma verifySignature = refl
lemma equalsByteString = refl
lemma ifThenElse = refl

lemma≤ : (b : Builtin) → length (proj₁ (proj₂ (AS.SIG b))) ≤‴ arity b
lemma≤ b rewrite lemma b = ≤‴-refl
\end{code}

\begin{code}
eraseVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ∋ A → Fin (len Γ)
eraseVar Z     = zero
eraseVar (S α) = suc (eraseVar α) 
eraseVar (T α) = eraseVar α

eraseTC : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *} → AC.TyTermCon A → TermCon
eraseTC (AC.integer i)    = integer i
eraseTC (AC.bytestring b) = bytestring b
eraseTC (AC.string s)     = string s
eraseTC (AC.bool b)       = bool b
eraseTC (AC.char c)       = char c
eraseTC AC.unit           = unit

eraseTel : ∀{Φ Γ Δ}{σ : SubNf Δ Φ}{As : List (Δ ⊢Nf⋆ *)}
  → A.Tel Γ Δ σ As
  → Untyped.Tel (length As) (len Γ)
erase : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢ A → len Γ ⊢
erase (` α)                = ` (eraseVar α)
erase (ƛ t)                = ƛ (erase t) 
erase (t · u)              = erase t · erase u
erase (Λ t)                = ƛ (U.weaken (erase t))
erase (_·⋆_ t A)           = erase t · plc_dummy
erase (wrap1 pat arg t)    = erase t
erase (unwrap1 t)          = erase t
erase {Γ = Γ} (con t)      = con (eraseTC {Γ = Γ} t)
erase (builtin bn σ ts)    = builtin bn (lemma≤ bn) (eraseTel ts)
erase (error A)            = error

eraseTel {As = []}     _          = []
eraseTel {As = x ∷ As} (t ∷ tel) = erase t ∷ eraseTel tel
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

open import Utils

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
sameTC (DC.bool b)       = refl
sameTC (DC.char c)       = refl
sameTC DC.unit           = refl

lem≡Ctx : ∀{Φ}{Γ Γ' : Ctx Φ} → Γ ≡ Γ' → len Γ ≡ len Γ'
lem≡Ctx refl = refl

lem-conv∋ : ∀{Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')(x : Γ A.∋ A)
  → subst Fin (lem≡Ctx p) (eraseVar x)  ≡ eraseVar (conv∋ p q x)
lem-conv∋ refl refl x = refl

sameVar : ∀{Φ Γ}{A : Φ ⊢⋆ *}(x : Γ D.∋ A)
  → D.eraseVar x ≡ subst Fin (lenLemma Γ) (eraseVar (nfTyVar x))
sameVar {Γ = Γ D., _} D.Z     = lemzero (cong suc (lenLemma Γ))
sameVar {Γ = Γ D., _} (D.S x) = trans
  (cong suc (sameVar x))
  (lemsuc (cong suc (lenLemma Γ)) (lenLemma Γ) (eraseVar (nfTyVar x)))
sameVar {Γ = Γ D.,⋆ _} (D.T {A = A} x) = trans
  (sameVar x)
  (cong (subst Fin (lenLemma Γ)) (lem-conv∋ refl (ren-nf S A) (T (nfTyVar x))))

lemVar : ∀{n n'}(p : n ≡ n')(i : Fin n) →  ` (subst Fin p i) ≡ subst _⊢ p (` i)
lemVar refl i = refl

lemƛ : ∀{n n'}(p : n ≡ n')(q : suc n ≡ suc n')(t : suc n ⊢)
  → ƛ (subst _⊢ q t) ≡ subst _⊢ p (ƛ t)  
lemƛ refl refl t = refl

lem· : ∀{n n'}(p : n ≡ n')(t u : n ⊢) → subst _⊢ p t · subst _⊢ p u ≡ subst _⊢ p (t · u)
lem· refl t u = refl

lem-weaken : ∀{n n'}(p : n ≡ n')(q : suc n ≡ suc n')(t : n ⊢)
  → U.weaken (subst _⊢ p t) ≡ subst _⊢ q (U.weaken t)
lem-weaken refl refl t = refl

lemcon' : ∀{n n'}(p : n ≡ n')(tcn : TermCon) → con tcn ≡ subst _⊢ p (con tcn)
lemcon' refl tcn = refl

lemerror : ∀{n n'}(p : n ≡ n') →  error ≡ subst _⊢ p error
lemerror refl = refl

lem[]' : ∀{n n'}(p : n ≡ n') →
  [] ≡ subst (λ n → Vec (n ⊢) 0) p []
lem[]' refl = refl

lem-plc_dummy : ∀{n n'}(p : n ≡ n') →
  plc_dummy ≡ subst _⊢ p plc_dummy
lem-plc_dummy refl = refl


lem∷ : ∀{m n n'}(p : n ≡ n')(t : n ⊢)(ts : Vec (n ⊢) m)
  → subst _⊢ p t ∷ subst (λ n → Vec (n ⊢) m) p ts ≡ subst (λ n → Vec (n ⊢) (suc m)) p (t ∷ ts) 
lem∷ refl t ts = refl

lem∷' : ∀{A : Set}{n n'}(p : n ≡ n')(q : suc n ≡ suc n')(t : A)(ts : Vec A n)
  → t ∷ subst (Vec A) p ts ≡ subst (Vec A) q (t ∷ ts) 
lem∷' refl refl t ts = refl

lemTel : ∀{m n n'}(p : n ≡ n')(bn : Builtin)(ts : Vec (n ⊢) m)
  → (q : m ≤‴ arity bn)
  → builtin bn q (subst (λ n → Vec (n ⊢) m) p ts)
    ≡ subst _⊢ p (builtin bn q ts)
lemTel refl bn ts q = refl

lem-erase : ∀{Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')(t : Γ A.⊢ A)
  → subst _⊢ (lem≡Ctx p) (erase t)  ≡ erase (conv⊢ p q t)
lem-erase refl refl t = refl


{-
lem-convTel : ∀{Φ Γ Γ' Δ}(As : List (Δ ⊢Nf⋆ *))(p : Γ ≡ Γ')
  → (σ : ∀{J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)
  → (tel : A.Tel Γ Δ σ As)
  → subst (List ∘ _⊢) (lem≡Ctx p) (eraseTel tel)
    ≡ eraseTel (convTel p σ As tel)
lem-convTel []       p σ _         = sym (lem[]' (lem≡Ctx p))
lem-convTel (A ∷ As) p σ (t ,, ts) = trans
  (sym (lem∷ (lem≡Ctx p) (erase t) (eraseTel ts)))
  (cong₂ _∷_ (lem-erase p refl t) (lem-convTel As p σ ts))
-}

lem-subst : ∀{n}(t : n ⊢)(p : n ≡ n) → subst _⊢ p t ≡ t
lem-subst t refl = refl

open import Relation.Nullary
open import Data.Empty

-- these two may be in the standard library
lem¬≤ : ∀{n} → ¬ (suc n Data.Nat.≤ n)
lem¬≤ (s≤s p) = lem¬≤ p

lem≤‴ : ∀{m n}(p q : m ≤‴ n) → p ≡ q
lem≤‴ ≤‴-refl ≤‴-refl     = refl
lem≤‴ ≤‴-refl (≤‴-step q) = ⊥-elim (lem¬≤ (≤″⇒≤ (≤‴⇒≤″ q)))
lem≤‴ (≤‴-step p) ≤‴-refl = ⊥-elim (lem¬≤ (≤″⇒≤ (≤‴⇒≤″ p)))
lem≤‴ (≤‴-step p) (≤‴-step q) = cong ≤‴-step (lem≤‴ p q)

lem-builtin : ∀{m n n'}(b : Builtin)(ts : Untyped.Tel n m)
  → (p : n ≤‴ arity b)
  → (q : n' ≤‴ arity b)
  → (r : n ≡ n')
  → Untyped.builtin b p ts ≡ builtin b q (subst (Vec (m ⊢)) r ts)
lem-builtin b ts p q refl = cong (λ p → builtin b p ts) (lem≤‴ p q)

lem-erase' : ∀{Φ Γ}{A A' : Φ ⊢Nf⋆ *}(q : A ≡ A')(t : Γ A.⊢ A)
  → erase t  ≡ erase (conv⊢ refl q t)
lem-erase' {Γ = Γ} p t = trans
  (sym (lem-subst (erase t) (lem≡Ctx {Γ = Γ} refl)))
  (lem-erase refl p t)

same : ∀{Φ Γ}{A : Φ ⊢⋆ *}(t : Γ D.⊢ A)
  → D.erase t ≡ subst _⊢ (lenLemma Γ) (erase (nfType t)) 

sameTel : ∀{Φ Γ Δ Δ'}
  (σ : T.Sub Δ Φ)
  (As : List (Δ ⊢⋆ *))
  (p : Δ' ≡ Δ)
  (As' : List (Δ' ⊢Nf⋆ *))
  (q : subst (λ Δ → List (Δ ⊢Nf⋆ *)) p As' ≡ nfList As)
  (r : length As ≡ length As')
  (tel : D.Tel Γ Δ σ As)
  → subst (Vec (D.len Γ ⊢)) r (D.eraseTel tel)
    ≡
    subst (λ n → Vec (n ⊢) (length As')) (lenLemma Γ) (eraseTel (nfTypeTel' σ As p As' q tel) )
sameTel {Γ = Γ} σ [] refl .[] refl refl tel = lem[]' (lenLemma Γ)
sameTel {Γ = Γ} σ (A ∷ As) refl .(nf A ∷ nfList As) refl r (t ,, ts) = trans (sym (lem∷' (suc-injective r) r (D.erase t) (D.eraseTel ts))) (trans (cong₂ _∷_ (same t) (sameTel σ As refl (nfList As) refl (suc-injective r) ts)) (trans (lem∷ (lenLemma Γ) (erase (nfType t)) (eraseTel (nfTypeTel σ As ts))) (cong (λ t → subst (λ n → Vec (n ⊢) (suc (length (nfList As)))) (lenLemma Γ) (t ∷ eraseTel (nfTypeTel σ As ts))) (lem-erase' ((sym
      (trans
        (trans
          (subst-eval (embNf (nf A)) idCR (embNf ∘ nf ∘ σ))
          (fund
            (λ α → fund idCR (sym≡β (soundness (σ α))))
            (sym≡β (soundness A))))
        (sym (subst-eval A idCR σ))))) (nfType t)) )))

open import Data.Unit
same {Γ = Γ}(D.` x) =
  trans (cong ` (sameVar x)) (lemVar (lenLemma Γ) (eraseVar (nfTyVar x)))
same {Γ = Γ} (D.ƛ t) = trans
  (cong ƛ (same t))
  (lemƛ (lenLemma Γ) (cong suc (lenLemma Γ)) (erase (nfType t)))
same {Γ = Γ} (t D.· u) = trans
  (cong₂ _·_ (same t) (same u))
  (lem· (lenLemma Γ) (erase (nfType t)) (erase (nfType u)))
same {Γ = Γ} (D.Λ {B = B} t) = trans (trans (trans (cong (ƛ ∘ U.weaken) (same t)) (cong ƛ (lem-weaken (lenLemma Γ) (cong suc (lenLemma Γ)) (erase (nfType t))))) (lemƛ (lenLemma Γ) (cong suc (lenLemma Γ)) (U.weaken (erase (nfType t))))) (cong (subst _⊢ (lenLemma Γ) ∘ ƛ ∘ U.weaken) (lem-erase' (substNf-lemma' B) (nfType t)))
same {Γ = Γ} (D._·⋆_ {B = B} t A) = trans
  (cong (_· plc_dummy) (same t))
  (trans
    (trans (cong₂ _·_ (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (lemΠ B) (nfType t)) ) (lem-plc_dummy (lenLemma Γ)))
           (lem· (lenLemma Γ) (erase (conv⊢ refl (lemΠ B) (nfType t))) plc_dummy))
    (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (lem[] A B) (conv⊢ refl (lemΠ B) (nfType t) ·⋆ nf A)))) 
same {Γ = Γ} (D.wrap1 pat arg t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (lemXX pat arg) (nfType t)))
same {Γ = Γ} (D.unwrap1 {pat = pat}{arg = arg} t) = trans
  (same t)
  (cong
    (subst _⊢ (lenLemma Γ))
    (lem-erase' (sym (lemXX pat arg)) (unwrap1 (nfType t)))) 
same {Γ = Γ} (D.conv p t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (completeness p) (nfType t)))
same {Γ = Γ} (D.con tcn) = trans
  (cong con (sameTC {Γ = Γ} tcn))
  (lemcon' (lenLemma Γ) (eraseTC {Γ = nfCtx Γ} (nfTypeTC tcn)))

same {Γ = Γ} (D.builtin bn σ ts) = trans (trans (trans (lem-builtin bn (D.eraseTel ts) (D.lemma≤ bn) (lemma≤ bn) (nfTypeSIG≡₃ bn)) (cong (Untyped.builtin bn (lemma≤ bn)) (sameTel σ _ (sym (nfTypeSIG≡₁ bn)) _ (lemList bn) (nfTypeSIG≡₃ bn) ts))) (lemTel (lenLemma Γ) bn ((eraseTel
  (nfTypeTel' (λ {J} → σ) (proj₁ (proj₂ (DS.SIG bn)))
   (sym (nfTypeSIG≡₁ bn)) (proj₁ (proj₂ (AS.SIG bn))) (lemList bn)
   ts))) (lemma≤ bn)))
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase'  (lemσ σ (proj₂ (proj₂ (DS.SIG bn))) (proj₂ (proj₂ (AS.SIG bn)))
         (sym (nfTypeSIG≡₁ bn)) (nfTypeSIG≡₂ bn)) (builtin bn
         (λ {J} x → nf (σ (subst (_∋⋆ J) (sym (nfTypeSIG≡₁ bn)) x)))
         (nfTypeTel' σ (proj₁ (proj₂ (DS.SIG bn))) (sym (nfTypeSIG≡₁ bn))
          (proj₁ (proj₂ (AS.SIG bn))) (lemList bn) ts)))) 
same {Γ = Γ} (D.error A) = lemerror (lenLemma Γ)


open import Algorithmic.Soundness

same'Len : ∀ {Φ}(Γ : A.Ctx Φ) → D.len (embCtx Γ) ≡ len Γ
same'Len ∅          = refl
same'Len (Γ ,⋆ J)   = same'Len Γ
same'Len (Γ , A)    = cong suc (same'Len Γ)

lem-Dconv∋ : ∀{Φ Γ Γ'}{A A' : Φ ⊢⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')(x : Γ D.∋ A)
  → subst Fin (cong D.len p) (D.eraseVar x)  ≡ D.eraseVar (D.conv∋ p q x)
lem-Dconv∋ refl refl x = refl

same'Var : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ A.∋ A)
  →  eraseVar x ≡ subst Fin (same'Len Γ) (D.eraseVar (embVar x))
same'Var {Γ = Γ , _} Z     = lemzero (cong suc (same'Len Γ))
same'Var {Γ = Γ , _} (S x) = trans
  (cong suc (same'Var x))
  (lemsuc (cong suc (same'Len Γ)) (same'Len Γ) (D.eraseVar (embVar x)))
same'Var {Γ = Γ ,⋆ _} (T {A = A} x) = trans
  (same'Var x)
  (cong (subst Fin (same'Len Γ)) (lem-Dconv∋ refl (sym (ren-embNf S A))
        (D.T (embVar x))))

same'TC : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(tcn : AC.TyTermCon A)
  → eraseTC {Γ = Γ} tcn ≡ D.eraseTC {Φ}{Γ = embCtx Γ} (embTC tcn)
same'TC (AC.integer i)    = refl
same'TC (AC.bytestring b) = refl
same'TC (AC.string s)     = refl
same'TC (AC.bool b)       = refl
same'TC (AC.char c)       = refl
same'TC AC.unit           = refl


same' : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ A.⊢ A)
  →  erase x ≡ subst _⊢ (same'Len Γ) (D.erase (emb x))

same'Tel : ∀{Φ Γ Δ Δ'}
  (σ : SubNf Δ Φ)
  (As : List (Δ ⊢Nf⋆ *))
  (tel : A.Tel Γ Δ σ As)
  (p : Δ' ≡ Δ)
  (As' : List (Δ' ⊢⋆ *))
  (q : length As ≡ length As')
  (r : embList As ≡βL subst (λ Δ → List (Δ ⊢⋆ *)) p As')
  →
  subst (Vec (len Γ ⊢)) q (eraseTel tel)
    ≡
    subst (λ n → Vec (n ⊢) (length As')) (same'Len Γ) (D.eraseTel (embTel p As As' r σ tel))

same'Tel {Γ = Γ} σ .[] [] p [] refl r = lem[]' (same'Len Γ)
same'Tel {Γ = Γ} σ .(_ ∷ _) (t ∷ ts) refl (A' ∷ As') q r = trans
  (trans (trans (sym (lem∷' (suc-injective q) q (erase t) (eraseTel ts))) (cong (_∷ _) (same' t)))
         (cong (subst _⊢ (same'Len Γ) (D.erase (emb t)) ∷_) (same'Tel σ _ ts refl As' (suc-injective q) (proj₂ r))))
  (lem∷  (same'Len Γ) (D.erase (emb t)) (D.eraseTel (embTel refl _ As' (proj₂ r) σ ts)))

same' {Γ = Γ} (` x) =
  trans (cong ` (same'Var x)) (lemVar (same'Len Γ) (D.eraseVar (embVar x)))
same' {Γ = Γ} (ƛ t) = trans
  (cong ƛ (same' t))
  (lemƛ (same'Len Γ) (cong suc (same'Len Γ)) (D.erase (emb t)))
same' {Γ = Γ} (t · u) = trans
  (cong₂ _·_ (same' t) (same' u))
  (lem· (same'Len Γ) (D.erase (emb t)) (D.erase (emb u)))
same' {Γ = Γ} (Λ t)      = trans
  (trans (cong (ƛ ∘ U.weaken) (same' t))
         (cong ƛ
               (lem-weaken (same'Len Γ) (cong suc (same'Len Γ)) (D.erase (emb t)))))
  (lemƛ (same'Len Γ) (cong suc (same'Len Γ)) (U.weaken (D.erase (emb t))))
same' {Γ = Γ} (_·⋆_ t A)   = trans
  (cong₂ _·_ (same' t) (lem-plc_dummy (same'Len Γ)))
  (lem· (same'Len Γ) (D.erase (emb t)) plc_dummy)
same' {Γ = Γ} (wrap1 pat arg t)   = same' t
same' {Γ = Γ} (unwrap1 t) = same' t
same' {Γ = Γ} (con x) = trans (cong con (same'TC {Γ = Γ} x)) (lemcon' (same'Len Γ) (D.eraseTC {Γ = embCtx Γ}(embTC x)))
same' {Γ = Γ} (builtin b σ ts) = trans (trans (lem-builtin b (eraseTel ts) (lemma≤ b) (D.lemma≤ b) (sym (nfTypeSIG≡₃ b))) (cong (builtin b (D.lemma≤ b)) (same'Tel σ (proj₁ (proj₂ (AS.SIG b))) ts (nfTypeSIG≡₁ b) (proj₁ (proj₂ (DS.SIG b))) (sym (nfTypeSIG≡₃ b)) (lemList' b) ))) (lemTel (same'Len Γ) b (D.eraseTel (embTel (nfTypeSIG≡₁ b) (proj₁ (proj₂ (AS.SIG b))) (proj₁ (proj₂ (DS.SIG b))) (lemList' b) σ ts)) (D.lemma≤ b)) 
same' {Γ = Γ} (error A) = lemerror (same'Len Γ)
\end{code}
