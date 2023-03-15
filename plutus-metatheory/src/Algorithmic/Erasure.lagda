\begin{code}
--{-# OPTIONS --rewriting #-}
{-# OPTIONS --injective-type-constructors #-}

module Algorithmic.Erasure where
\end{code}

\begin{code}
open import Function using (_∘_;id)
open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-cancelˡ-≡)
open import Data.Fin using (Fin;zero;suc)
open import Data.List using (List;length;[];_∷_)
open import Data.Product using () renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;subst;trans;sym;cong₂)
open import Data.Empty using (⊥)

open import Algorithmic as A
open import Untyped using (_⊢)
open _⊢

open import Type.BetaNormal using (_⊢Nf⋆_;ren-embNf)
open _⊢Nf⋆_

open import Type.BetaNBE using (nf)
open import Type.BetaNBE.Completeness using (completeness)
open import Utils using (Kind;*;Maybe;nothing;just;TermCon)
open TermCon

open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;S;Z)
open _⊢⋆_

open import Type.BetaNBE.RenamingSubstitution using (ren-nf;subNf-lemma')

open import Builtin using (Builtin)
import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con as DC renaming (TermCon to TyTermCon)
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as AC renaming (TermCon to TyTermCon)
open import Type.RenamingSubstitution as T

import Declarative as D
import Declarative.Erasure as D
open import Algorithmic.Completeness using (nfCtx;nfTypeTC;nfTyVar;nfType;lemΠ;lem[];stability-μ;btype-lem)
open import Algorithmic.Soundness using (embCtx;embVar;embTC;emb)
\end{code}

\begin{code}
len⋆ : Ctx⋆ → Set
len⋆ ∅        = ⊥
len⋆ (Γ ,⋆ K) = Maybe (len⋆ Γ)

len : ∀{Φ} → Ctx Φ → Set
len ∅ = ⊥
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = Maybe (len Γ)
\end{code}

\begin{code}
eraseVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ∋ A → len Γ
eraseVar Z     = nothing
eraseVar (S α) = just (eraseVar α)
eraseVar (T α) = eraseVar α

eraseTC : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *} → AC.TyTermCon A → TermCon
eraseTC (AC.integer i)    = integer i
eraseTC (AC.bytestring b) = bytestring b
eraseTC (AC.string s)     = string s
eraseTC (AC.bool b)       = bool b
eraseTC AC.unit           = unit
eraseTC (AC.pdata d)       = pdata d

erase : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢ A → len Γ ⊢
erase (` α)                = ` (eraseVar α)
erase (ƛ t)                = ƛ (erase t) 
erase (t · u)              = erase t · erase u
erase (Λ t)                = delay (erase t)
erase (t ·⋆ A / refl)      = force (erase t)
erase (wrap A B t)         = erase t
erase (unwrap t refl)      = erase t
erase {Γ = Γ} (con t)      = con (eraseTC {Γ = Γ} t)
erase (builtin b / refl)   = builtin b
erase (error A)            = error
\end{code}

Porting this from declarative required basically deleting one line but
I don't think I can fully exploit this by parameterizing the module as
I need to pattern match on the term constructors

# Erasing decl/alg terms agree

\begin{code}
lenLemma : ∀ {Φ}(Γ : D.Ctx Φ) → len (nfCtx Γ) ≡ D.len Γ
lenLemma D.∅        = refl
lenLemma (Γ D.,⋆ J) = lenLemma Γ
lenLemma (Γ D., A)  = cong Maybe (lenLemma Γ)

lenLemma⋆ : ∀ Φ → D.len⋆ Φ ≡ len⋆ Φ
lenLemma⋆ ∅       = refl
lenLemma⋆ (Φ ,⋆ K) = cong Maybe (lenLemma⋆ Φ)

-- these lemmas for each clause of eraseVar and erase below could be
-- avoided by using with but it would involve doing with on a long
-- string of arguments, both contexts, equality proof above, and
-- before and after versions of all arguments and all recursive calls

-- these lemmas (as stated and proved) require injectivity of type
-- constructors
lemzero : ∀{X X'}(p : Maybe X ≡ Maybe X') → nothing ≡ subst id p nothing
lemzero refl = refl

lemsuc : ∀{X X'}(p : Maybe X ≡ Maybe X')(q : X ≡ X')(x : X) →
  just (subst id q x) ≡ subst id p (just x)
lemsuc refl refl x = refl

sameTC : ∀{Φ Γ}{A : Φ ⊢⋆ *}(tcn : DC.TyTermCon A)
  → D.eraseTC {Γ = Γ} tcn ≡ eraseTC {Γ = nfCtx Γ} (nfTypeTC tcn)
sameTC (DC.integer i)    = refl
sameTC (DC.bytestring b) = refl
sameTC (DC.string s)     = refl
sameTC (DC.bool b)       = refl
sameTC DC.unit           = refl
sameTC (DC.pdata d)       = refl


lem≡Ctx : ∀{Φ}{Γ Γ' : Ctx Φ} → Γ ≡ Γ' → len Γ ≡ len Γ'
lem≡Ctx refl = refl

lem-conv∋ : ∀{Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')(x : Γ A.∋ A)
  →  subst id (lem≡Ctx p) (eraseVar x) ≡ eraseVar (conv∋ p q x)
lem-conv∋ refl refl x = refl

sameVar : ∀{Φ Γ}{A : Φ ⊢⋆ *}(x : Γ D.∋ A)
  → D.eraseVar x ≡ subst id (lenLemma Γ) (eraseVar (nfTyVar x))
sameVar {Γ = Γ D., _} D.Z     = lemzero (cong Maybe (lenLemma Γ))
sameVar {Γ = Γ D., _} (D.S x) = trans
  (cong just (sameVar x))
  (lemsuc (cong Maybe (lenLemma Γ)) (lenLemma Γ) (eraseVar (nfTyVar x)))
sameVar {Γ = Γ D.,⋆ _} (D.T {A = A} x) = trans
  (sameVar x)
  (cong (subst id (lenLemma Γ)) (lem-conv∋ refl (ren-nf S A) (T (nfTyVar x))))

lemVar : ∀{X X'}(p : X ≡ X')(x : X) →  ` (subst id p x) ≡ subst _⊢ p (` x)
lemVar refl x = refl

lemƛ : ∀{X X'}(p : X ≡ X')(q : Maybe X ≡ Maybe X')(t : Maybe X ⊢)
  → ƛ (subst _⊢ q t) ≡ subst _⊢ p (ƛ t)  
lemƛ refl refl t = refl

lem· : ∀{X X'}(p : X ≡ X')(t u : X ⊢) → subst _⊢ p t · subst _⊢ p u ≡ subst _⊢ p (t · u)
lem· refl t u = refl

lem-delay : ∀{X X'}(p : X ≡ X')(t : X ⊢) → delay (subst _⊢ p t) ≡ subst _⊢ p (delay t)
lem-delay refl t = refl

lem-force : ∀{X X'}(p : X ≡ X')(t : X ⊢) → force (subst _⊢ p t) ≡ subst _⊢ p (force t)
lem-force refl t = refl

lemcon' : ∀{X X'}(p : X ≡ X')(tcn : TermCon) → con tcn ≡ subst _⊢ p (con tcn)
lemcon' refl tcn = refl

lemerror : ∀{X X'}(p : X ≡ X') →  error ≡ subst _⊢ p error
lemerror refl = refl

lembuiltin : ∀{X X'}(b : Builtin)(p : X ≡ X') →  builtin b ≡ subst _⊢ p (builtin b)
lembuiltin b refl = refl

lem-erase : ∀{Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')(t : Γ A.⊢ A)
  → subst _⊢ (lem≡Ctx p) (erase t)  ≡ erase (conv⊢ p q t)
lem-erase refl refl t = refl

lem-subst : ∀{n}(t : n ⊢)(p : n ≡ n) → subst _⊢ p t ≡ t
lem-subst t refl = refl

lem-erase' : ∀{Φ Γ}{A A' : Φ ⊢Nf⋆ *}(q : A ≡ A')(t : Γ A.⊢ A)
  → erase t  ≡ erase (conv⊢ refl q t)
lem-erase' {Γ = Γ} p t = trans
  (sym (lem-subst (erase t) (lem≡Ctx {Γ = Γ} refl)))
  (lem-erase refl p t)

same : ∀{Φ Γ}{A : Φ ⊢⋆ *}(t : Γ D.⊢ A)
  → D.erase t ≡ subst _⊢ (lenLemma Γ) (erase (nfType t)) 

+cancel : ∀{m m' n n'} → m + n ≡ m' + n' → m ≡ m' → n ≡ n'
+cancel p refl = +-cancelˡ-≡ _ p

same {Γ = Γ}(D.` x) =
  trans (cong ` (sameVar x)) (lemVar (lenLemma Γ) (eraseVar (nfTyVar x)))
same {Γ = Γ} (D.ƛ t) = trans
  (cong ƛ (same t))
  (lemƛ (lenLemma Γ) (cong Maybe (lenLemma Γ)) (erase (nfType t)))
same {Γ = Γ} (t D.· u) = trans
  (cong₂ _·_ (same t) (same u))
  (lem· (lenLemma Γ) (erase (nfType t)) (erase (nfType u)))
same {Γ = Γ} (D.Λ {B = B} t) = trans
  (trans (cong delay (same t))
         (lem-delay (lenLemma Γ) (erase (nfType t))))
  (cong (subst _⊢ (lenLemma Γ) ∘ delay)
        (lem-erase' (subNf-lemma' B) (nfType t)))
same {Γ = Γ} (D._·⋆_ {B = B} t A) = trans
  (trans (cong force (same t))
         (lem-force (lenLemma Γ) (erase (nfType t))))
  (cong (subst _⊢ (lenLemma Γ))
        (trans (cong force (lem-erase' (lemΠ B) (nfType t)))
        (lem-erase' (lem[] A B) (conv⊢ refl (lemΠ B) (nfType t) ·⋆ nf A / refl))))
same {Γ = Γ} (D.wrap A B t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (stability-μ A B) (nfType t)))
same {Γ = Γ} (D.unwrap {A = A}{B = B} t) = trans
  (same t)
  (cong
    (subst _⊢ (lenLemma Γ))
    (lem-erase' (sym (stability-μ A B)) (unwrap (nfType t) refl))) 
same {Γ = Γ} (D.conv p t) = trans
  (same t)
  (cong (subst _⊢ (lenLemma Γ)) (lem-erase' (completeness p) (nfType t)))
same {Γ = Γ} (D.con tcn) = trans
  (cong con (sameTC {Γ = Γ} tcn))
  (lemcon' (lenLemma Γ) (eraseTC {Γ = nfCtx Γ} (nfTypeTC tcn)))
same {Γ = Γ} (D.builtin b) = trans
  (lembuiltin b (lenLemma Γ)) (cong (subst _⊢ (lenLemma Γ))
  (lem-erase refl (btype-lem b) (builtin b / refl)))
same {Γ = Γ} (D.error A) = lemerror (lenLemma Γ)

same'Len : ∀ {Φ}(Γ : A.Ctx Φ) → D.len (embCtx Γ) ≡ len Γ
same'Len ∅          = refl
same'Len (Γ ,⋆ J)   = same'Len Γ
same'Len (Γ , A)    = cong Maybe (same'Len Γ)

lem-Dconv∋ : ∀{Φ Γ Γ'}{A A' : Φ ⊢⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')(x : Γ D.∋ A)
  → subst id (cong D.len p) (D.eraseVar x)  ≡ D.eraseVar (D.conv∋ p q x)
lem-Dconv∋ refl refl x = refl

same'Var : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ A.∋ A)
  →  eraseVar x ≡ subst id (same'Len Γ) (D.eraseVar (embVar x))
same'Var {Γ = Γ , _} Z     = lemzero (cong Maybe (same'Len Γ))
same'Var {Γ = Γ , _} (S x) = trans
  (cong just (same'Var x))
  (lemsuc (cong Maybe (same'Len Γ)) (same'Len Γ) (D.eraseVar (embVar x)))
same'Var {Γ = Γ ,⋆ _} (T {A = A} x) = trans
  (same'Var x)
  (cong (subst id (same'Len Γ)) (lem-Dconv∋ refl (sym (ren-embNf S A))
        (D.T (embVar x))))

same'TC : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(tcn : AC.TyTermCon A)
  → eraseTC {Γ = Γ} tcn ≡ D.eraseTC {Φ}{Γ = embCtx Γ} (embTC tcn)
same'TC (AC.integer i)    = refl
same'TC (AC.bytestring b) = refl
same'TC (AC.string s)     = refl
same'TC (AC.bool b)       = refl
same'TC AC.unit           = refl
same'TC (AC.pdata d)       = refl

same' : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ A.⊢ A)
  →  erase x ≡ subst _⊢ (same'Len Γ) (D.erase (emb x))
same' {Γ = Γ} (` x) =
  trans (cong ` (same'Var x)) (lemVar (same'Len Γ) (D.eraseVar (embVar x)))
same' {Γ = Γ} (ƛ t) = trans
  (cong ƛ (same' t))
  (lemƛ (same'Len Γ) (cong Maybe (same'Len Γ)) (D.erase (emb t)))
same' {Γ = Γ} (t · u) = trans
  (cong₂ _·_ (same' t) (same' u))
  (lem· (same'Len Γ) (D.erase (emb t)) (D.erase (emb u)))
same' {Γ = Γ} (Λ t) =  trans
  (cong delay (same' t))
  (lem-delay (same'Len Γ) (D.erase (emb t)))
same' {Γ = Γ} (t ·⋆ A / refl)   = trans
  (cong force (same' t))
  (lem-force (same'Len Γ) (D.erase (emb t)))
same' {Γ = Γ} (wrap A B t)   = same' t
same' {Γ = Γ} (unwrap t refl) = same' t
same' {Γ = Γ} (con x) = trans
  (cong con (same'TC {Γ = Γ} x))
  (lemcon' (same'Len Γ) (D.eraseTC {Γ = embCtx Γ}(embTC x)))
same' {Γ = Γ} (builtin b / refl) = lembuiltin b (same'Len Γ)
same' {Γ = Γ} (error A) = lemerror (same'Len Γ)
\end{code}
