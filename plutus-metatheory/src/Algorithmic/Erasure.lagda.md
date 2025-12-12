---
title: Algorithmic.Erasure
layout: page
---
```
module Algorithmic.Erasure where
```

```
open import Agda.Primitive using (lzero)
open import Data.Nat using (ℕ;suc;zero)
open import Function using (_∘_;id)
open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-cancelˡ-≡)
open import Data.Fin using (Fin;zero;suc;toℕ)
open import Data.List.Properties using (map-compose;map-id)
open import Data.Vec using (Vec;lookup)
open import Data.Product using () renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;subst;trans;sym;cong₂;cong-app)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)

open import Algorithmic as A
open import Untyped using (_⊢)
open _⊢

open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;ren-embNf;embNf)
open _⊢Nf⋆_
open _⊢Ne⋆_

open import Type.BetaNBE using (nf;reflect;eval-VecList;lookup-eval-VecList )
open import Type.BetaNBE.Completeness using (completeness)
open import Utils using (Kind;*;Maybe;nothing;just;fromList;map-cong)
open import Utils.List using (List;IList;[];_∷_;map)
open import RawU using (TmCon;tmCon;TyTag)
open import Builtin.Signature using (_⊢♯)
open _⊢♯
open import Builtin.Constant.Type

open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;S;Z)
open _⊢⋆_

open import Type.BetaNBE.RenamingSubstitution using (ren-nf;subNf-lemma')
open import Type.BetaNBE.Stability using (stability)

open import Builtin using (Builtin)
open import Type.RenamingSubstitution as T

import Declarative as D
import Declarative.Erasure as D
open import Algorithmic.Completeness using (nfCtx;nfTyVar;nfType;lemΠ;lem[];stability-μ;btype-lem;nfType-ConstrArgs;nfType-Cases;lemma-mkCaseType)
open import Algorithmic.Soundness using (embCtx;embVar;emb;emb-ConstrArgs;lema-mkCaseType)
```

```
len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Γ ,⋆ K) = suc (len⋆ Γ)

len : ∀{Φ} → Ctx Φ → ℕ
len ∅ = 0
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = suc (len Γ)
```

```
eraseVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ∋ A → Fin (len Γ)
eraseVar Z     = zero
eraseVar (S α) = suc (eraseVar α)
eraseVar (T α) = eraseVar α

eraseTC : (A : ∅ ⊢Nf⋆ Kind.♯) → ⟦ A ⟧ → TmCon
eraseTC A t = tmCon (A.ty2sty A) (subst ⟦_⟧ (ty≅sty₁ A) t)

erase : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢ A → len Γ ⊢

erase-ConstrArgs : ∀ {Φ} {Γ : Ctx Φ}
               {Ts : List (Φ ⊢Nf⋆ *)}
               (cs : ConstrArgs Γ Ts)
          → List (len Γ ⊢)
erase-ConstrArgs [] = []
erase-ConstrArgs (c ∷ cs) = (erase c) ∷ (erase-ConstrArgs cs)

erase-Cases : ∀ {Φ} {Γ : Ctx Φ} {A : Φ ⊢Nf⋆ *} {n}
                {Tss : Vec (List (Φ ⊢Nf⋆ *)) n}
                (cs : Cases Γ A Tss) →
              List (len Γ ⊢)
erase-Cases [] = []
erase-Cases (c ∷ cs) = (erase c) ∷ (erase-Cases cs)

erase (` α)                  = ` (eraseVar α)
erase (ƛ t)                  = ƛ (erase t)
erase (t · u)                = erase t · erase u
erase (Λ t)                  = delay (erase t)
erase (t ·⋆ A / refl)        = force (erase t)
erase (wrap A B t)           = erase t
erase (unwrap t refl)        = erase t
erase (con {A = A} t p)      = con (eraseTC A t)
erase (builtin b / refl)     = builtin b
erase (error A)              = error
erase (constr e Tss p cs)    = constr (toℕ e) (erase-ConstrArgs cs)
erase (case t cases)         = case (erase t) (erase-Cases cases)
```

Porting this from declarative required basically deleting one line but
I don't think I can fully exploit this by parameterizing the module as
I need to pattern match on the term constructors

# Erasing decl/alg terms agree

```
lenLemma : ∀ {Φ}(Γ : D.Ctx Φ) → len (nfCtx Γ) ≡ D.len Γ
lenLemma D.∅        = refl
lenLemma (Γ D.,⋆ J) = lenLemma Γ
lenLemma (Γ D., A)  = cong suc (lenLemma Γ)

lenLemma⋆ : ∀ Φ → D.len⋆ Φ ≡ len⋆ Φ
lenLemma⋆ ∅       = refl
lenLemma⋆ (Φ ,⋆ K) = cong suc (lenLemma⋆ Φ)

-- these lemmas for each clause of eraseVar and erase below could be
-- avoided by using with but it would involve doing with on a long
-- string of arguments, both contexts, equality proof above, and
-- before and after versions of all arguments and all recursive calls

lemzero : ∀{X X' : ℕ} (p : suc X ≡ suc X') → zero ≡ subst Fin p zero
lemzero refl = refl

lemsuc : ∀{X X' : ℕ} (p : suc X ≡ suc X') (q : X ≡ X') (x : Fin X) →
  suc (subst Fin q x) ≡ subst Fin p (suc x)
lemsuc refl refl x = refl

lem≡Ctx : ∀{Φ}{Γ Γ' : Ctx Φ} → Γ ≡ Γ' → len Γ ≡ len Γ'
lem≡Ctx refl = refl

lem-conv∋ : ∀{Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')(x : Γ A.∋ A)
  →  subst Fin (lem≡Ctx p) (eraseVar x) ≡ eraseVar (conv∋ p q x)
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

lemVar : ∀{X X'}(p : X ≡ X')(x : Fin X) →  ` (subst Fin p x) ≡ subst _⊢ p (` x)
lemVar refl x = refl

lemƛ : ∀{X X'}(p : X ≡ X')(q : suc X ≡ suc X')(t : suc X ⊢)
  → ƛ (subst _⊢ q t) ≡ subst _⊢ p (ƛ t)
lemƛ refl refl t = refl

lem· : ∀{X X'}(p : X ≡ X')(t u : X ⊢) → subst _⊢ p t · subst _⊢ p u ≡ subst _⊢ p (t · u)
lem· refl t u = refl

lem-delay : ∀{X X'}(p : X ≡ X')(t : X ⊢) → delay (subst _⊢ p t) ≡ subst _⊢ p (delay t)
lem-delay refl t = refl

lem-force : ∀{X X'}(p : X ≡ X')(t : X ⊢) → force (subst _⊢ p t) ≡ subst _⊢ p (force t)
lem-force refl t = refl

lemcon' : ∀{X X'}(p : X ≡ X')(tcn : TmCon) → con tcn ≡ subst _⊢ p (con tcn)
lemcon' refl tcn = refl

lemerror : ∀{X X'}(p : X ≡ X') →  error ≡ subst _⊢ p error
lemerror refl = refl

lembuiltin : ∀{X X'}(b : Builtin)(p : X ≡ X') →  builtin b ≡ subst _⊢ p (builtin b)
lembuiltin b refl = refl

lemConstr : ∀ {X X'}(e : ℕ) (xs : List (X ⊢))(p : X ≡ X')
         → subst _⊢ p (constr e xs) ≡ constr e (map (subst _⊢ p) xs)
lemConstr e [] refl = refl
lemConstr e (x ∷ xs) refl = cong (constr e) (cong (x ∷_) (sym (map-id xs)))

lemCase : ∀ {X X'}(t : X ⊢) (cs : List (X ⊢))(p : X ≡ X')
        → subst _⊢ p (case t cs) ≡ case (subst _⊢ p t) (map (subst _⊢ p) cs)
lemCase t cs refl = cong (case t) (sym (map-id cs))

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

lem-erase'' : ∀{Φ Γ}{A A' : Φ ⊢Nf⋆ *}(q : A ≡ A')(t : Γ A.⊢ A)
  → erase t  ≡ erase (subst (Γ A.⊢_) q t)
lem-erase'' refl t = refl

same : ∀{Φ Γ}{A : Φ ⊢⋆ *}(t : Γ D.⊢ A)
  → D.erase t ≡ subst _⊢ (lenLemma Γ) (erase (nfType t))

+cancel : ∀{m m' n n'} → m + n ≡ m' + n' → m ≡ m' → n ≡ n'
+cancel p refl = +-cancelˡ-≡ _ _ _ p

same-ConstrArgs : ∀{Φ}{Γ : D.Ctx Φ}{Ts : List (Φ ⊢⋆ *)}

                   (xs : D.ConstrArgs Γ Ts)
   → D.erase-ConstrArgs xs ≡ map (subst _⊢ (lenLemma Γ)) (erase-ConstrArgs (nfType-ConstrArgs xs))
same-ConstrArgs {Γ = Γ} [] = refl
same-ConstrArgs {Γ = Γ} (x ∷ xs) = cong₂ _∷_ (same x) (same-ConstrArgs xs)

same-mkCaseType : ∀ {Φ} {Γ : Ctx Φ} {A B : Φ ⊢Nf⋆ *}
                           (c : Γ ⊢ A)
                           (eq : A ≡ B)
            → erase {Φ} {Γ} { A } c ≡ erase {Φ} {Γ} { B } (subst (Γ ⊢_) eq c)
same-mkCaseType c refl = refl

same-Cases : ∀ {Φ} {Γ : D.Ctx Φ} {A : Φ ⊢⋆ *} {n}
               {Tss : Vec (List (Φ ⊢⋆ *)) n}
               (cases : D.Cases Γ A Tss) →
             D.erase-Cases cases ≡
             map (subst _⊢ (lenLemma Γ)) (erase-Cases (nfType-Cases cases))
same-Cases D.[] = refl
same-Cases {Γ = Γ}(D._∷_ {Ts = As} c cs) = cong₂ _∷_ (trans (same c)
                                                (cong (subst _⊢ (lenLemma Γ)) (same-mkCaseType (nfType c) (lemma-mkCaseType As))))
                                         (same-Cases cs)

same {Γ = Γ}(D.` x) =
  trans (cong ` (sameVar x)) (lemVar (lenLemma Γ) (eraseVar (nfTyVar x)))
same {Γ = Γ} (D.ƛ t) = trans
  (cong ƛ (same t))
  (lemƛ (lenLemma Γ) (cong suc (lenLemma Γ)) (erase (nfType t)))
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
same {Γ = Γ} (D.con {A = A} tcn p) = lemcon' (lenLemma Γ) (eraseTC (nf A) tcn)
same {Γ = Γ} (D.builtin b) = trans
  (lembuiltin b (lenLemma Γ)) (cong (subst _⊢ (lenLemma Γ))
  (lem-erase refl (btype-lem b) (builtin b / refl)))
same {Γ = Γ} (D.error A) = lemerror (lenLemma Γ)
same {Γ = Γ} (D.constr e Tss refl xs) rewrite lemConstr (toℕ e) (erase-ConstrArgs (nfType-ConstrArgs xs)) (lenLemma Γ)
                = cong (constr (toℕ e)) (same-ConstrArgs xs)
same {Γ = Γ} (D.case t cases) rewrite lemCase (erase (nfType t)) (erase-Cases (Algorithmic.Completeness.nfType-Cases cases)) (lenLemma Γ)
     = cong₂ case (same t) (same-Cases cases)

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

same'TC : ∀ {Φ} {Γ : Ctx Φ} A (tcn : ⟦ A ⟧) →
         eraseTC A tcn ≡ D.eraseTC (embNf A) (subst ⟦_⟧ (sym (stability A)) tcn)
same'TC A tcn rewrite stability A = refl

same' : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ A.⊢ A)
  →  erase x ≡ subst _⊢ (same'Len Γ) (D.erase (emb x))

same'ConstrArgs : ∀ {Φ} {Γ : Ctx Φ}
                    {Ts : List (Φ ⊢Nf⋆ *)}
                    (xs : ConstrArgs Γ Ts)
    → erase-ConstrArgs xs ≡  map (subst _⊢ (same'Len Γ))
                                 (D.erase-ConstrArgs (emb-ConstrArgs xs))
same'ConstrArgs [] = refl
same'ConstrArgs (x ∷ xs) = cong₂ _∷_ (same' x) (same'ConstrArgs xs)

same-subst : ∀ {Φ} {Γ : D.Ctx Φ} {A B : Φ ⊢⋆ *}
               (c : Γ D.⊢ A)
               (eq : A ≡ B)
             → D.erase c ≡ D.erase (subst (D._⊢_ Γ) eq c)
same-subst c refl = refl

same'Case : ∀ {Φ} {Γ : Ctx Φ} {A : Φ ⊢Nf⋆ *} {n}
              {Tss : Vec (List (Φ ⊢Nf⋆ *)) n}
              (cases : Cases Γ A Tss)
      → erase-Cases cases ≡ map (subst _⊢ (same'Len Γ))
                                (D.erase-Cases (Algorithmic.Soundness.emb-Cases cases))
same'Case [] = refl
same'Case {Γ = Γ} (_∷_ {Ts = As} c cases) =
    cong₂ _∷_ (trans (same' c)
                     (cong (subst _⊢ (same'Len Γ)) (same-subst (emb c) (lema-mkCaseType As))))
              (same'Case cases)
same' {Γ = Γ} (` x) =
  trans (cong ` (same'Var x)) (lemVar (same'Len Γ) (D.eraseVar (embVar x)))
same' {Γ = Γ} (ƛ t) = trans
  (cong ƛ (same' t))
  (lemƛ (same'Len Γ) (cong suc (same'Len Γ)) (D.erase (emb t)))
same' {Γ = Γ} (t · u) = trans
  (cong₂ _·_ (same' t) (same' u))
  (lem· (same'Len Γ) (D.erase (emb t)) (D.erase (emb u)))
same' {Γ = Γ} (Λ t) =  trans
  (cong delay (same' t))
  (lem-delay (same'Len Γ) (D.erase (emb t)))
same' {Γ = Γ} (t ·⋆ A / refl)   = trans
  (cong force (same' t))
  (lem-force (same'Len Γ) (D.erase (emb t)))
same' (wrap A B t)   = same' t
same' (unwrap t refl) = same' t
same' {Γ = Γ} (con {A = A} tcn refl) = trans (cong con (same'TC {Γ = Γ} A tcn))
  (lemcon' (same'Len Γ) (D.eraseTC (embNf A) (subst ⟦_⟧ (sym (stability A)) tcn)))
same' {Γ = Γ} (builtin b / refl) = lembuiltin b (same'Len Γ)
same' {Γ = Γ} (error A) = lemerror (same'Len Γ)
same' {Γ = Γ} (constr e Tss {ts} refl xs) rewrite lemConstr (toℕ e) (D.erase-ConstrArgs (Algorithmic.Soundness.emb-ConstrArgs xs)) (same'Len Γ)
            = cong (constr (toℕ e)) (same'ConstrArgs xs)
same' {Γ = Γ}(case t cases) rewrite lemCase (D.erase (emb t)) (D.erase-Cases (Algorithmic.Soundness.emb-Cases cases)) (same'Len Γ)
     = cong₂ case (same' t) (same'Case cases)
```
