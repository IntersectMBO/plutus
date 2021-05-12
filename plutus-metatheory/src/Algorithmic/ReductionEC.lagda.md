```
module Algorithmic.ReductionEC where
```

## Imports

```
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to substEq)
open import Agda.Builtin.String using (primStringFromList; primStringAppend)
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Function hiding (_∋_)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_) renaming (_*_ to _**_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
open import Data.List as List using (List; _∷_; []; _++_;reverse;length)
open import Data.Bool using (Bool;true;false)
open import Data.Nat using (zero;ℕ;_+_)
open import Data.Unit using (tt)
import Debug.Trace as Debug


open import Type
import Type.RenamingSubstitution as T
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Utils
open import Data.Maybe using (just;from-just)
open import Data.String using (String)
```

## Values

```

data Arg : Set where
  Term Type : Arg

Arity = List Arg

-- number of args still needed

arity : Builtin → Arity
arity addInteger = Term ∷ Term ∷ []
arity subtractInteger = Term ∷ Term ∷ []
arity multiplyInteger = Term ∷ Term ∷ []
arity divideInteger = Term ∷ Term ∷ []
arity quotientInteger = Term ∷ Term ∷ []
arity remainderInteger = Term ∷ Term ∷ []
arity modInteger = Term ∷ Term ∷ []
arity lessThanInteger = Term ∷ Term ∷ []
arity lessThanEqualsInteger = Term ∷ Term ∷ []
arity greaterThanInteger = Term ∷ Term ∷ []
arity greaterThanEqualsInteger = Term ∷ Term ∷ []
arity equalsInteger = Term ∷ Term ∷ []
arity concatenate = Term ∷ Term ∷ []
arity takeByteString = Term ∷ Term ∷ []
arity dropByteString = Term ∷ Term ∷ []
arity lessThanByteString = Term ∷ Term ∷ []
arity greaterThanByteString = Term ∷ Term ∷ []
arity sha2-256 = Term ∷ []
arity sha3-256 = Term ∷ []
arity verifySignature = Term ∷ Term ∷ Term ∷ []
arity equalsByteString = Term ∷ Term ∷ []
arity ifThenElse = Type ∷ Term ∷ Term ∷ Term ∷ []
arity charToString = Term ∷ []
arity append = Term ∷ Term ∷ []
arity trace = Term ∷ []

data Bwd (A : Set) : Set where
  [] : Bwd A
  _∷_ : Bwd A → A → Bwd A

cons : ∀{A} → A → Bwd A → Bwd A
cons a [] = [] ∷ a
cons a (as ∷ a') = cons a as ∷ a'

data _<>>_∈_ : ∀{A} → Bwd A → List A → List A → Set where
  start : ∀{A}(as : List A) → [] <>> as ∈ as
  bubble : ∀{A}{a : A}{as : Bwd A}{as' as'' : List A} → as <>> (a ∷ as') ∈ as''
    → (as ∷ a) <>> as' ∈ as''

unique<>> : ∀{A}{az : Bwd A}{as as' : List A}(p p' : az <>> as ∈ as') → p ≡ p'
unique<>> (start _) (start _) = refl
unique<>> (bubble p) (bubble p') = cong bubble (unique<>> p p')

_<>>_ : ∀{A} → Bwd A → List A → List A
[] <>> as = as
(az ∷ a) <>> as = az <>> (a ∷ as)

_<><_ : ∀{A} → Bwd A → List A → Bwd A
az <>< []       = az
az <>< (a ∷ as) = (az ∷ a) <>< as

_<>>_∈'_ : ∀{A} → Bwd A → List A → List A → Set
xs <>> ys ∈' zs = xs <>> ys ≡ zs

bwd-length : ∀{A} → Bwd A → ℕ
bwd-length [] = 0
bwd-length (az ∷ a) = Data.Nat.suc (bwd-length az)

open import Data.Nat.Properties

<>>-length : ∀{A}(az : Bwd A)(as : List A)
  → List.length (az <>> as) ≡ bwd-length az Data.Nat.+ List.length as
<>>-length [] as = refl
<>>-length (az ∷ x) as = trans (<>>-length az (x ∷ as)) (+-suc _ _)

-- reasoning about the length inspired by similar proof about ++ in the stdlib
<>>-rcancel : ∀{A}(az : Bwd A)(as : List A) → az <>> [] ≡ az <>> as → as ≡ []
<>>-rcancel []       as p = sym p
<>>-rcancel (az ∷ a) [] p = refl
<>>-rcancel (az ∷ a) (a' ∷ as) p = ⊥-elim
  (m+1+n≢m 1
           (sym (+-cancelˡ-≡ (bwd-length az)
                             (trans (trans (sym (<>>-length az (a ∷ [])))
                                           (cong List.length p))
                                    (<>>-length az (a ∷ a' ∷ as))))))

<>>-lcancel : ∀{A}(az : Bwd A)(as : List A) → as ≡ az <>> as → az ≡ []
<>>-lcancel []       as p = refl
<>>-lcancel (az ∷ a) as p = ⊥-elim
  (m≢1+n+m (List.length as)
           (trans (trans (cong List.length p)
                         (<>>-length az (a ∷ as)))
                  (+-suc (bwd-length az) (List.length as))))

<>>-lcancel' : ∀{A}(az : Bwd A)(as as' : List A)
  → as ≡ az <>> as'
  → List.length as ≡ List.length as'
  → az ≡ [] × as ≡ as'
<>>-lcancel' [] as as' p q = refl ,, p
<>>-lcancel' (az ∷ a) as as' p q = ⊥-elim
  (m≢1+n+m (List.length as')
           (trans (trans (trans (sym q) (cong List.length p))
                         (<>>-length az (a ∷ as')))
                  (+-suc (bwd-length az) (List.length as'))))

<>>2<>>' : ∀{A}(xs : Bwd A)(ys zs : List A) → xs <>> ys ∈ zs → xs <>> ys ∈' zs
<>>2<>>' [] ys .ys (start .ys) = refl
<>>2<>>' (xs ∷ x) ys zs (bubble p) = <>>2<>>' xs (x ∷ ys) zs p

<>>'2<>> : ∀{A}(xs : Bwd A)(ys zs : List A) → xs <>> ys ∈' zs → xs <>> ys ∈ zs
<>>'2<>> [] ys .ys refl = start ys
<>>'2<>> (xs ∷ x) ys zs p = bubble (<>>'2<>> xs (x ∷ ys) zs p)

data _<><_∈_ : ∀{A} → Bwd A → List A → Bwd A → Set where
  start : ∀{A}(as : Bwd A) → as <>< [] ∈ as
  bubble : ∀{A}{a : A}{as as'' : Bwd A}{as' : List A}
    → (as ∷ a) <>< as' ∈ as''
    → as <>< (a ∷ as') ∈ as''

_<><_∈'_ : ∀{A} → Bwd A → List A → Bwd A → Set
xs <>< ys ∈' zs = xs <>< ys ≡ zs

<><2<><' : ∀{A}(xs : Bwd A)(ys : List A)(zs : Bwd A)
  → xs <>< ys ∈ zs → xs <>< ys ∈' zs
<><2<><' xs [] .xs (start .xs) = refl
<><2<><' xs (y ∷ ys) zs (bubble p) = <><2<><' (xs ∷ y) ys zs p

<><'2<>< : ∀{A}(xs : Bwd A)(ys : List A)(zs : Bwd A)
  → xs <>< ys ∈' zs → xs <>< ys ∈ zs
<><'2<>< xs [] .xs refl = start xs
<><'2<>< xs (x ∷ ys) zs p = bubble (<><'2<>< (xs ∷ x) ys zs p)

lemma<><[] : ∀{A}(xs : Bwd A) → (xs <>< []) ≡ xs
lemma<><[] xs = refl

lemma[]<>> : ∀{A}(xs : List A) → ([] <>> xs) ≡ xs
lemma[]<>> xs = refl

-- convert a list to a backward list and back again

lemma<>1 : ∀{A}(xs : Bwd A)(ys : List A) → (xs <>< ys) <>> [] ≡ xs <>> ys
lemma<>1 xs []       = refl
lemma<>1 xs (x ∷ ys) = lemma<>1 (xs ∷ x) ys

lemma<>2 : ∀{A}(xs : Bwd A)(ys : List A) → ([] <>< (xs <>> ys)) ≡ xs <>< ys
lemma<>2 [] ys = refl
lemma<>2 (xs ∷ x) ys = lemma<>2 xs (x ∷ ys)

saturated : ∀{A}(as : List A) → ([] <>< as) <>> [] ∈ as
saturated as = <>>'2<>> ([] <>< as) [] as (lemma<>1 [] as)


-- I'd prefer not to use cons', stop' and rev
cons' : ∀{A}{a : A}{as : Bwd A}{as' as'' : List A} → as <>> as' ∈ as''
    → (cons a as) <>> as' ∈ (a ∷ as'')
cons' (start _) = bubble (start _)
cons' (bubble p) = bubble (cons' p)

toBwd : ∀{A} → List A → Bwd A
toBwd [] = []
toBwd (a ∷ as) = cons a (toBwd as)

stop' : ∀{A}(as : List A) → toBwd as <>> [] ∈ as
stop' [] = start []
stop' (a ∷ as) = cons' (stop' as)

data Value : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Set

-- one BApp to rule them all...
data BApp (b : Builtin) : ∀{az}{as}
  → az <>> as ∈ arity b
  → ∀{A} → ∅ ⊢ A → Set where
  base : BApp b (start (arity b)) (ibuiltin b)
  step : ∀{A B}{az as}
    → (p : az <>> (Term ∷ as) ∈ arity b)
    → {t : ∅ ⊢ A ⇒ B} → BApp b p t
    → {u : ∅ ⊢ A} → Value u → BApp b (bubble p) (t · u)
  step⋆ : ∀{B}{az as}
    → (p : az <>> (Type ∷ as) ∈ arity b)
    → {t : ∅ ⊢ Π B} → BApp b p t
    → {A : ∅ ⊢Nf⋆ K}
    → BApp b (bubble p) (t ·⋆ A)

data Value where
  V-ƛ : {A B : ∅ ⊢Nf⋆ *}
    → (M : ∅ , A ⊢ B)
      ---------------------------
    → Value (ƛ M)

  V-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
    → (M : ∅ ,⋆ K ⊢ B)
      ----------------
    → Value (Λ M)

  V-wrap : ∀{K}
   → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : ∅ ⊢Nf⋆ K}
   → {M : ∅ ⊢  _}
   → Value M
   → Value (wrap A B M)

  V-con : ∀{tcn : TyCon}
    → (cn : TermCon (con tcn))
    → Value (con cn)

  V-I⇒ : ∀ b {A B as as'}
       → (p : as <>> (Term ∷ as') ∈ arity b)
       → {t : ∅ ⊢ A ⇒ B}
       → BApp b p t
       → Value t
  V-IΠ : ∀ b {A : ∅ ,⋆ K ⊢Nf⋆ *}{as as'}
       → (p : as <>> (Type ∷ as') ∈ arity b)
       → {t : ∅ ⊢ Π A}
       → BApp b p t
       → Value t

deval : {A : ∅ ⊢Nf⋆ *}{u : ∅ ⊢ A} → Value u → ∅ ⊢ A
deval {u = u} _ = u

tval : {A : ∅ ⊢Nf⋆ *}{u : ∅ ⊢ A} → Value u → ∅ ⊢Nf⋆ *
tval {A = A} _ = A

-- this more flexible definition is easier to fully pattern match on
data BAPP (b : Builtin) : ∀{az}{as}
  → az <>> as ∈ arity b
  → ∀{A} → ∅ ⊢ A → Set where
  base : BAPP b (start (arity b)) (ibuiltin b)
  step : ∀{A B}{az as}
    → (p : az <>> (Term ∷ as) ∈ arity b)
    → {t : ∅ ⊢ A ⇒ B} → BAPP b p t
    → {u : ∅ ⊢ A} → Value u → BAPP b (bubble p) (t · u)
  step⋆ : ∀{B C}{az as}
    → (p : az <>> (Type ∷ as) ∈ arity b)
    → {t : ∅ ⊢ Π B} → BAPP b p t
    → {A : ∅ ⊢Nf⋆ K}{tA : ∅ ⊢ C}
    → (q : C ≡ B [ A ]Nf)
    → substEq (∅ ⊢_) q tA ≡ t ·⋆ A
    → BAPP b (bubble p) tA


BUILTIN : ∀ b {A}{t : ∅ ⊢ A} → BAPP b (saturated (arity b)) t → ∅ ⊢ A
BUILTIN addInteger (step .(bubble (start (Term ∷ Term ∷ []))) (step .(start (Term ∷ Term ∷ [])) base (V-con (integer i))) (V-con (integer j))) = con (integer (i Data.Integer.+ j))
BUILTIN ifThenElse (step .(bubble (bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))))) (step .(bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) (step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl refl) (V-con (bool true))) t) f) = deval t
BUILTIN ifThenElse (step .(bubble (bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))))) (step .(bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) (step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl refl) (V-con (bool false))) t) f) = deval f
BUILTIN _ p = error _

convBApp : (b : Builtin) → ∀{az}{as}(p p' : az <>> as ∈ arity b) → ∀{A}(t : ∅ ⊢ A) → BApp b p t → BApp b p' t
convBApp b p p' t q rewrite unique<>> p p' = q

BApp2BAPP : ∀{b : Builtin}{az}{as}{p : az <>> as ∈ arity b}{A}{t : ∅ ⊢ A}
  → BApp b p t → BAPP b p t
BApp2BAPP base         = base
BApp2BAPP (step p q v) = step p (BApp2BAPP q) v
BApp2BAPP (step⋆ p q)  = step⋆ p (BApp2BAPP q) refl refl


BUILTIN' : ∀ b {A}{t : ∅ ⊢ A}{az}(p : az <>> [] ∈ arity b)
  → BApp b p t
  → ∅ ⊢ A
BUILTIN' b {t = t}{az = az} p q
  with sym (trans (cong ([] <><_) (sym (<>>2<>>' _ _ _ p))) (lemma<>2 az []))
... | refl = BUILTIN b (BApp2BAPP  (convBApp b p (saturated (arity b)) t q))

```

```
voidVal : Value (con unit)
voidVal = V-con unit
```

```
data Error :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  -- an actual error term
  E-error : ∀{Φ Γ }{A : Φ ⊢Nf⋆ *} → Error {Γ = Γ} (error {Φ} A)
```

```
convVal :  ∀ {A A' : ∅ ⊢Nf⋆ *}(q : A ≡ A')
  → ∀{t : ∅ ⊢ A} → Value t → Value (conv⊢ refl q t)
convVal refl v = v

convVal' :  ∀ {A A' : ∅ ⊢Nf⋆ *}(q : A ≡ A')
  → ∀{t : ∅ ⊢ A} → Value (conv⊢ refl q t) → Value t
convVal' refl v = v

convBApp1 :  ∀ b {az as}{p : az <>> as ∈ arity b}{A A' : ∅ ⊢Nf⋆ *}(q : A ≡ A')
  → ∀{t : ∅ ⊢ A} → BApp b p t → BApp b p (conv⊢ refl q t)
convBApp1 b refl v = v

convBApp1' :  ∀ b {az as}{p : az <>> as ∈ arity b}{A A' : ∅ ⊢Nf⋆ *}(q : A ≡ A')
  → ∀{t : ∅ ⊢ A} → BApp b p (conv⊢ refl q t) → BApp b p t
convBApp1' b refl v = v

```

## Intrinsically Type Preserving Reduction

```
data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·_     : {A B : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → Frame B A
  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K) → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (μ A B) (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  unwrap- : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) (μ A B)

data EC : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  []   : {A : ∅ ⊢Nf⋆ *} → EC A A
  _l·_ : {A B C : ∅ ⊢Nf⋆ *} → EC (A ⇒ B) C → ∅ ⊢ A → EC B C
  _·r_ : {A B C : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → EC A C → EC B C
  _·⋆_ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{C}
    → EC (Π B) C → (A : ∅ ⊢Nf⋆ K) → EC (B [ A ]Nf) C
  wrap : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}
    → EC (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) C
    → EC (μ A B) C
  unwrap : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}
    → EC (μ A B) C
    → EC (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) C
```

```
infix 2 _—→⋆_

data _—→⋆_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where
  β-ƛ : {A B : ∅ ⊢Nf⋆ *}{N : ∅ , A ⊢ B} {V : ∅ ⊢ A}
    → Value V
      -------------------
    → (ƛ N) · V —→⋆ N [ V ]

  β-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{N : ∅ ,⋆ K ⊢ B}{A}
      -------------------
    → (Λ N) ·⋆ A —→⋆ N [ A ]⋆

  β-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : ∅ ⊢ _}
    → Value M
    → unwrap (wrap A B M) —→⋆ M

  β-sbuiltin : ∀{A B}
      (b : Builtin)
    → (t : ∅ ⊢ A ⇒ B)
    → ∀{az}
    → (p : az <>> (Term ∷ []) ∈ arity b)
    → (bt : BApp b p t) -- one left
    → (u : ∅ ⊢ A)
    → (vu : Value u)
      -----------------------------
    → t · u —→⋆ BUILTIN' b (bubble p) (BApp.step p bt vu) 

  β-sbuiltin⋆ : ∀{B : ∅ ,⋆ K ⊢Nf⋆ *}
      (b : Builtin)
    → (t : ∅ ⊢ Π B)
    → ∀{az}
    → (p : az <>> (Type ∷ []) ∈ arity b)    
    → (bt : BApp b p t) -- one left
    → ∀ A
      -----------------------------
    → t ·⋆ A —→⋆ BUILTIN' b (bubble p) (BApp.step⋆ p bt)

infix 2 _—→_

_[_]ᴱ : ∀{A B : ∅ ⊢Nf⋆ *} → EC B A → ∅ ⊢ A → ∅ ⊢ B
[]       [ L ]ᴱ = L
(E l· B) [ L ]ᴱ = E [ L ]ᴱ · B
(V ·r E) [ L ]ᴱ = deval V · E [ L ]ᴱ
(E ·⋆ A) [ L ]ᴱ = E [ L ]ᴱ ·⋆ A
wrap   E [ L ]ᴱ = wrap _ _ (E [ L ]ᴱ)
unwrap E [ L ]ᴱ = unwrap (E [ L ]ᴱ)

_[_]ᶠ : ∀{A B : ∅ ⊢Nf⋆ *} → Frame B A → ∅ ⊢ A → ∅ ⊢ B
(-· M') [ L ]ᶠ = L · M' 
(V ·-)  [ L ]ᶠ = deval V · L
-·⋆ A   [ L ]ᶠ = L ·⋆ A
wrap-   [ L ]ᶠ = wrap _ _ L
unwrap- [ L ]ᶠ = unwrap L

data _—→_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where

  ruleEC : ∀{A B}{L L' : ∅ ⊢ B}
         → (E : EC A B)
         → L —→⋆ L'
         → ∀{M M' : ∅ ⊢ A}
         → M ≡ E [ L ]ᴱ
         → M' ≡ E [ L' ]ᴱ
           ----
         → M —→ M'

  ruleErr : ∀{A B}
          → (E : EC B A)
            ------------------------
          → E [ error A ]ᴱ —→ error B
```

```
data _—↠_ : {A A' : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → ∅ ⊢ A' → Set
  where

  refl—↠ : ∀{A}{M : ∅ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : ∅ ⊢Nf⋆ *}{M  M' M'' : ∅ ⊢ A}
    → M —→ M'
    → M' —↠ M''
      ---------
    → M —↠ M''
```

```
data Progress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{N : ∅ ⊢ A}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M

  error :
      Error M
      -------
    → Progress M
```

```
ival : ∀ b → Value (ibuiltin b)
ival addInteger = V-I⇒ addInteger (start _) base 
ival subtractInteger = V-I⇒ subtractInteger (start _) base 
ival multiplyInteger = V-I⇒ multiplyInteger (start _) base 
ival divideInteger = V-I⇒ divideInteger (start _) base 
ival quotientInteger = V-I⇒ quotientInteger (start _) base 
ival remainderInteger = V-I⇒ remainderInteger (start _) base 
ival modInteger = V-I⇒ modInteger (start _) base 
ival lessThanInteger = V-I⇒ lessThanInteger (start _) base 
ival lessThanEqualsInteger = V-I⇒ lessThanEqualsInteger (start _) base 
ival greaterThanInteger = V-I⇒ greaterThanInteger (start _) base 
ival greaterThanEqualsInteger = V-I⇒ greaterThanEqualsInteger (start _) base 
ival equalsInteger = V-I⇒ equalsInteger (start _) base 
ival concatenate = V-I⇒ concatenate (start _) base 
ival takeByteString = V-I⇒ takeByteString (start _) base 
ival dropByteString = V-I⇒ dropByteString (start _) base 
ival lessThanByteString = V-I⇒ lessThanByteString (start _) base 
ival greaterThanByteString = V-I⇒ greaterThanByteString (start _) base 
ival sha2-256 = V-I⇒ sha2-256 (start _) base 
ival sha3-256 = V-I⇒ sha3-256 (start _) base 
ival verifySignature = V-I⇒ verifySignature (start _) base 
ival equalsByteString = V-I⇒ equalsByteString (start _) base 
ival ifThenElse = V-IΠ ifThenElse (start _) base 
ival charToString = V-I⇒ charToString (start _) base 
ival append = V-I⇒ append (start _) base 
ival trace = V-I⇒ trace (start _) base 

lemma∷1 : ∀{A}(as as' : List A) → [] <>> as ∈ as' → as ≡ as'
lemma∷1 as .as (start .as) = refl

-- these properties are needed for bappTermLem
<>>-cancel-both : ∀{A}(az az' : Bwd A)(as : List A)
  → az <>> (az' <>> as) ∈ (az' <>> [])
  → az ≡ [] × as ≡ []
<>>-cancel-both az az' [] p =
  <>>-lcancel az (az' <>> []) (sym (<>>2<>>' az (az' <>> []) (az' <>> []) p))
  ,,
  refl
<>>-cancel-both az az' (a ∷ as) p = ⊥-elim (m+1+n≢0
  _
  (+-cancelʳ-≡
    _
    0
    (trans
      (trans
        (+-assoc (bwd-length az) (List.length (a ∷ as)) (bwd-length az'))
        (trans
          (cong
            (bwd-length az Data.Nat.+_)
            (+-comm (List.length (a ∷ as)) (bwd-length az')))
          (trans
            (cong
              (bwd-length az Data.Nat.+_)
              (sym (<>>-length az' (a ∷ as))))
            (trans
              (sym (<>>-length az (az' <>> (a ∷ as))))
              (trans
                (cong
                  List.length
                  (<>>2<>>' az (az' <>> (a ∷ as)) (az' <>> []) p))
                (<>>-length az' []))))))
      (+-comm (bwd-length az') 0))))

<>>-cancel-both' : ∀{A}(az az' az'' : Bwd A)(as : List A)
  → az <>> (az' <>> as) ∈ (az'' <>> []) → bwd-length az' ≡ bwd-length az''
  → az ≡ [] × as ≡ [] × az' ≡ az''
<>>-cancel-both' az az' az'' [] p q
  with <>>-lcancel' az (az'' <>> []) (az' <>> []) (sym (<>>2<>>' _ _ _ p)) (trans (<>>-length az'' []) (trans (cong (Data.Nat._+ 0) (sym q)) (sym (<>>-length az' []))))
... | refl ,, Y = refl ,, refl ,, sym (trans (trans (sym (lemma<>2 az'' [])) (cong ([] <><_) Y)) (lemma<>2 az' []))
<>>-cancel-both' az az' az'' (a ∷ as) p q = ⊥-elim (m+1+n≢0
  _
  (+-cancelʳ-≡
    _
    0
    (trans
      (trans
        (+-assoc (bwd-length az) (List.length (a ∷ as)) (bwd-length az'))
        (trans
          (cong
            (bwd-length az Data.Nat.+_)
            (+-comm (List.length (a ∷ as)) (bwd-length az')))
          (trans
            (cong
              (bwd-length az Data.Nat.+_)
              (sym (<>>-length az' (a ∷ as))))
            (trans
              (sym (<>>-length az (az' <>> (a ∷ as))))
              (trans
                (cong
                  List.length
                  (<>>2<>>' az (az' <>> (a ∷ as)) (az'' <>> []) p))
                (trans (<>>-length az'' []) (cong (Data.Nat._+ 0) (sym q))))))))
      (+-comm (bwd-length az') 0))))

-- these two proofs are defined by pattern matching on the builtin,
-- they are very long and very ugly.  They could probably be made
-- shorter by giving cases for particular types/arities, and adding a
-- lemma that knocks off a more general class of impossible _<>>_∈_
-- inhabitants.

bappTermLem : ∀  b {A}{az as}(M : ∅ ⊢ A)(p : az <>> (Term ∷ as) ∈ arity b)
  → BAPP b p M → ∃ λ A' → ∃ λ A'' → A ≡ A' ⇒ A''
bappTermLem addInteger _ _ base = _ ,, _ ,, refl
bappTermLem addInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem addInteger {as = .[]} (.(ibuiltin addInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem addInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem subtractInteger _ _ base = _ ,, _ ,, refl
bappTermLem subtractInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem subtractInteger {as = .[]} (.(ibuiltin subtractInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem subtractInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem multiplyInteger _ _ base = _ ,, _ ,, refl
bappTermLem multiplyInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem multiplyInteger {as = .[]} (.(ibuiltin multiplyInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem multiplyInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem divideInteger _ _ base = _ ,, _ ,, refl
bappTermLem divideInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem divideInteger {as = .[]} (.(ibuiltin divideInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem divideInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem quotientInteger _ _ base = _ ,, _ ,, refl
bappTermLem quotientInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem quotientInteger {as = .[]} (.(ibuiltin quotientInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem quotientInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem remainderInteger _ _ base = _ ,, _ ,, refl
bappTermLem remainderInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem remainderInteger {as = .[]} (.(ibuiltin remainderInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem remainderInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTermLem modInteger _ _ base = _ ,, _ ,, refl
bappTermLem modInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem modInteger {as = .[]} (.(ibuiltin modInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem modInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTermLem lessThanInteger _ _ base = _ ,, _ ,, refl
bappTermLem lessThanInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem lessThanInteger {as = .[]} (.(ibuiltin lessThanInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem lessThanInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTermLem lessThanEqualsInteger _ _ base = _ ,, _ ,, refl
bappTermLem lessThanEqualsInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem lessThanEqualsInteger {as = .[]} (.(ibuiltin lessThanEqualsInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem lessThanEqualsInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem greaterThanInteger _ _ base = _ ,, _ ,, refl
bappTermLem greaterThanInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem greaterThanInteger {as = .[]} (.(ibuiltin greaterThanInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem greaterThanInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem greaterThanEqualsInteger _ _ base = _ ,, _ ,, refl
bappTermLem greaterThanEqualsInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem greaterThanEqualsInteger {as = .[]} (.(ibuiltin greaterThanEqualsInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem greaterThanEqualsInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem equalsInteger _ _ base = _ ,, _ ,, refl
bappTermLem equalsInteger {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem equalsInteger {as = .[]} (.(ibuiltin equalsInteger) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem equalsInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem concatenate _ _ base = _ ,, _ ,, refl
bappTermLem concatenate {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem concatenate {as = .[]} (.(ibuiltin concatenate) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem concatenate {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem takeByteString _ _ base = _ ,, _ ,, refl
bappTermLem takeByteString {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem takeByteString {as = .[]} (.(ibuiltin takeByteString) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem takeByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTermLem dropByteString _ _ base = _ ,, _ ,, refl
bappTermLem dropByteString {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem dropByteString {as = .[]} (.(ibuiltin dropByteString) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem dropByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem lessThanByteString _ _ base = _ ,, _ ,, refl
bappTermLem lessThanByteString {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem lessThanByteString {as = .[]} (.(ibuiltin lessThanByteString) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem lessThanByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTermLem greaterThanByteString _ _ base = _ ,, _ ,, refl
bappTermLem greaterThanByteString {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem greaterThanByteString {as = .[]} (.(ibuiltin greaterThanByteString) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem greaterThanByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem sha2-256 {az = az} {as} M p q with <>>-cancel-both az ([] ∷ Term) as p
bappTermLem sha2-256 {az = .[]} {.[]} .(ibuiltin sha2-256) .(start (Term ∷ [])) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem sha3-256 {az = az} {as} M p q with <>>-cancel-both az ([] ∷ Term) as p
bappTermLem sha3-256 {az = .[]} {.[]} .(ibuiltin sha3-256) .(start (Term ∷ [])) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem verifySignature .(ibuiltin verifySignature) .(start (Term ∷ Term ∷ Term ∷ [])) base = _ ,, _ ,, refl
bappTermLem verifySignature .(ibuiltin verifySignature · _) .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (step .(start (Term ∷ Term ∷ Term ∷ [])) base x) = _ ,, _ ,, refl
bappTermLem verifySignature {as = as} .((_ · _) · _) .(bubble (bubble p)) (step .(bubble p) (step {az = az} p q x₁) x) with <>>-cancel-both az ((([] ∷ Term) ∷ Term) ∷ Term) as p
bappTermLem verifySignature {as = .[]} ((.(ibuiltin verifySignature) · _) · _) (bubble (bubble .(start (Term ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (step {az = _} .(start (Term ∷ Term ∷ Term ∷ [])) base x₁) x) | refl ,, refl = _ ,, _ ,, refl
bappTermLem verifySignature {as = as} .(_ · _) .(bubble (bubble p)) (step .(bubble p) (step⋆ {az = az} p q q₁ x₁) x) with <>>-cancel-both' az ((([] ∷ Type) ∷ Term) ∷ Term) ((([] ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifySignature {as = as} M .(bubble (bubble p)) (step⋆ .(bubble p) (step {az = az} p q x₁) q₁ x)  with <>>-cancel-both' az ((([] ∷ Term) ∷ Type) ∷ Term) ((([] ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifySignature {as = as} M .(bubble (bubble p)) (step⋆ .(bubble p) (step⋆ {az = az} p q q₂ x₁) q₁ x) with <>>-cancel-both' az ((([] ∷ Type) ∷ Type) ∷ Term) ((([] ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem equalsByteString _ _ base = _ ,, _ ,, refl
bappTermLem equalsByteString {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem equalsByteString {as = .[]} (.(ibuiltin equalsByteString) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem equalsByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTermLem ifThenElse {as = as} .(((_ · _) · _) · _) .(bubble (bubble (bubble p))) (step .(bubble (bubble p)) (step .(bubble p) (step {az = az} p q x₂) x₁) x) with <>>-cancel-both' az (((([] ∷ Term) ∷ Term) ∷ Term) ∷ Term) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse {as = as} .((_ · _) · _) .(bubble (bubble (bubble p))) (step .(bubble (bubble p)) (step .(bubble p) (step⋆ {az = az} p q q₁ x₂) x₁) x) with <>>-cancel-both az (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p
bappTermLem ifThenElse {as = .[]} ((_ · _) · _) (bubble (bubble (bubble .(start (Type ∷ Term ∷ Term ∷ Term ∷ []))))) (step .(bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) (step⋆ {az = _} .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl x₂) x₁) x) | refl ,, refl = _ ,, _ ,, refl
bappTermLem ifThenElse .(_ · _) .(bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) (step⋆ (start .(Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl x₁) x) = _ ,, _ ,, refl
bappTermLem ifThenElse {as = as} .(_ · _) .(bubble (bubble (bubble p))) (step .(bubble (bubble p)) (step⋆ (bubble {as = as₁} p) q q₁ x₁) x) with <>>-cancel-both' as₁ (((([] ∷ _) ∷ Type) ∷ Term) ∷ Term) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term)as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse M .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) (step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl x) = _ ,, _ ,, refl
bappTermLem ifThenElse {as = as} M .(bubble (bubble (bubble p))) (step⋆ .(bubble (bubble p)) (step .(bubble p) (step {az = az} p q x₂) x₁) q₁ x) with <>>-cancel-both' az (((([] ∷ Term) ∷ Term) ∷ Type) ∷ Term) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse {as = as} M .(bubble (bubble (bubble p))) (step⋆ .(bubble (bubble p)) (step .(bubble p) (step⋆ {az = az} p q q₂ x₂) x₁) q₁ x) with <>>-cancel-both' az (((([] ∷ Type) ∷ Term) ∷ Type) ∷ Term) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse {as = as} M .(bubble (bubble (bubble p))) (step⋆ .(bubble (bubble p)) (step⋆ .(bubble p) (step {az = az} p q x₂) q₂ x₁) q₁ x) with <>>-cancel-both' az (((([] ∷ Term) ∷ Type) ∷ Type) ∷ Term) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse {as = as} M .(bubble (bubble (bubble p))) (step⋆ .(bubble (bubble p)) (step⋆ .(bubble p) (step⋆ {az = az} p q q₃ x₂) q₂ x₁) q₁ x) with <>>-cancel-both' az (((([] ∷ Type) ∷ Type) ∷ Type) ∷ Term) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem charToString {az = az} {as} M p q with <>>-cancel-both az ([] ∷ Term) as p
bappTermLem charToString {az = .[]} {.[]} .(ibuiltin charToString) .(start (Term ∷ [])) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem append _ _ base = _ ,, _ ,, refl
bappTermLem append {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] ∷ Term) ∷ Term) as p
bappTermLem append {as = .[]} (.(ibuiltin append) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem append {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Term) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTermLem trace {az = az} {as} M p q with <>>-cancel-both az ([] ∷ Term) as p
bappTermLem trace {az = .[]} {.[]} .(ibuiltin trace) .(start (Term ∷ [])) base | refl ,, refl = _ ,, _ ,, refl


bappTypeLem : ∀  b {A}{az as}(M : ∅ ⊢ A)(p : az <>> (Type ∷ as) ∈ arity b)
  → BAPP b p M → ∃ λ K → ∃ λ (B : ∅ ,⋆ K ⊢Nf⋆ *) → A ≡ Π B
bappTypeLem addInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem addInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTypeLem subtractInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem subtractInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTypeLem multiplyInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem multiplyInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTypeLem divideInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem divideInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTypeLem quotientInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem quotientInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()

bappTypeLem remainderInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem remainderInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem modInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem modInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem lessThanInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanEqualsInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem lessThanEqualsInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem greaterThanInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem greaterThanInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem greaterThanEqualsInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem greaterThanEqualsInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem equalsInteger {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem equalsInteger {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem concatenate {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem concatenate {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem takeByteString {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem takeByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem dropByteString {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem dropByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanByteString {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem lessThanByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem greaterThanByteString {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem greaterThanByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem sha2-256 {az = az} {as} M p q
  with <>>-cancel-both' az ([] ∷ Type) ([] ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem sha3-256 {az = az} {as} M p q
  with <>>-cancel-both' az ([] ∷ Type) ([] ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySignature {as = as} .((_ · _) · _) .(bubble (bubble p)) (step .(bubble p) (step {az = az} p q x₁) x)
  with <>>-cancel-both' az ((([] ∷ Term) ∷ Term) ∷ Type) ((([] ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySignature {as = as} .(_ · _) .(bubble (bubble p)) (step .(bubble p) (step⋆ {az = az} p q q₁ x₁) x)
  with <>>-cancel-both' az ((([] ∷ Type) ∷ Term) ∷ Type) ((([] ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySignature {as = as} M .(bubble (bubble p)) (step⋆ .(bubble p) (step {az = az} p q x₁) q₁ x) with <>>-cancel-both' az ((([] ∷ Term) ∷ Type) ∷ Type) ((([] ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySignature {as = as} M .(bubble (bubble p)) (step⋆ .(bubble p) (step⋆ {az = az} p q q₂ x₁) q₁ x) with <>>-cancel-both' az ((([] ∷ Type) ∷ Type) ∷ Type) ((([] ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem equalsByteString {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem equalsByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse .(ibuiltin ifThenElse) .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base = _ ,, _ ,, refl
bappTypeLem ifThenElse {as = as} .(((_ · _) · _) · _) .(bubble (bubble (bubble p))) (step .(bubble (bubble p)) (step .(bubble p) (step {az = az} p q x₂) x₁) x)
  with <>>-cancel-both' az (((([] ∷ Term) ∷ Term) ∷ Term) ∷ Type) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} .((_ · _) · _) .(bubble (bubble (bubble p))) (step .(bubble (bubble p)) (step .(bubble p) (step⋆ {az = az} p q q₁ x₂) x₁) x) with <>>-cancel-both' az (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Type) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} .(_ · _) .(bubble (bubble (bubble p))) (step .(bubble (bubble p)) (step⋆ .(bubble p) (step {az = az} p q x₂) q₁ x₁) x) with <>>-cancel-both' az (((([] ∷ Term) ∷ Type) ∷ Term) ∷ Type) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} .(_ · _) .(bubble (bubble (bubble p))) (step .(bubble (bubble p)) (step⋆ .(bubble p) (step⋆ {az = az} p q q₂ x₂) q₁ x₁) x)  with <>>-cancel-both' az (((([] ∷ Type) ∷ Type) ∷ Term) ∷ Type) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} M .(bubble (bubble (bubble p))) (step⋆ .(bubble (bubble p)) (step .(bubble p) (step {az = az} p q x₂) x₁) q₁ x)  with <>>-cancel-both' az (((([] ∷ Term) ∷ Term) ∷ Type) ∷ Type) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} M .(bubble (bubble (bubble p))) (step⋆ .(bubble (bubble p)) (step .(bubble p) (step⋆ {az = az} p q q₂ x₂) x₁) q₁ x)  with <>>-cancel-both' az (((([] ∷ Type) ∷ Term) ∷ Type) ∷ Type) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} M .(bubble (bubble (bubble p))) (step⋆ .(bubble (bubble p)) (step⋆ .(bubble p) (step {az = az} p q x₂) q₂ x₁) q₁ x)  with <>>-cancel-both' az (((([] ∷ Term) ∷ Type) ∷ Type) ∷ Type) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} M .(bubble (bubble (bubble p))) (step⋆ .(bubble (bubble p)) (step⋆ .(bubble p) (step⋆ {az = az} p q q₃ x₂) q₂ x₁) q₁ x) with <>>-cancel-both' az (((([] ∷ Type) ∷ Type) ∷ Type) ∷ Type) (((([] ∷ Type) ∷ Term) ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem charToString {az = az} {as} M p q
  with <>>-cancel-both' az ([] ∷ Type) ([] ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem append {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] ∷ Term) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem append {as = as} M .(bubble p) (step⋆ {az = az} p q q₁ x)
  with <>>-cancel-both' az (([] ∷ Type) ∷ Type) (([] ∷ Term) ∷ Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem trace {az = az} {as} M p q
  with <>>-cancel-both' az ([] ∷ Type) ([] ∷ Term) as p refl
... | refl ,, refl ,, ()

progress : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M
progress (ƛ M)        = done (V-ƛ M)
progress (M · M')     with progress M
... | error E-error = step (ruleErr ([] l· M'))
... | step (ruleEC E p refl refl) = step (ruleEC (E l· M') p refl refl)
... | step (ruleErr E) = step (ruleErr (E l· M'))
... | done VM with progress M'
... | step (ruleEC E p refl refl) = step (ruleEC (VM ·r E) p refl refl)
... | step (ruleErr E) = step (ruleErr (VM ·r E))
... | error E-error = step (ruleErr (VM ·r []))
progress (.(ƛ M) · M') | done (V-ƛ M) | done VM' =
  step (ruleEC [] (β-ƛ VM') refl refl)
progress (M · M') | done (V-I⇒ b {as' = []} p q) | done VM' =
  step (ruleEC [] (β-sbuiltin b M p q M' VM') refl refl)
progress (M · M') | done (V-I⇒ b {as' = Term ∷ as'} p q) | done VM'
  with bappTermLem b (M · M') (bubble p) (BApp2BAPP (step p q VM'))
... | _ ,, _ ,, refl = done (V-I⇒ b (bubble p) (BApp.step p q VM'))
progress (M · M') | done (V-I⇒ b {as' = Type ∷ as'} p q) | done VM'
  with bappTypeLem b (M · M') (bubble p) (BApp2BAPP (step p q VM'))
... | _ ,, _ ,, refl = done (V-IΠ b (bubble p) (BApp.step p q VM'))
progress (Λ M)        = done (V-Λ M)
progress (M ·⋆ A) with progress M
... | error E-error = step (ruleErr ([] ·⋆ A))
... | step (ruleEC E p refl refl) = step (ruleEC (E ·⋆ A) p refl refl)
... | step (ruleErr E) = step (ruleErr (E ·⋆ A))
... | done (V-Λ M') = step (ruleEC [] β-Λ refl refl)
progress (M ·⋆ A) | done (V-IΠ b {as' = []}         p q) =
  step (ruleEC [] (β-sbuiltin⋆ b M p q A) refl refl)
progress (M ·⋆ A) | done (V-IΠ b {as' = Term ∷ as'} p q)
  with bappTermLem b (M ·⋆ A) (bubble p) (BApp2BAPP (step⋆ p q))
... | _ ,, _ ,, X =
  done (convVal' X (V-I⇒ b (bubble p) (convBApp1 b X (step⋆ p q))))
progress (M ·⋆ A) | done (V-IΠ b {as' = Type ∷ as'} p q)
  with bappTypeLem b (M ·⋆ A) (bubble p) (BApp2BAPP (step⋆ p q))
... | _ ,, _ ,, X =
  done (convVal' X (V-IΠ b (bubble p) (convBApp1 b X (step⋆ p q))))
progress (wrap A B M) with progress M
... | done V            = done (V-wrap V)
... | step (ruleEC E p refl refl) = step (ruleEC (wrap E) p refl refl)
... | step (ruleErr E)  = step (ruleErr (wrap E))
... | error E-error     = step (ruleErr (wrap []))
progress (unwrap M) with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (unwrap E) p refl refl)
... | step (ruleErr E) = step (ruleErr (unwrap E))
... | done (V-wrap V) = step (ruleEC [] (β-wrap V) refl refl)
... | error E-error = step (ruleErr (unwrap []))
progress (con c)      = done (V-con c)
progress (ibuiltin b) = done (ival b)
progress (error A)    = error E-error

_↓ : ∀{A} → ∅ ⊢ A → Set
M ↓ = ∃ λ M' → M —→⋆ M'

-- progress in disguise
lemma51 : ∀{A}(M : ∅ ⊢ A)
        → Value M
        ⊎ ∃ λ B
        → ∃ λ (E : EC A B)
        → ∃ λ (L : ∅ ⊢ B)
        → (L ↓ ⊎ Error L)
        × M ≡ E [ L ]ᴱ 
lemma51 (ƛ M) = inj₁ (V-ƛ M)
lemma51 (M · M') with lemma51 M
... | inj₂ (B ,, E ,, L ,, p ,, q) = 
  inj₂ (B ,, E l· M' ,, L ,, p ,, cong (_· M') q)
... | inj₁ VM with lemma51 M'
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, VM ·r E ,, L ,, p ,, cong (M ·_) q)
lemma51 (.(ƛ M) · M') | inj₁ (V-ƛ M)      | inj₁ VM' =
  inj₂ (_ ,, [] ,, _ ,, inj₁ (_ ,, β-ƛ VM') ,, refl)
lemma51 (M · M') | inj₁ (V-I⇒ b {as' = []} p x) | inj₁ VM' =
  inj₂ (_ ,, [] ,, _ ,, inj₁ (_ ,, β-sbuiltin b M p x M' VM') ,, refl)
lemma51 (M · M') | inj₁ (V-I⇒ b {as' = Term ∷ as'} p x) | inj₁ VM'
  with bappTermLem b (M · M') (bubble p) (BApp2BAPP (step p x VM'))
... | _ ,, _ ,, refl = inj₁ (V-I⇒ b (bubble p) (step p x VM'))
lemma51 (M · M') | inj₁ (V-I⇒ b {as' = Type ∷ as'} p x) | inj₁ VM'
  with bappTypeLem b (M · M') (bubble p) (BApp2BAPP (step p x VM'))
... | _ ,, _ ,, refl = inj₁ (V-IΠ b (bubble p) (step p x VM'))
lemma51 (Λ M) = inj₁ (V-Λ M)
lemma51 (M ·⋆ A) with lemma51 M
... | inj₁ (V-Λ M') =
  inj₂ (_ ,, [] ,, M ·⋆ A ,, inj₁ (M' [ A ]⋆ ,, β-Λ) ,, refl)
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, E ·⋆ A ,, L ,, p ,, cong (_·⋆ A) q)
lemma51 (M ·⋆ A) | inj₁ (V-IΠ b {as' = []} p x) =
  inj₂ (_ ,, [] ,, _ ,, inj₁ (_ ,, β-sbuiltin⋆ b M p x A) ,, refl)
lemma51 (M ·⋆ A) | inj₁ (V-IΠ b {as' = Term ∷ as} p x)
  with bappTermLem b (M ·⋆ A) (bubble p) (BApp2BAPP (step⋆ p x))
... | _ ,, _ ,, q =
  inj₁ (convVal' q (V-I⇒ b (bubble p) (convBApp1 b q (step⋆ p x))))
lemma51 (M ·⋆ A) | inj₁ (V-IΠ b {as' = Type ∷ as} p x)
  with bappTypeLem b (M ·⋆ A) (bubble p) (BApp2BAPP (step⋆ p x))
... | _ ,, _ ,, q =
  inj₁ (convVal' q (V-IΠ b (bubble p) (convBApp1 b q (step⋆ p x))))
lemma51 (wrap A B M) with lemma51 M
... | inj₁ V = inj₁ (V-wrap V)
... | inj₂ (C ,, E ,, L ,, p ,, p') =
  inj₂ (C ,, wrap E ,, L ,, p ,, cong (wrap A B) p')
lemma51 (unwrap M) with lemma51 M
... | inj₁ (V-wrap V) =
  inj₂ (_ ,, [] ,, unwrap M ,, inj₁ (deval V ,, β-wrap V) ,, refl)
... | inj₂ (B ,, E ,, L ,, p ,, p') =
  inj₂ (B ,, unwrap E ,, L ,, p ,, cong unwrap p')
lemma51 (con c) = inj₁ (V-con c)
lemma51 (ibuiltin b) = inj₁ (ival b)
lemma51 (error _) = inj₂ (_ ,, ([] ,, (error _ ,, (inj₂ E-error) ,, refl)))

progress' : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M
progress' M with lemma51 M
... | inj₁ V = done V
... | inj₂ (B ,, E ,, L ,, inj₁ (M' ,, p) ,, refl) = step (ruleEC E p refl refl)
... | inj₂ (B ,, E ,, L ,, inj₂ E-error ,, refl) = step (ruleErr E)

data EProgress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{B}(E : EC A B){L L' : ∅ ⊢ B}
    → L —→⋆ L'
    → M ≡ E [ L ]ᴱ
      -------------
    → EProgress M
  done :
      Value M
      ----------
    → EProgress M

  error : ∀{B}(E : EC A B){L : ∅ ⊢ B} → Error L → M ≡ E [ L ]ᴱ
      -------
    → EProgress M

lemma51' : ∀{A}(M : ∅ ⊢ A) → EProgress M
lemma51' M with lemma51 M
... | inj₁ V = done V
... | inj₂ (B ,, E ,, L ,, inj₁ (M' ,, p) ,, p') = step E p p'
... | inj₂ (B ,, E ,, L ,, inj₂ e ,, p) = error E e p


uniqueVal : ∀{A}(M : ∅ ⊢ A)(v v' : Value M) → v ≡ v'

uniqueBApp : ∀{A b as az}
  → (p : az <>> as ∈ arity b)(M : ∅ ⊢ A)(v v' : BApp b p M) → v ≡ v'
uniqueBApp .(start (arity b)) (ibuiltin b) base base = refl
uniqueBApp .(bubble p) (M ·⋆ A) (step⋆ p v) (step⋆ .p v')
  with uniqueBApp p M v v'
... | refl = refl
uniqueBApp .(bubble p) (M · M') (step p v w) (step .p v' w')
  with uniqueBApp p M v v' | uniqueVal M' w w'
... | refl | refl = refl

subst<>>∈ : ∀{b b' as as' az az'}
  → az' <>> as' ∈ arity b'
  → b ≡ b' → az ≡ az' → as ≡ as'
  → az <>> as ∈ arity b
subst<>>∈ p refl refl refl = p

uniqueBApp' : ∀{A b b' as as' az az'}(M : ∅ ⊢ A)(p : az <>> as ∈ arity b)(p' : az' <>> as' ∈ arity b')(v : BApp b p M)(v' : BApp b' p' M)
  → ∃ λ (r : b ≡ b') → ∃ λ (r' : az ≡ az') → ∃ λ (r'' : as ≡ as')
  → p ≡ subst<>>∈ p' r r' r''
uniqueBApp' (ibuiltin b) .(start (arity _)) .(start (arity _)) base base =
  refl ,, refl ,, refl ,, refl
uniqueBApp' (M · M') .(bubble p) .(bubble p₁) (step p q x) (step p₁ q' x₁)
  with uniqueBApp' M p p₁ q q'
... | refl ,, refl ,, refl ,, refl = refl ,, refl ,, refl ,, refl
uniqueBApp' (M ·⋆ A) .(bubble p) .(bubble p₁) (step⋆ p q) (step⋆ p₁ q')
  with uniqueBApp' M p p₁ q q'
... | refl ,, refl ,, refl ,, refl = refl ,, refl ,, refl ,, refl

uniqueVal .(ƛ M) (V-ƛ M) (V-ƛ .M) = refl
uniqueVal .(Λ M) (V-Λ M) (V-Λ .M) = refl
uniqueVal .(wrap _ _ _) (V-wrap v) (V-wrap v') with uniqueVal _ v v'
... | refl = refl
uniqueVal .(con cn) (V-con cn) (V-con .cn) = refl
uniqueVal M (V-I⇒ b x y) (V-I⇒ b' x' y') with uniqueBApp' M x x' y y'
... | refl ,, refl ,, refl ,, refl = cong (V-I⇒ b x) (uniqueBApp x M y y')
uniqueVal M (V-IΠ b x y) (V-IΠ b' x' y')  with uniqueBApp' M x x' y y'
... | refl ,, refl ,, refl ,, refl = cong (V-IΠ b x) (uniqueBApp x M y y')

