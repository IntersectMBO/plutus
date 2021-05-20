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
data VALUE : ∀{A} → ∅ ⊢ A → Set where
  V-ƛ : {A B : ∅ ⊢Nf⋆ *}
    → (M : ∅ , A ⊢ B)
      ---------------------------
    → VALUE (ƛ M)

  V-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
    → (M : ∅ ,⋆ K ⊢ B)
      ----------------
    → VALUE (Λ M)

  V-wrap : ∀{K}
   → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : ∅ ⊢Nf⋆ K}
   → {M : ∅ ⊢  _}
   → VALUE M
   → VALUE (wrap A B M)

  V-con : ∀{tcn : TyCon}
    → (cn : TermCon (con tcn))
    → VALUE (con cn)

  V-I⇒ : ∀ b {A B C as as'}
       → (p : as <>> (Term ∷ as') ∈ arity b)
       → {t : ∅ ⊢ C}
       → (q : A ⇒ B ≡ C)
       → BApp b p t
       → VALUE t
  V-IΠ : ∀ b {A : ∅ ,⋆ K ⊢Nf⋆ *}{C}{as as'}
       → (p : as <>> (Type ∷ as') ∈ arity b)
       → {t : ∅ ⊢ C}
       → (q : Π A ≡ C)
       → BApp b p t
       → VALUE t


Value2VALUE : ∀{A}{M : ∅ ⊢ A} → Value M → VALUE M
Value2VALUE (V-ƛ M) = V-ƛ M
Value2VALUE (V-Λ M) = V-Λ M
Value2VALUE (V-wrap V) = V-wrap (Value2VALUE V)
Value2VALUE (V-con cn) = V-con cn
Value2VALUE (V-I⇒ b p x) = V-I⇒ b p refl x
Value2VALUE (V-IΠ b p x) = V-IΠ b p refl x

VALUE2Value : ∀{A}{M : ∅ ⊢ A} → VALUE M → Value M
VALUE2Value (V-ƛ M) = V-ƛ M
VALUE2Value (V-Λ M) = V-Λ M
VALUE2Value (V-wrap V) = V-wrap (VALUE2Value V)
VALUE2Value (V-con cn) = V-con cn
VALUE2Value (V-I⇒ b p refl x) = V-I⇒ b p x
VALUE2Value (V-IΠ b p refl x) = V-IΠ b p x


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

convBApp : (b : Builtin) → ∀{az}{as}(p p' : az <>> as ∈ arity b) → ∀{A}(t : ∅ ⊢ A) → BApp b p t → BApp b p' t
convBApp b p p' t q rewrite unique<>> p p' = q

BApp2BAPP : ∀{b : Builtin}{az}{as}{p : az <>> as ∈ arity b}{A}{t : ∅ ⊢ A}
  → BApp b p t → BAPP b p t
BApp2BAPP base         = base
BApp2BAPP (step p q v) = step p (BApp2BAPP q) v
BApp2BAPP (step⋆ p q)  = step⋆ p (BApp2BAPP q) refl refl


BUILTIN : ∀ b {A}{t : ∅ ⊢ A} → BAPP b (saturated (arity b)) t → ∅ ⊢ A
BUILTIN addInteger (step .(bubble (start (Term ∷ Term ∷ []))) (step .(start (Term ∷ Term ∷ [])) base (V-con (integer i))) (V-con (integer j))) = con (integer (i Data.Integer.+ j))
BUILTIN ifThenElse (step .(bubble (bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))))) (step .(bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) (step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl refl) (V-con (bool true))) t) f) = deval t
BUILTIN ifThenElse (step .(bubble (bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))))) (step .(bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) (step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl refl) (V-con (bool false))) t) f) = deval f
BUILTIN _ p = error _

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

data EC' : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  []   : {A : ∅ ⊢Nf⋆ *} → EC' A A
  _l·_ : {A B C : ∅ ⊢Nf⋆ *} → EC' (A ⇒ B) C → ∅ ⊢ A → EC' B C
  _·r_ : {A B C : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → EC' A C → EC' B C
  _·⋆_~_ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{C}{X}
    → EC' (Π B) C → (A : ∅ ⊢Nf⋆ K) → X ≡ B [ A ]Nf → EC' X C
  wrap : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}
    → EC' (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) C
    → EC' (μ A B) C
  unwrap : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}
    → EC' (μ A B) C
    → EC' (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) C
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
(wrap   E) [ L ]ᴱ = wrap _ _ (E [ L ]ᴱ)
(unwrap E) [ L ]ᴱ = unwrap (E [ L ]ᴱ)

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
          → ∀{M : ∅ ⊢ B}
          → M ≡ E [ error A ]ᴱ
            ------------------------
          → M —→ error B
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
... | error E-error = step (ruleErr ([] l· M') refl)
... | step (ruleEC E p refl refl) = step (ruleEC (E l· M') p refl refl)
... | step (ruleErr E refl) = step (ruleErr (E l· M') refl)
... | done VM with progress M'
... | step (ruleEC E p refl refl) = step (ruleEC (VM ·r E) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (VM ·r E) refl)
... | error E-error = step (ruleErr (VM ·r []) refl)
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
... | error E-error = step (ruleErr ([] ·⋆ A) refl)
... | step (ruleEC E p refl refl) = step (ruleEC (E ·⋆ A) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (E ·⋆ A) refl)
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
... | step (ruleErr E refl)  = step (ruleErr (wrap E) refl)
... | error E-error     = step (ruleErr (wrap []) refl)
progress (unwrap M) with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (unwrap E) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (unwrap E) refl)
... | done (V-wrap V) = step (ruleEC [] (β-wrap V) refl refl)
... | error E-error = step (ruleErr (unwrap []) refl)
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
... | inj₂ (B ,, E ,, L ,, inj₂ E-error ,, refl) = step (ruleErr E refl)

subst<>>∈ : ∀{b b' as as' az az'}
  → az' <>> as' ∈ arity b'
  → b ≡ b' → az ≡ az' → as ≡ as'
  → az <>> as ∈ arity b
subst<>>∈ p refl refl refl = p

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

lemV· : ∀{A B}{M : ∅ ⊢ A ⇒ B}{M'} → ¬ (Value M) → ¬ (Value (M · M'))
lemV· ¬VM (V-I⇒ b .(bubble p) (step p q VM')) = ⊥-elim (¬VM (V-I⇒ b p q))
lemV· ¬VM (V-IΠ b .(bubble p) (step p q VM')) = ⊥-elim (¬VM (V-I⇒ b p q))

lemV'· : ∀{A B}{M : ∅ ⊢ A ⇒ B}{M'} → ¬ (Value M') → ¬ (Value (M · M'))
lemV'· ¬VM' (V-I⇒ b .(bubble p) (step p q VM')) = ⊥-elim (¬VM' VM')
lemV'· ¬VM' (V-IΠ b .(bubble p) (step p q VM')) = ⊥-elim (¬VM' VM')

lemVunwrap :  ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{M}
  → ¬ (VALUE (unwrap {A = A}{B} M))
lemVunwrap (V-I⇒ b p q ())
lemVunwrap (V-IΠ b p q ())


lemV·⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ⊢ Π B}
  → ¬ (VALUE M) → ¬ (VALUE (M ·⋆ A))
lemV·⋆ ¬VM (V-I⇒ b .(bubble p) q (step⋆ p x)) = ¬VM (V-IΠ b p refl x)
lemV·⋆ ¬VM (V-IΠ b .(bubble p) q (step⋆ p x)) = ¬VM (V-IΠ b p refl x)

lemBAppβ : ∀{A B}{b}{az as}{p : az <>> as ∈ arity b}{M : ∅ , A ⊢ B}{M'}
  → ¬ (BApp b p (ƛ M · M'))
lemBAppβ (step p () x)

lemBAppβ⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{b}{az as}{p : az <>> as ∈ arity b}{M : ∅ ,⋆ K ⊢ B} → ¬ (BApp b p (Λ M ·⋆ A))
lemBAppβ⋆ (step⋆ p ())

lemVβ : ∀{A B}{M : ∅ , A ⊢ B}{M'} → ¬ (VALUE (ƛ M · M'))
lemVβ (V-I⇒ b p q x) = lemBAppβ x
lemVβ (V-IΠ b p q x) = lemBAppβ x

lemVβ⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ,⋆ K ⊢ B} → ¬ (VALUE (Λ M ·⋆ A))
lemVβ⋆ (V-I⇒ b p q x) = lemBAppβ⋆ x
lemVβ⋆ (V-IΠ b p q x) = lemBAppβ⋆ x

lemVE : ∀{A B} M (E : EC A B) → VALUE (E [ M ]ᴱ) → VALUE M
lemVE M [] V = V
lemVE M (E l· M') (V-I⇒ b .(bubble p) refl (step p x x₁)) =
  lemVE _ E (V-I⇒ b p refl x)
lemVE M (E l· M') (V-IΠ b .(bubble p) refl (step p x x₁)) =
  lemVE _ E (V-I⇒ b p refl x)
lemVE M (VM' ·r E) (V-I⇒ b .(bubble p) refl (step p x x₁)) =
  lemVE _ E (Value2VALUE x₁)
lemVE M (VM' ·r E) (V-IΠ b .(bubble p) refl (step p x x₁)) =
  lemVE _ E (Value2VALUE x₁)
lemVE M (E ·⋆ A) (V-I⇒ b .(bubble p) q (step⋆ p x)) =
  lemVE _ E (V-IΠ b p refl x)
lemVE M (E ·⋆ A) (V-IΠ b .(bubble p) q (step⋆ p x)) =
  lemVE _ E (V-IΠ b p refl x)
lemVE M (wrap E) (V-wrap V) = lemVE _ E V
lemVE M (unwrap E) (V-I⇒ b p q ())
lemVE M (unwrap E) (V-IΠ b p q ())

lemBE : ∀{A B} M (E : EC A B){as a az b}{p : az <>> (a ∷ as) ∈ arity b}
  → BApp b p (E [ M ]ᴱ) → VALUE M
lemBE M [] {a = Term} q with bappTermLem _ M _ (BApp2BAPP q)
... | _ ,, _ ,, refl = V-I⇒ _ _ refl q
lemBE M [] {a = Type} q with bappTypeLem _ M _ (BApp2BAPP q)
... | _ ,, _ ,, refl = V-IΠ _ _ refl q
lemBE M (E l· x) (step p q x₁) = lemBE _ E q
lemBE M (x ·r E) (step p q x₁) = lemVE _ E (Value2VALUE x₁)
lemBE M (E ·⋆ A) (step⋆ p q) = lemBE _ E q
lemBE M (wrap E) ()
lemBE M (unwrap E) ()

subst-l· : ∀{A B C C'}(E : EC (A ⇒ B) C)(M' : ∅ ⊢ A)(p : C ≡ C')
  → substEq (EC B) p (E l· M') ≡ substEq (EC (A ⇒ B)) p E l· M'
subst-l· E B refl = refl

subst-·r : ∀{A B C C'}(E : EC A C)(M : ∅ ⊢ A ⇒ B)(VM : Value M)(p : C ≡ C')
  → substEq (EC B) p (VM ·r E) ≡ VM ·r substEq (EC A) p E
subst-·r E M VM refl = refl


proj· : ∀{A A' B}{t : ∅ ⊢ A ⇒ B}{t' : ∅ ⊢ A' ⇒ B}{u : ∅ ⊢ A}{u' : ∅ ⊢ A'}
  → t _⊢_.· u ≡ t' · u'
  → ∃ λ (p : A ≡ A')
      → substEq (λ A → ∅ ⊢ A ⇒ B) p t ≡ t'
      × substEq (∅ ⊢_) p u ≡ u'
proj· refl = refl ,, refl ,, refl

valred : ∀{A}{L N : ∅ ⊢ A} → VALUE L → L —→⋆ N → ⊥
valred VL (β-ƛ VN) = lemVβ VL
valred VL β-Λ = lemVβ⋆ VL
valred VL (β-wrap VN) = lemVunwrap VL
valred (V-I⇒ b₁ .(bubble p₁) refl (step p₁ x x₁)) (β-sbuiltin b t p bt u vu)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl
valred (V-IΠ b₁ .(bubble p₁) refl (step p₁ x x₁)) (β-sbuiltin b t p bt u vu)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl
valred (V-I⇒ b₁ .(bubble p₁) q (step⋆ p₁ x)) (β-sbuiltin⋆ b t p bt A)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl
valred (V-IΠ b₁ .(bubble p₁) q (step⋆ p₁ x)) (β-sbuiltin⋆ b t p bt A)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl



bapperr : ∀{A}{L : ∅ ⊢ A}{b az as}{p : az <>> as ∈ arity b}
  → Error L → BApp b p L → ⊥
bapperr () base
bapperr () (step p bs x)
bapperr () (step⋆ p bs)

valerr : ∀{A}{L : ∅ ⊢ A} → Error L → Value L → ⊥
valerr E-error (V-I⇒ b p x) = bapperr E-error x
valerr E-error (V-IΠ b p x) = bapperr E-error x

errred : ∀{A}{L N : ∅ ⊢ A} → Error L → L —→⋆ N → ⊥
errred E-error ()

-- should replace this with something more general if something similar shows
-- up again
substƛVAL : ∀{A A' B}{M : ∅ , A ⊢ B} (p : A ≡ A')
  → VALUE (substEq (λ A → ∅ ⊢ (A ⇒ B)) p (ƛ M))
substƛVAL refl = V-ƛ _

BUILTIN-eq : ∀{A b b' az az'}(M : ∅ ⊢ A)(p : az <>> _ ∈ arity b)(p' : az' <>> _ ∈ arity b')(bv : BApp b p M)(bv' : BApp b' p' M)
  → BUILTIN' b p bv ≡ BUILTIN' b' p' bv'
BUILTIN-eq M p p' bv bv'
  with uniqueBApp' M p p' bv bv'
... | refl ,, refl ,, refl ,, refl
  with uniqueBApp p M bv bv'
... | refl = refl

{-
data EProgress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step :
      (Value M → ⊥)
    → ∀{B}(E : EC A B){L N : ∅ ⊢ B}
    → L —→⋆ N
    → M ≡ E [ L ]ᴱ
    → (∀{B'}(E' : EC A B'){L' N' : ∅ ⊢ B'} → L' —→⋆ N' → M ≡ E' [ L' ]ᴱ
                → ∃ λ (p : B ≡ B')
                    → substEq (EC A) p E ≡ E' × substEq (∅ ⊢_) p L ≡ L'
                    × substEq (∅ ⊢_) p N ≡ N')
      -------------
    
    → EProgress M
  done :
      Value M
      ----------
    → EProgress M

  error : ∀{B}(E : EC A B){L : ∅ ⊢ B} → Error L → M ≡ E [ L ]ᴱ
      -------
    → EProgress M


lemma51! : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A)
  → EProgress M
lemma51! (ƛ M) = done (V-ƛ M)
lemma51! (M · M') with lemma51! M
... | step ¬VM E p q U = step
  (lemV· ¬VM)
  (E l· M')
  p (cong (_· M') q)
  λ { [] {.(ƛ _ · M')} (β-ƛ VM') refl → ⊥-elim (¬VM (V-ƛ _))
    ; [] {.(M · M')} (β-sbuiltin b .M p bt .M' VM') refl →
      ⊥-elim (¬VM (V-I⇒ b p bt))
    ; (E' l· B) {L'} {N'} p' refl → let X ,, Y ,, Y' = U E' p' refl in
      X ,, trans (subst-l· E M' (proj₁ (U E' p' refl))) (cong (_l· M') Y) ,, Y'
    ; (VM ·r E') {L'} {N'} p' refl → ⊥-elim (¬VM VM)
    ; (E' ·⋆ A) {L'} {N'} p' ()
    ; (wrap E') {L'} {N'} p' ()
    ; (unwrap E') {L'} {N'} p' ()
    }
... | error E' e refl = error (E' l· M') e refl
... | done VM with lemma51! M'
... | step ¬VM' E p q U = step
  (lemV'· ¬VM')
  (VM ·r E)
  p
  (cong (M ·_) q)
  λ { [] (β-ƛ VM') refl → ⊥-elim (¬VM' VM') 
    ; [] (β-sbuiltin b .M p bt .M' VM') refl → ⊥-elim (¬VM' VM')
    ; (E' l· M'') p' refl → ⊥-elim (valred (lemVE _ _ (Value2VALUE VM)) p')
    ; (VM'' ·r E') p' refl → let X ,, X'' ,, X''' = U E' p' refl in X ,, trans (subst-·r E M VM X) (trans (cong (VM ·r_) X'') (cong (_·r E') (uniqueVal M VM VM''))) ,, X'''
    }
... | error E e refl = error (VM ·r E) e refl
lemma51! (.(ƛ M) · M') | done (V-ƛ M)       | done VM' = step
  (λ V → lemVβ (Value2VALUE V))
  []
  (β-ƛ VM')
  refl
  λ { [] (β-ƛ VM'') refl → refl ,, refl ,, refl ,, refl
    ; (E l· N) p q → let X ,, Y ,, Y' = proj· q in
      ⊥-elim (valred (lemVE _ E (substEq VALUE Y (substƛVAL X))) p)
    ; (V ·r E) p refl →
      ⊥-elim (valred (lemVE _ E (Value2VALUE VM')) p)}
lemma51! (M · M') | done (V-I⇒ b {as' = []}      p q) | done VM' = step
  (λ V → valred (Value2VALUE V) (β-sbuiltin b M p q M' VM'))
  -- ^ is there a more direct way?
  []
  (β-sbuiltin b M p q M' VM')
  refl
  λ { [] (β-sbuiltin b .M p bt .M' vu) refl
      → refl ,, refl ,, refl ,, BUILTIN-eq _ _ (bubble p) (step _ q VM') (step p bt vu)
    ; (E l· x) p' refl → ⊥-elim (valred (lemBE _ E q) p')
    ; (x ·r E) p' refl → ⊥-elim (valred (lemVE _ E (Value2VALUE VM')) p')}
lemma51! (M · M') | done (V-I⇒ b {as' = Term ∷ as'} p q) | done VM'
  with bappTermLem b (M · M') (bubble p) (BApp2BAPP (step p q VM'))
... | _ ,, _ ,, refl = done (V-I⇒ b (bubble p) (step p q VM'))
lemma51! (M · M') | done (V-I⇒ b {as' = Type ∷ as'} p q) | done VM'
  with bappTypeLem b (M · M') (bubble p) (BApp2BAPP (step p q VM'))
... | _ ,, _ ,, refl = done (V-IΠ b (bubble p) (step p q VM'))
lemma51! (Λ M) = done (V-Λ M)
lemma51! (M ·⋆ A) with lemma51! M
... | step ¬VM E p refl U = step
  (λ VM·⋆A → lemV·⋆ (λ VM → ¬VM (VALUE2Value VM)) (Value2VALUE VM·⋆A))
  (E ·⋆ A)
  p
  refl
  λ { E p q → {!U!}}
  where 
... | done (V-Λ L) = step
  (λ V → lemVβ⋆ (Value2VALUE V))
  []
  β-Λ
  refl
  λ {E p q → {!E!}}
lemma51! (M ·⋆ A) | done (V-IΠ b {as' = []} p x) = step
  (λ V → valred (Value2VALUE V) (β-sbuiltin⋆ b M p x A))
  []
  (β-sbuiltin⋆ b M p x A)
  refl
  λ {E p q → {!q!}}
lemma51! (M ·⋆ A) | done (V-IΠ b {as' = Term ∷ as'} p x)
  with bappTermLem b (M ·⋆ A) (bubble p) (BApp2BAPP (step⋆ p x))
... | _ ,, _ ,, X =
  done (convVal' X (V-I⇒ b (bubble p) (convBApp1 b X (step⋆ p x))))
lemma51! (M ·⋆ A) | done (V-IΠ b {as' = Type ∷ as'} p x)
  with bappTypeLem b (M ·⋆ A) (bubble p) (BApp2BAPP (step⋆ p x))
... | _ ,, _ ,, X =
  done (convVal' X (V-IΠ b (bubble p) (convBApp1 b X (step⋆ p x))))
lemma51! (M ·⋆ A) | error E e p = error (E ·⋆ A) e (cong (_·⋆ A) p)
lemma51! (wrap A B M) with lemma51! M
... | step ¬VM E p refl U = step
  (λ { (V-wrap VM) → ¬VM VM})
  (wrap E)
  p
  refl
  λ {E' p' q' → {!E'!}}
... | done VM = done (V-wrap VM)
... | error E e p = error (wrap E) e (cong (wrap A B) p)
lemma51! (unwrap M) with lemma51! M
... | step ¬VM E p refl U = step
  (λ V → lemVunwrap (Value2VALUE V))
  (unwrap E)
  p
  refl
  λ { E' p' q' → {!!}}
... | done (V-wrap VM) = step
  (λ V → lemVunwrap (Value2VALUE V))
  []
  (β-wrap VM)
  refl
  λ {E' p' q' → {!E'!}}
... | error E e p = error (unwrap E) e (cong unwrap p)
lemma51! (con c) = done (V-con c)
lemma51! (ibuiltin b) = done (ival b)
lemma51! (error _) = error [] E-error refl
-}

determinism⋆ : ∀{A}{L N N' : ∅ ⊢ A} → L —→⋆ N → L —→⋆ N' → N ≡ N'
determinism⋆ (β-ƛ _)                    (β-ƛ _)    = refl
determinism⋆ β-Λ                        β-Λ        = refl
determinism⋆ (β-wrap _)                 (β-wrap _) = refl
determinism⋆ (β-sbuiltin b t p bt u vu) (β-sbuiltin b' .t p' bt' .u vu') =
  BUILTIN-eq _ (bubble p) (bubble p') (step p bt vu) (step p' bt' vu')
determinism⋆ (β-sbuiltin⋆ b t p bt A)   (β-sbuiltin⋆ b' .t p' bt' .A) =
  BUILTIN-eq _ (bubble p) (bubble p') (step⋆ p bt) (step⋆ p' bt') 

data Redex {A : ∅ ⊢Nf⋆ *} : ∅ ⊢ A → Set where
  β   : {L N : ∅ ⊢ A} → L —→⋆ N → Redex L
  err : Redex (error A)

valredex : ∀{A}{L : ∅ ⊢ A} → VALUE L → Redex L → ⊥
valredex V (β r) = valred V r
valredex V err   = valerr E-error (VALUE2Value V)

data RProgress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step :
      (Value M → ⊥)
    → ∀{B}(E : EC A B){L : ∅ ⊢ B}
    → Redex L
    → M ≡ E [ L ]ᴱ
    → (∀{B'}
      → (E' : EC A B')
      → {L' : ∅ ⊢ B'}
      → M ≡ E' [ L' ]ᴱ
      → Redex L'
      → ∃ λ (p : B ≡ B')
      → substEq (EC A) p E ≡ E' × substEq (∅ ⊢_) p L ≡ L')
      ----------------------------------------------------
    → RProgress M
  done :
      Value M
      -----------
    → RProgress M

-- these negative things can probably be most easily proved via a less
-- rigid representation e.g, removing some green slime or even via
-- extrinsic typing

postulate
  lem-wrap-·⋆ : ∀{K'}{B' : ∅ ,⋆ K' ⊢Nf⋆ *}{B''}(E' : EC (Π B') B''){A'}{L'}
    → ∀{K}{A}{B : ∅ ⊢Nf⋆ K}{N} p
    → wrap A B N ≡ substEq (λ X → EC X B'') p (E' ·⋆ A') [ L' ]ᴱ
    → ⊥
  lem-wrap-unwrap : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}{B''}(E' : EC (μ A B) B''){L'}
    → ∀{K'}{A'}{B' : ∅ ⊢Nf⋆ K'}{N} p
    → wrap A' B' N ≡ substEq (λ X → EC X B'') p (unwrap E') [ L' ]ᴱ
    → ⊥


helper-wrap : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}(M : ∅ ⊢ _){B' B'' X : ∅ ⊢Nf⋆ *}{E}{L}
  → (E' : EC X B') {L' : ∅ ⊢ B'}
  → (p : X ≡ μ A B)
  → (U : {B' : ∅ ⊢Nf⋆ *} -- there should be a shorter way of writing this type!
      (E'
       : EC
         ((eval (embNf A) (λ x → reflect (` x)) ·V
           inj₂
           (λ v v₁ →
              μ
              (reify
               (eval (embNf (renNf S A))
                ((λ x → renVal v (reflect (` x))) ,,⋆ v₁)))
              (reify v₁)))
          ·V eval (embNf B) (λ x → reflect (` x)))
         B')
      {L' : ∅ ⊢ B'} →
      M ≡ (E' [ L' ]ᴱ) →
      Redex L' →
      ∃
      (λ p₁ →
         substEq
         (EC
          ((eval (embNf A) (λ x → reflect (` x)) ·V
            inj₂
            (λ ρ v →
               μ
               (reify
                (eval (embNf (renNf S A))
                 ((λ x → renVal ρ (reflect (` x))) ,,⋆ v)))
               (reify v)))
           ·V eval (embNf B) (λ x → reflect (` x))))
         p₁ E
         ≡ E'
         × substEq (_⊢_ ∅) p₁ L ≡ L'))
  → wrap A B M ≡ (substEq (λ X → EC X B') p E' [ L' ]ᴱ)
  → Redex L'
  → ∃ (λ (p₁ : B'' ≡ B') → substEq (EC (μ A B)) p₁ (wrap E) ≡ substEq (λ X → EC X B') p E'
    × substEq (_⊢_ ∅) p₁ L ≡ L')
helper-wrap M [] refl U refl (β ())
helper-wrap M (E' l· x) refl U () r
helper-wrap M (x ·r E') refl U () r
helper-wrap {A = A₁} M (_·⋆_ {B = B} E' A) p U q r =
  ⊥-elim (lem-wrap-·⋆ E' p q)
helper-wrap .(E' [ _ ]ᴱ) (wrap E') refl U refl r with U E' refl r
... | refl ,, refl ,, refl = refl ,, refl ,, refl
helper-wrap M (unwrap E') p U q r = ⊥-elim (lem-wrap-unwrap E' p q)

rlemma51! : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → RProgress M
rlemma51! (ƛ M)        = done (V-ƛ M)
rlemma51! (M · M') with rlemma51! M
... | step ¬VM E p q U = step
  (lemV· ¬VM)
  (E l· M')
  p
  (cong (_· M') q)
  λ { [] {.(ƛ _ · M')} refl (β (β-ƛ VM')) → ⊥-elim (¬VM (V-ƛ _))
    ; [] {.(M · M')} refl (β (β-sbuiltin b .M p bt .M' VM')) →
      ⊥-elim (¬VM (V-I⇒ b p bt))
    ; (E' l· B) {L'} refl p' → let X ,, Y ,, Y' = U E' refl p' in
      X ,, trans (subst-l· E M' (proj₁ (U E' refl p'))) (cong (_l· M') Y) ,, Y'
    ; (VM ·r E') {L'} refl p' → ⊥-elim (¬VM VM)
    ; (E' ·⋆ A) {L'} () p'
    ; (wrap E') {L'} () p'
    ; (unwrap E') {L'} () p'
    }
... | done VM with rlemma51! M'
... | step ¬VM' E p q U = step
  (lemV'· ¬VM')
  (VM ·r E)
  p
  (cong (M ·_) q)
  λ { [] refl (β (β-ƛ VM')) → ⊥-elim (¬VM' VM') 
    ; [] refl (β (β-sbuiltin b .M p bt .M' VM')) → ⊥-elim (¬VM' VM')
    ; (E' l· M'') refl p' → ⊥-elim (valredex (lemVE _ _ (Value2VALUE VM)) p')
    ; (VM'' ·r E') refl p' → let X ,, X'' ,, X''' = U E' refl p' in X ,, trans (subst-·r E M VM X) (trans (cong (VM ·r_) X'') (cong (_·r E') (uniqueVal M VM VM''))) ,, X'''
    }
rlemma51! (.(ƛ M) · M') | done (V-ƛ M)       | done VM' = step
  (λ V → lemVβ (Value2VALUE V))
  []
  (β (β-ƛ VM'))
  refl
  λ { [] refl (β (β-ƛ VM'')) → refl ,, refl ,, refl
    ; (E l· N) q p → let X ,, Y ,, Y' = proj· q in
      ⊥-elim (valredex (lemVE _ E (substEq VALUE Y (substƛVAL X))) p)
    ; (V ·r E) refl p →
      ⊥-elim (valredex (lemVE _ E (Value2VALUE VM')) p)}
rlemma51! (M · M') | done (V-I⇒ b {as' = []}      p q) | done VM' = step
  (λ V → valred (Value2VALUE V) (β-sbuiltin b M p q M' VM'))
  []
  (β (β-sbuiltin b M p q M' VM'))
  refl
  λ { [] refl (β (β-sbuiltin b .M p bt .M' vu)) → refl ,, refl ,, refl
    ; (E l· x) refl p' → ⊥-elim (valredex (lemBE _ E q) p')
    ; (x ·r E) refl p' → ⊥-elim (valredex (lemVE _ E (Value2VALUE VM')) p')}
rlemma51! (M · M') | done (V-I⇒ b {as' = Term ∷ as'} p q) | done VM'
  with bappTermLem b (M · M') (bubble p) (BApp2BAPP (step p q VM'))
... | _ ,, _ ,, refl = done (V-I⇒ b (bubble p) (step p q VM'))
rlemma51! (M · M') | done (V-I⇒ b {as' = Type ∷ as'} p q) | done VM'
  with bappTypeLem b (M · M') (bubble p) (BApp2BAPP (step p q VM'))
... | _ ,, _ ,, refl = done (V-IΠ b (bubble p) (step p q VM'))
rlemma51! (Λ M)        = done (V-Λ M)
rlemma51! (M ·⋆ A)     with rlemma51! M
... | done (V-Λ L)      = step
  (λ V → lemVβ⋆ (Value2VALUE V))
  []
  (β β-Λ)
  refl
  λ {E p q → {!!}}
... | step ¬VM E p q r = step
  (λ V → lemV·⋆ (λ V → ¬VM (VALUE2Value V)) (Value2VALUE V))
  (E ·⋆ A)
  p
  (cong (_·⋆ A) q)
  λ {E' p' q' → {!!}}
rlemma51! (M ·⋆ A) | done (V-IΠ b {as' = []} p x) = step
  (λ V → valred (Value2VALUE V) (β-sbuiltin⋆ b M p x A))
  []
  (β (β-sbuiltin⋆ b M p x A))
  refl
  λ {E p q → {!!}}
rlemma51! (M ·⋆ A) | done (V-IΠ b {as' = Term ∷ as'} p x)
  with bappTermLem b (M ·⋆ A) (bubble p) (BApp2BAPP (step⋆ p x))
... | _ ,, _ ,, X =
  done (convVal' X (V-I⇒ b (bubble p) (convBApp1 b X (step⋆ p x))))
rlemma51! (M ·⋆ A) | done (V-IΠ b {as' = Type ∷ as'} p x)
  with bappTypeLem b (M ·⋆ A) (bubble p) (BApp2BAPP (step⋆ p x))
... | _ ,, _ ,, X =
  done (convVal' X (V-IΠ b (bubble p) (convBApp1 b X (step⋆ p x))))
rlemma51! (wrap A B M) with rlemma51! M
... | done VM = done (V-wrap VM)
... | step ¬VM E p q U = step
  (λ {(V-wrap VM) → ¬VM VM})
  (wrap E)
  p
  (cong (wrap A B) q)
  λ E p q → helper-wrap M E refl U p q
rlemma51! (unwrap M) with rlemma51! M
... | step ¬VM E p q r = step
  (λ V → lemVunwrap (Value2VALUE V))
  (unwrap E)
  p
  (cong unwrap q)
  {!!}
... | done (V-wrap VM) = step
  (λ V → valred (Value2VALUE V) (β-wrap VM))
  []
  (β (β-wrap VM))
  refl
  λ {E p q → {!E!}}
rlemma51! (con c)      = done (V-con c)
rlemma51! (ibuiltin b) = done (ival b)
rlemma51! (error _)    = step
  (valerr E-error)
  []
  err
  refl
  λ { [] p q → refl ,, refl ,, p}

notVAL : ∀{A}{L N N' : ∅ ⊢ A} → Value L → L —→ N' → ⊥
notVAL V (ruleEC E p refl r) = valred (lemVE _ E (Value2VALUE V)) p
notVAL V (ruleErr E refl)    =
  valerr E-error (VALUE2Value (lemVE _ E (Value2VALUE V)))

determinism : ∀{A}{L N N' : ∅ ⊢ A} → L —→ N → L —→ N' → N ≡ N'
determinism {L = L} p q with rlemma51! L
determinism {L = .(E [ _ ]ᴱ)} (ruleEC E p refl p') q | done VL =
  ⊥-elim (valred (lemVE _ E (Value2VALUE VL)) p)
determinism {L = L} (ruleErr E refl)      q | done VL =
  ⊥-elim (valerr E-error (VALUE2Value (lemVE _ E (Value2VALUE VL))))
determinism {L = L} (ruleEC E' p p' p'') q | step ¬VL E r r' U
  with U E' p' (β p)
determinism {L = L} (ruleEC E p p' p'') (ruleEC E' q q' q'') | step ¬VL E (β r) r' U | refl ,, refl ,, refl with U E' q' (β q)
... | refl ,, refl ,, refl =
  trans p'' (trans (cong (E [_]ᴱ) (determinism⋆ p q)) (sym q''))
determinism {L = L} (ruleEC E p p' p'') (ruleErr E' q) | step ¬VL E (β r) r' U | refl ,, refl ,, refl with U E' q err
determinism {L = L} (ruleEC .(substEq (EC _) refl E) p p' p'') (ruleErr .E q) | step ¬VL E (β ()) r' U | refl ,, refl ,, refl | refl ,, refl ,, refl
determinism {L = L} (ruleErr E' p) q | step ¬VL E (β x) r' U
  with U E' p err
determinism {L = L} (ruleErr .E p) q | step ¬VL E (β ()) r' U | refl ,, refl ,, refl
determinism {L = L} (ruleErr E' p) (ruleEC E'' q q' q'') | step ¬VL E err r' U with U E'' q' (β q)
determinism {L = L} (ruleErr E' p) (ruleEC .E () q' q'') | step ¬VL E err r' U | refl ,, refl ,, refl
determinism {L = L} (ruleErr E' p) (ruleErr E'' q) | step ¬VL E err r' U with U E' p err | U E'' q err
... | refl ,, refl ,, refl | refl ,, refl ,, refl = refl
