```
module Algorithmic.ReductionEC where
```
## Imports

```
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to substEq)
open import Agda.Builtin.String using (primStringFromList; primStringAppend ; primStringEquality)
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
open import Agda.Builtin.String using (primStringAppend;primStringEquality)

open import Utils hiding (TermCon)
open import Type
import Type.RenamingSubstitution as T
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Algorithmic.Properties
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Builtin
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *)
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Data.Maybe using (just;from-just)
open import Data.String using (String)
open import Relation.Binary.HeterogeneousEquality using (_≅_;≡-subst-removable;refl;≡-to-≅;≅-to-≡;≅-to-subst-≡) renaming (sym to hsym; trans to htrans; cong to hcong)
```

```
{-# INJECTIVE _⊢_ #-}
{-# INJECTIVE _⊢Nf⋆_ #-}
```

## Values

```
data Value : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Set

data BApp (b : Builtin) : ∀{az}{as}
  → az <>> as ∈ arity b
  → ∀{A} → ∅ ⊢ A → Set where
  base : ∀{C}(p : C ≡ btype b) → BApp b (start (arity b)) (builtin b / p)
  step : ∀{A B}{az as}
    → (p : az <>> (Term ∷ as) ∈ arity b)
    → {t : ∅ ⊢ A ⇒ B} → BApp b p t
    → {u : ∅ ⊢ A} → Value u → BApp b (bubble p) (t · u)
  step⋆ : ∀{C B}{az as}
    → (p : az <>> (Type ∷ as) ∈ arity b)
    → {t : ∅ ⊢ Π B} → BApp b p t
    → {A : ∅ ⊢Nf⋆ K}
    → (q : C ≡ B [ A ]Nf)
    → BApp b (bubble p) (t ·⋆ A / q)

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

  V-con : ∀{tcn : TyCon ∅}
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
convBApp : (b : Builtin) → ∀{az}{as}(p p' : az <>> as ∈ arity b)
  → ∀{A}(t : ∅ ⊢ A)
  → BApp b p t
  → BApp b p' t
convBApp b p p' t q rewrite unique<>> p p' = q

BUILTIN : ∀ b {A}{t : ∅ ⊢ A} → BApp b (saturated (arity b)) t → ∅ ⊢ A
BUILTIN addInteger (step _ (step _ (base refl) (V-con (integer i))) (V-con (integer j))) = con (integer (i Data.Integer.+ j))
BUILTIN subtractInteger (step _ (step _ (base refl) (V-con (integer i))) (V-con (integer j))) = con (integer (i Data.Integer.- j))
BUILTIN multiplyInteger (step _ (step _ (base refl) (V-con (integer i))) (V-con (integer j))) = con (integer (i Data.Integer.* j))
BUILTIN divideInteger (step _ (step _ (base refl) (V-con (integer i))) (V-con (integer j)))
  with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = con (integer (div i j))
... | yes p = error _
BUILTIN quotientInteger (step _ (step _ (base refl) (V-con (integer i))) (V-con (integer j)))
  with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = con (integer (quot i j))
... | yes p = error _
BUILTIN remainderInteger (step _ (step _ (base refl) (V-con (integer i))) (V-con (integer j)))
  with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = con (integer (rem i j))
... | yes p = error _
BUILTIN modInteger (step _ (step _ (base refl) (V-con (integer i))) (V-con (integer j)))
  with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = con (integer (mod i j))
... | yes p = error _
BUILTIN lessThanInteger (step _ (step _ (base refl) (V-con (integer i))) (V-con (integer j)))
  with i <? j
... | no ¬p = con (bool false)
... | yes p = con (bool true)
BUILTIN lessThanEqualsInteger (step _ (step _ (base refl) (V-con (integer i))) (V-con (integer j)))
  with i ≤? j
... | no ¬p = con (bool false)
... | yes p = con (bool true)
BUILTIN equalsInteger (step _ (step _ (base refl) (V-con (integer i))) (V-con (integer j)))
  with i ≟ j
... | no ¬p = con (bool false)
... | yes p = con (bool true)
BUILTIN appendByteString (step _ (step _ (base refl) (V-con (bytestring b))) (V-con (bytestring b'))) =
  con (bytestring (concat b b'))
BUILTIN lessThanByteString (step _ (step _ (base refl) (V-con (bytestring b))) (V-con (bytestring b'))) =
  con (bool (B< b b'))
BUILTIN lessThanEqualsByteString (step _ (step _ (base refl) (V-con (bytestring b))) (V-con (bytestring b'))) = 
  con (bool (B> b b'))
BUILTIN sha2-256 (step _ (base refl) (V-con (bytestring b))) =
  con (bytestring (SHA2-256 b))
BUILTIN sha3-256 (step _ (base refl) (V-con (bytestring b))) =
  con (bytestring (SHA3-256 b))
BUILTIN blake2b-256 (step _ (base refl) (V-con (bytestring b))) =
  con (bytestring (BLAKE2B-256 b))
BUILTIN verifySignature (step _ (step _ (step _ (base refl) (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c)))
  with verifySig k d c
... | just b = con (bool b)
... | nothing = error _
BUILTIN equalsByteString (step _ (step _ (base refl) (V-con (bytestring b))) (V-con (bytestring b'))) =
  con (bool (equals b b'))
BUILTIN ifThenElse (step _ (step _ (step _ (step⋆ _ (base refl) refl) (V-con (bool true))) t) f) = deval t
BUILTIN ifThenElse (step _ (step _ (step _ (step⋆ _ (base refl) refl) (V-con (bool false))) t) f) = deval f
BUILTIN appendString (step _ (step _ (base refl) (V-con (string s))) (V-con (string s'))) =
  con (string (primStringAppend s s'))
BUILTIN trace (step _ (step _ (step⋆ _ (base refl) refl) (V-con (string s))) v) = TRACE s (deval v)
BUILTIN iData (step _ (base refl) (V-con (integer i))) = con (Data (iDATA i))
BUILTIN bData (step _ (base refl) (V-con (bytestring b))) = con (Data (bDATA b))
BUILTIN consByteString (step _ (step _ (base refl) (V-con (integer i))) (V-con (bytestring b))) = con (bytestring (cons i b))
BUILTIN sliceByteString (step _ (step _ (step _ (base refl) (V-con (integer st))) (V-con (integer n))) (V-con (bytestring b))) = con (bytestring (slice st n b))
BUILTIN lengthOfByteString (step _ (base refl) (V-con (bytestring b))) = con (integer (Builtin.length b))
BUILTIN indexByteString (step _ (step _ (base refl) (V-con (bytestring b))) (V-con (integer i)))
  with Data.Integer.ℤ.pos 0 ≤? i
... | no  _ = error _
... | yes _
  with i <? Builtin.length b
... | no _ =  error _
... | yes _ = con (integer (index b i))
BUILTIN equalsString (step _ (step _ (base refl) (V-con (string s))) (V-con (string s'))) =
  con (bool (primStringEquality s s'))
BUILTIN encodeUtf8 (step _ (base refl) (V-con (string s))) =
  con (bytestring (ENCODEUTF8 s))
BUILTIN decodeUtf8 (step _ (base refl) (V-con (bytestring b)))
  with DECODEUTF8 b
... | nothing = error _
... | just s  = con (string s)
BUILTIN unIData (step _ (base refl) (V-con (Data (iDATA i)))) = con (integer i)
BUILTIN unBData (step _ (base refl) (V-con (Data (bDATA b)))) = con (bytestring b)
BUILTIN _ _ = error _


BUILTIN' : ∀ b {A}{t : ∅ ⊢ A}{az}(p : az <>> [] ∈ arity b)
  → BApp b p t
  → ∅ ⊢ A
BUILTIN' b {t = t}{az = az} p q
  with sym (trans (cong ([] <><_) (sym (<>>2<>>' _ _ _ p))) (lemma<>2 az []))
... | refl = BUILTIN b (convBApp b p (saturated (arity b)) t q)
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
  _·⋆_/_ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{C}{X}
    → EC (Π B) C → (A : ∅ ⊢Nf⋆ K) → X ≡ B [ A ]Nf → EC X C
  wrap : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}
    → EC (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) C
    → EC (μ A B) C
  unwrap_/_ : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}{X}
    → EC (μ A B) C
    → X ≡ (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) 
    → EC X C
```

```
infix 2 _—→⋆_

data _—→⋆_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where
  β-ƛ : {A B : ∅ ⊢Nf⋆ *}{N : ∅ , A ⊢ B} {V : ∅ ⊢ A}
    → Value V
      -------------------
    → (ƛ N) · V —→⋆ N [ V ]

  β-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{N : ∅ ,⋆ K ⊢ B}{A}{C}
    → (p : C ≡ _)
      -------------------
    → (Λ N) ·⋆ A / p —→⋆ substEq (∅ ⊢_) (sym p) (N [ A ]⋆)

  β-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {C : _}
    → {M : ∅ ⊢ _}
    → Value M
    → (p : C ≡ _)
    → unwrap (wrap A B M) p —→⋆ substEq (∅ ⊢_) (sym p) M

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

  β-sbuiltin⋆ : ∀{B : ∅ ,⋆ K ⊢Nf⋆ *}{C}
      (b : Builtin)
    → (t : ∅ ⊢ Π B)
    → ∀{az}
    → (p : az <>> (Type ∷ []) ∈ arity b)
    → (bt : BApp b p t) -- one left
    → ∀ A
    → (q : C ≡ _)
      -----------------------------
    → t ·⋆ A / q —→⋆ BUILTIN' b (bubble p) (BApp.step⋆ p bt q)

infix 2 _—→_

_[_]ᴱ : ∀{A B : ∅ ⊢Nf⋆ *} → EC B A → ∅ ⊢ A → ∅ ⊢ B
[]       [ L ]ᴱ = L
(E l· B) [ L ]ᴱ = E [ L ]ᴱ · B
(V ·r E) [ L ]ᴱ = deval V · E [ L ]ᴱ
(E ·⋆ A / q) [ L ]ᴱ = E [ L ]ᴱ ·⋆ A / q
(wrap   E) [ L ]ᴱ = wrap _ _ (E [ L ]ᴱ)
(unwrap E / q) [ L ]ᴱ = unwrap (E [ L ]ᴱ) q

-- does this need to be heterogeneous?
lemΛE : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
  → ∀{L : ∅ ,⋆ K ⊢ B}{X}{L' : ∅ ⊢ X}{Y}
  → Y ≡ Π B
  → (E : EC Y X)
  → Λ L ≅ E [ L' ]ᴱ
  → E ≅ EC.[] {A = Y} × Λ L ≅ L'
lemΛE refl [] refl = refl ,, refl
lemΛE refl (E l· M) ()
lemΛE refl (x₂ ·r E) ()
lemΛE refl (E ·⋆ A / q) ()
lemΛE refl (unwrap E / q) ()

-- apparently not...
lemΛE' : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
  → ∀{L : ∅ ,⋆ K ⊢ B}{X}{L' : ∅ ⊢ X}
  → (E : EC (Π B) X)
  → Λ L ≡ E [ L' ]ᴱ
  → ∃ λ (p : X ≡ Π B)
  → substEq (EC (Π B)) p E ≡ EC.[] × Λ L ≡ substEq (∅ ⊢_) p L'
lemΛE' [] refl = refl ,, refl ,, refl

lemΛE'' : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
  → ∀{L : ∅ ,⋆ K ⊢ B}{X}{L' : ∅ ⊢ X}
  → (E : EC (Π B) X)
  → Λ L ≅ E [ L' ]ᴱ
  → ∃ λ (p : X ≡ Π B)
  → substEq (EC (Π B)) p E ≡ EC.[] × Λ L ≡ substEq (∅ ⊢_) p L'
lemΛE'' [] refl = refl ,, refl ,, refl

_[_]ᶠ : ∀{A B : ∅ ⊢Nf⋆ *} → Frame B A → ∅ ⊢ A → ∅ ⊢ B
(-· M') [ L ]ᶠ = L · M'
(V ·-)  [ L ]ᶠ = deval V · L
-·⋆ A   [ L ]ᶠ = L ·⋆ A / refl
wrap-   [ L ]ᶠ = wrap _ _ L
unwrap- [ L ]ᶠ = unwrap L refl

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
-- these two proofs are defined by pattern matching on the builtin,
-- they are very long and very ugly.  They could probably be made
-- shorter by giving cases for particular types/arities, and adding a
-- lemma that knocks off a more general class of imposible _<>>_∈_
-- inhabitants.

-- HINT: pattern matching on p rather than the next arg (q) generates
-- fewer cases
bappTermLem : ∀  b {A}{az as}(M : ∅ ⊢ A)(p : az <>> Term ∷ as ∈ arity b)
  → BApp b p M → ∃ λ A' → ∃ λ A'' → A ≡ A' ⇒ A''
bappTermLem addInteger _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem addInteger {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ ([] :< Term :< Term) as p refl
bappTermLem addInteger _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem subtractInteger _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem subtractInteger {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem subtractInteger _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem multiplyInteger _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem multiplyInteger {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem multiplyInteger _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem divideInteger _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem divideInteger {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem divideInteger _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem quotientInteger _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem quotientInteger {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem quotientInteger _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem remainderInteger _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem remainderInteger {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem remainderInteger _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem modInteger _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem modInteger {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem modInteger _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem lessThanInteger _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem lessThanInteger {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem lessThanInteger _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem lessThanEqualsInteger _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem lessThanEqualsInteger {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem lessThanEqualsInteger _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem equalsInteger _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem equalsInteger {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem equalsInteger _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem lessThanByteString _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem lessThanByteString {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem lessThanByteString _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem sha2-256 {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem sha2-256 _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem sha3-256 {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem sha3-256 _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem verifySignature _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem verifySignature _ (bubble (start _)) (step (start _) (base refl) _) =
  _ ,, _ ,, refl
bappTermLem verifySignature {as = as} _ (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Term) :< Term) :< Term) as p refl
bappTermLem verifySignature
            _
            (bubble (bubble (start _)))
            (step _ (step _ (base refl) _) _)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem equalsByteString _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem equalsByteString {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem equalsByteString _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem ifThenElse _ (bubble (start _)) (step⋆ (start _) (base refl) refl) =
  _ ,, _ ,, refl
bappTermLem ifThenElse
            _
            (bubble (bubble (start _)))
            (step _ (step⋆ _ (base refl) refl) _) = _ ,, _ ,, refl
bappTermLem ifThenElse _ (bubble (bubble (bubble {as = az} p))) q
  with <>>-cancel-both' az _ ([] <>< arity ifThenElse) _ p refl
bappTermLem ifThenElse
            _
            (bubble (bubble (bubble (start _))))
            (step _ (step _ (step⋆ _ (base refl) refl) _) _)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem trace {as = .(Term ∷ [])} _ (bubble (start .(Type ∷ Term ∷ Term ∷ []))) (step⋆ .(start (Type ∷ Term ∷ Term ∷ [])) (base refl) refl) = _ ,, _ ,, refl
bappTermLem trace {as = as} _ (bubble (bubble {as = az} p)) q with <>>-cancel-both' az _ ([] <>< arity trace) _ p refl
bappTermLem trace {as = .[]} _ (bubble (bubble {as = _} (start .(Type ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Type ∷ Term ∷ Term ∷ []))) (step⋆ .(start (Type ∷ Term ∷ Term ∷ [])) (base refl) refl) x) | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem equalsString _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem equalsString {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem equalsString _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem encodeUtf8 {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem encodeUtf8 _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem decodeUtf8 {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem decodeUtf8 _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem fstPair _ (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ([] <>< arity fstPair) _ p refl
bappTermLem fstPair
            _
            (bubble (bubble (start _)))
            (step⋆ _ (step⋆ _ (base refl) refl) refl)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem sndPair _ (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ([] <>< arity fstPair) _ p refl
bappTermLem sndPair
            _
            (bubble (bubble (start _)))
            (step⋆ _ (step⋆ _ (base refl) refl) refl)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem nullList _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ ([] <>< arity nullList) _ p refl
bappTermLem nullList _ (bubble (start _)) (step⋆ _ (base refl) refl)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem headList _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ ([] <>< arity nullList) _ p refl
bappTermLem headList _ (bubble (start _)) (step⋆ _ (base refl) refl)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem tailList _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ ([] <>< arity nullList) _ p refl
bappTermLem tailList _ (bubble (start _)) (step⋆ _ (base refl) refl)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem chooseList
            _
            (bubble (bubble (start _)))
            (step⋆ _ (step⋆ _ (base refl) refl) refl)
            = _ ,, _ ,, refl
bappTermLem chooseList
            _
            (bubble (bubble (bubble (start _))))
            (step _ (step⋆ _ (step⋆ _ (base refl) refl) refl) x)
            = _ ,, _ ,, refl
bappTermLem chooseList _ (bubble (bubble (bubble (bubble {as = az} p)))) q
  with <>>-cancel-both' az _ ([] <>< arity chooseList) _ p refl
bappTermLem chooseList
            _
            (bubble (bubble (bubble (bubble (start _)))))
            (step _ (step _ (step⋆ _ (step⋆ _ (base refl) refl) refl) _) _)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem constrData _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem constrData {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem constrData _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem mapData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem mapData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem listData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem listData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem iData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem iData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem bData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem bData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem unConstrData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem unConstrData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem unMapData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem unMapData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem unListData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem unListData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem unIData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem unIData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem unBData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem unBData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem equalsData _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem equalsData {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem equalsData _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem chooseData _ (bubble (start _)) (step⋆ _ (base refl) refl) =
  _ ,, _ ,, refl
bappTermLem chooseData
            _
            (bubble (bubble (start _)))
            (step _ (step⋆ _ (base refl) refl) _)
            = _ ,, _ ,, refl
bappTermLem chooseData
            _
            (bubble (bubble (bubble (start _))))
            (step _ (step _ (step⋆ _ (base refl) refl) _) _)
            = _ ,, _ ,, refl
bappTermLem chooseData
            _
            (bubble (bubble (bubble (bubble (start _)))))
            (step _ (step _ (step _ (step⋆ _ (base refl) refl) _) _) _)
            = _ ,, _ ,, refl
bappTermLem chooseData
            _
            (bubble (bubble (bubble (bubble (bubble (start _))))))
            (step _ (step _ (step _ (step _ (step⋆ _ (base refl) refl) _) _) _) _)
            = _ ,, _ ,, refl
bappTermLem chooseData
            _
            (bubble (bubble (bubble (bubble (bubble (bubble {as = az} p)))))) q
  with <>>-cancel-both' az _ ([] <>< arity chooseData) _ p refl
bappTermLem
  chooseData
  _
  (bubble (bubble (bubble (bubble (bubble (bubble (start _)))))))
  (step _ (step _ (step _ (step _ (step _ (step⋆ _ (base refl) refl)_)_)_)_)_)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem chooseUnit _ (bubble (start _)) (step⋆ _ (base refl) refl) =
  _ ,, _ ,, refl
bappTermLem chooseUnit _ (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Type) :< Term) :< Term) _ p refl
bappTermLem chooseUnit
            _
            (bubble (bubble (start _)))
            (step _ (step⋆ _ (base refl) refl) x)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem mkPairData _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem mkPairData {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem mkPairData _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem mkNilData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem mkNilData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem mkNilPairData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem mkNilPairData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem mkCons _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem mkCons {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem mkCons _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem appendByteString _ _ (base refl) = _ ,, _ ,, refl
bappTermLem appendByteString {as = as} (M · M') .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem appendByteString {as = .[]} (.(builtin appendByteString / refl) · M') (bubble (start .(Term ∷ Term ∷ []))) (step {az = _} (start .(Term ∷ Term ∷ [])) (base refl) x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem appendByteString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem lessThanEqualsByteString _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem lessThanEqualsByteString {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem lessThanEqualsByteString _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem appendString _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem appendString {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem appendString _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem consByteString _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem consByteString {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem consByteString _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem sliceByteString _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem sliceByteString _ (bubble (start _)) (step (start _) (base refl) _) =
  _ ,, _ ,, refl
bappTermLem sliceByteString {as = as} _ (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Term) :< Term) :< Term) as p refl
bappTermLem sliceByteString
            _
            (bubble (bubble (start _)))
            (step _ (step _ (base refl) _) _)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem lengthOfByteString {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem lengthOfByteString _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
bappTermLem indexByteString _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem indexByteString {as = as} _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem indexByteString _ (bubble (start _)) (step _ (base refl) _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem blake2b-256 {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem blake2b-256 _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl

bappTypeLem : ∀  b {A}{az as}(M : ∅ ⊢ A)(p : az <>> (Type ∷ as) ∈ arity b)
  → BApp b p M → ∃ λ K → ∃ λ (B : ∅ ,⋆ K ⊢Nf⋆ *) → A ≡ Π B
bappTypeLem addInteger _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem subtractInteger _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem multiplyInteger _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem divideInteger _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem quotientInteger _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem remainderInteger _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem modInteger _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanInteger _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanEqualsInteger _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem equalsInteger _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanByteString _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem sha2-256 {az = az} _ p _
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem sha3-256 {az = az} _ p _
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem verifySignature _ (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ([] <>< arity verifySignature) _ p refl
... | refl ,, refl ,, ()
bappTypeLem equalsByteString _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem ifThenElse _ (bubble (bubble (bubble {as = az} p))) _
  with <>>-cancel-both' az _ ([] <>< arity ifThenElse) _ p refl
... | _ ,, _ ,, ()
bappTypeLem trace _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem trace M (bubble (bubble {as = az} p)) q with <>>-cancel-both' az _ ([] <>< arity trace) _ p refl
... | _ ,, _ ,, ()
bappTypeLem equalsString _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem encodeUtf8 {az = az} _ p _
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem decodeUtf8 {az = az} _ p _
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem fstPair _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem fstPair _ (bubble (start _)) (step⋆ _ (base refl) refl) =
  _ ,, _ ,, refl
bappTypeLem fstPair _ (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ((([] :< Type) :< Type) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem sndPair _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem sndPair _ (bubble (start _)) (step⋆ _ (base refl) refl) =
  _ ,, _ ,, refl
bappTypeLem sndPair _ (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ((([] :< Type) :< Type) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem bData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem unConstrData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem unMapData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem unListData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem unIData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem unBData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem equalsData _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem chooseData _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem chooseData _ (bubble (bubble (bubble (bubble (bubble (bubble {as = az} p)))))) _
  with <>>-cancel-both' az _ ([] <>< arity chooseData) _ p refl
... | _ ,, _ ,, ()
bappTypeLem chooseUnit _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem chooseUnit _ (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ([] <>< arity chooseUnit) _ p refl
... | _ ,, _ ,, ()
bappTypeLem mkPairData _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem mkNilData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem mkNilPairData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem appendString {as = as} .(_ · _) .(bubble p) (step {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem appendString {as = as} M .(bubble p) (step⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem mkCons _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem nullList _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem nullList _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Type) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem headList _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem headList _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Type) :< Term) _ p refl
... | refl ,, refl ,, ()  
bappTypeLem tailList _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem tailList _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Type) :< Term) _ p refl
... | refl ,, refl ,, ()  
bappTypeLem chooseList _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem chooseList _ (bubble (start _)) (step⋆ _ (base refl) refl) =
  _ ,, _ ,, refl
bappTypeLem chooseList _ (bubble (bubble (bubble (bubble {as = az} p)))) _
  with <>>-cancel-both' az _ ([] <>< arity chooseList) _ p refl
... | _ ,, _ ,, ()
bappTypeLem appendByteString _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem constrData _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem mapData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem listData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem iData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanEqualsByteString _ (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem consByteString _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem sliceByteString _ (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Term) :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem lengthOfByteString {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem indexByteString _ (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem blake2b-256 {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()

-- a smart constructor that looks at the arity and then puts on the
-- right constructor
V-I : ∀ b {A : ∅ ⊢Nf⋆ *}{a as as'}
       → (p : as <>> a ∷ as' ∈ arity b)
       → {t : ∅ ⊢ A}
       → BApp b p t
       → Value t
V-I b {a = Term} p q with bappTermLem b _ p q
... | _ ,, _ ,, refl = V-I⇒ b p q
V-I b {a = Type} p q  with bappTypeLem b _ p q
... | _ ,, _ ,, refl = V-IΠ b p q

ival : ∀ b → Value (builtin b / refl)

-- ival b = V-I b (start _) (base refl)
-- ^ not possible as we could have a builtin with no args

ival addInteger = V-I⇒ addInteger (start _) (base refl) 
ival subtractInteger = V-I⇒ subtractInteger (start _) (base refl) 
ival multiplyInteger = V-I⇒ multiplyInteger (start _) (base refl) 
ival divideInteger = V-I⇒ divideInteger (start _) (base refl) 
ival quotientInteger = V-I⇒ quotientInteger (start _) (base refl) 
ival remainderInteger = V-I⇒ remainderInteger (start _) (base refl) 
ival modInteger = V-I⇒ modInteger (start _) (base refl) 
ival lessThanInteger = V-I⇒ lessThanInteger (start _) (base refl) 
ival lessThanEqualsInteger = V-I⇒ lessThanEqualsInteger (start _) (base refl) 
ival lessThanByteString = V-I⇒ lessThanByteString (start _) (base refl) 
ival sha2-256 = V-I⇒ sha2-256 (start _) (base refl) 
ival sha3-256 = V-I⇒ sha3-256 (start _) (base refl) 
ival verifySignature = V-I⇒ verifySignature (start _) (base refl) 
ival equalsByteString = V-I⇒ equalsByteString (start _) (base refl) 
ival ifThenElse = V-IΠ ifThenElse (start _) (base refl) 
ival trace = V-IΠ trace (start _) (base refl) 
ival equalsString = V-I _ (start _) (base refl)
ival encodeUtf8 = V-I _ (start _) (base refl)
ival decodeUtf8 = V-I _ (start _) (base refl)
ival fstPair = V-I _ (start _) (base refl)
ival sndPair = V-I _ (start _) (base refl)
ival nullList = V-I _ (start _) (base refl)
ival headList = V-I _ (start _) (base refl)
ival tailList = V-I _ (start _) (base refl)
ival chooseList = V-I _ (start _) (base refl)
ival constrData = V-I _ (start _) (base refl)
ival mapData = V-I _ (start _) (base refl)
ival listData = V-I _ (start _) (base refl)
ival iData = V-I _ (start _) (base refl)
ival bData = V-I _ (start _) (base refl)
ival unConstrData = V-I _ (start _) (base refl)
ival unMapData = V-I _ (start _) (base refl)
ival unListData = V-I _ (start _) (base refl)
ival unIData = V-I _ (start _) (base refl)
ival unBData = V-I _ (start _) (base refl)
ival equalsData = V-I _ (start _) (base refl)
ival chooseData = V-I _ (start _) (base refl)
ival chooseUnit = V-I _ (start _) (base refl)
ival mkPairData = V-I _ (start _) (base refl)
ival mkNilData = V-I _ (start _) (base refl)
ival mkNilPairData = V-I _ (start _) (base refl)
ival mkCons = V-I _ (start _) (base refl)
ival equalsInteger = V-I⇒ equalsInteger (start _) (base refl)
ival appendByteString = V-I⇒ appendByteString (start _) (base refl)
ival appendString = V-I⇒ appendString (start _) (base refl)
ival lessThanEqualsByteString = V-I⇒ lessThanEqualsByteString (start _) (base refl)
ival consByteString = V-I⇒ consByteString (start _) (base refl)
ival sliceByteString = V-I⇒ sliceByteString (start _) (base refl)
ival lengthOfByteString = V-I⇒ lengthOfByteString (start _) (base refl)
ival indexByteString = V-I⇒ indexByteString (start _) (base refl)
ival blake2b-256 = V-I⇒ blake2b-256 (start _) (base refl)

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
progress (M · M') | done (V-I⇒ b {as' = a ∷ as'} p q) | done VM' =
  done (V-I b (bubble p) (step p q VM'))
progress (Λ M)        = done (V-Λ M)
progress (M ·⋆ A / refl) with progress M
... | error E-error = step (ruleErr ([] ·⋆ A / refl) refl)
... | step (ruleEC E p refl refl) = step (ruleEC (E ·⋆ A / refl) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (E ·⋆ A / refl) refl)
... | done (V-Λ M') = step (ruleEC [] (β-Λ refl) refl refl)
progress (M ·⋆ A / r) | done (V-IΠ b {as' = []}         p q) =
  step (ruleEC [] (β-sbuiltin⋆ b M p q A refl) refl refl)
progress (M ·⋆ A / refl) | done (V-IΠ b {as' = a ∷ as'} p q) =
  done (V-I b (bubble p) (step⋆ p q refl))
progress (wrap A B M) with progress M
... | done V            = done (V-wrap V)
... | step (ruleEC E p refl refl) = step (ruleEC (wrap E) p refl refl)
... | step (ruleErr E refl)  = step (ruleErr (wrap E) refl)
... | error E-error     = step (ruleErr (wrap []) refl)
progress (unwrap M refl) with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (unwrap E / refl) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (unwrap E / refl) refl)
... | done (V-wrap V) = step (ruleEC [] (β-wrap V refl) refl refl)
... | error E-error = step (ruleErr (unwrap [] / refl) refl)
progress (con c)      = done (V-con c)
progress (builtin b / refl) = done (ival b)
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
lemma51 (M · M') | inj₁ (V-I⇒ b {as' = a ∷ as'} p x) | inj₁ VM' =
  inj₁ (V-I b (bubble p) (step p x VM'))
lemma51 (Λ M) = inj₁ (V-Λ M)
lemma51 (M ·⋆ A / refl) with lemma51 M
... | inj₁ (V-Λ M') =
  inj₂ (_ ,, [] ,, M ·⋆ A / refl ,, inj₁ (M' [ A ]⋆ ,, (β-Λ refl)) ,, refl)
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, E ·⋆ A / refl ,, L ,, p ,, cong (_·⋆ A / refl) q)
lemma51 (M ·⋆ A / refl) | inj₁ (V-IΠ b {as' = []} p x) =
  inj₂ (_ ,, [] ,, _ ,, inj₁ (_ ,, β-sbuiltin⋆ b M p x A refl) ,, refl)
lemma51 (M ·⋆ A / refl) | inj₁ (V-IΠ b {as' = a ∷ as} p x) =
  inj₁ (V-I b (bubble p) (step⋆ p x refl))
lemma51 (wrap A B M) with lemma51 M
... | inj₁ V = inj₁ (V-wrap V)
... | inj₂ (C ,, E ,, L ,, p ,, p') =
  inj₂ (C ,, wrap E ,, L ,, p ,, cong (wrap A B) p')
lemma51 (unwrap M refl) with lemma51 M
... | inj₁ (V-wrap V) =
  inj₂ (_ ,, [] ,, unwrap M refl ,, inj₁ (deval V ,, β-wrap V refl) ,, refl)
... | inj₂ (B ,, E ,, L ,, p ,, p') =
  inj₂ (B ,, unwrap E / refl ,, L ,, p ,, cong (λ x → unwrap x refl) p')
lemma51 (con c) = inj₁ (V-con c)
lemma51 (builtin b / refl) = inj₁ (ival b)
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
uniqueBApp .(start (arity b)) (builtin b / refl) (base refl) (base refl) = refl
uniqueBApp .(bubble p) (M ·⋆ A / refl) (step⋆ p v refl) (step⋆ .p v' refl)
  with uniqueBApp p M v v'
... | refl = refl
uniqueBApp .(bubble p) (M · M') (step p v w) (step .p v' w')
  with uniqueBApp p M v v' | uniqueVal M' w w'
... | refl | refl = refl

uniqueBApp' : ∀{A b b' as as' az az'}(M : ∅ ⊢ A)(p : az <>> as ∈ arity b)(p' : az' <>> as' ∈ arity b')(v : BApp b p M)(v' : BApp b' p' M)
  → ∃ λ (r : b ≡ b') → ∃ λ (r' : az ≡ az') → ∃ λ (r'' : as ≡ as')
  → p ≡ subst<>>∈ p' r r' r''
uniqueBApp' (builtin b / refl) .(start (arity b)) .(start (arity b)) (base refl) (base  refl) =
  refl ,, refl ,, refl ,, refl
uniqueBApp' (M · M') .(bubble p) .(bubble p₁) (step p q x) (step p₁ q' x₁)
  with uniqueBApp' M p p₁ q q'
... | refl ,, refl ,, refl ,, refl = refl ,, refl ,, refl ,, refl
uniqueBApp' (M ·⋆ A / refl) .(bubble p) .(bubble p₁) (step⋆ p q refl) (step⋆ p₁ q' refl)
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

lemVunwrap :  ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}{q : C ≡ _}{M}
  → ¬ (Value (unwrap {A = A}{B} M q))
lemVunwrap (V-I⇒ b p ())
lemVunwrap (V-IΠ b p ())

lemV·⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ⊢ Π B}{C}{p : C ≡ B [ A ]Nf}
  → ¬ (Value M) → ¬ (Value (M ·⋆ A / p))
lemV·⋆ ¬VM (V-I⇒ b .(bubble p) (step⋆ p q r)) = ¬VM (V-IΠ b p q)
lemV·⋆ ¬VM (V-IΠ b .(bubble p) (step⋆ p q r)) = ¬VM (V-IΠ b p q)

lemBAppβ : ∀{A B}{b}{az as}{p : az <>> as ∈ arity b}{M : ∅ , A ⊢ B}{M'}
  → ¬ (BApp b p (ƛ M · M'))
lemBAppβ (step p () x)

lemBAppβ⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{b}{az as}{p : az <>> as ∈ arity b}{M : ∅ ,⋆ K ⊢ B}{C}{q : C ≡ B [ A ]Nf} → ¬ (BApp b p (Λ M ·⋆ A / q))
lemBAppβ⋆ (step⋆ p () refl)

lemVβ : ∀{A B}{M : ∅ , A ⊢ B}{M'} → ¬ (Value (ƛ M · M'))
lemVβ (V-I⇒ b p q) = lemBAppβ q
lemVβ (V-IΠ b p q) = lemBAppβ q

lemVβ⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ,⋆ K ⊢ B}{C}{p : C ≡ B [ A ]Nf}
  → ¬ (Value (Λ M ·⋆ A / p))
lemVβ⋆ (V-I⇒ b p q) = lemBAppβ⋆ q
lemVβ⋆ (V-IΠ b p q) = lemBAppβ⋆ q


postulate lemVE : ∀{A B} M (E : EC A B) → Value (E [ M ]ᴱ) → Value M

{-
This currently triggers an agda bug:
Panic: Pattern match failure in do expression at
src/full/Agda/TypeChecking/Rules/LHS/Unify.hs:1313:7-14
when checking that the pattern V-I⇒ b p q has type
Value ((x ·r E) [ M ]ᴱ)

lemVE M []             V = V
lemVE M (x ·r E) (V-I⇒ b p q) = ?
lemVE M (x ·r E) (V-IΠ b p q) = ?
lemVE M (E l· x) (V-I⇒ b .(bubble p) (step p x₁ x₂)) = lemVE _ E (V-I⇒ b p x₁)
lemVE M (E l· x) (V-IΠ b .(bubble p) (step p x₁ x₂)) = lemVE _ E (V-I⇒ b p x₁)
lemVE M (E ·⋆ A / x)   V = {!!}
lemVE M (wrap E)       V = {!!}
lemVE M (unwrap E / x) V = {!!}
{-
lemVE M [] V = V
lemVE M (E l· M') (V-I⇒ b .(bubble p) (step p x x₁)) =
  lemVE _ E (V-I⇒ b p x)
lemVE M (E l· M') (V-IΠ b .(bubble p) (step p x x₁)) =
  lemVE _ E (V-I⇒ b p x)
lemVE M (VM' ·r E) (V-I⇒ b .(bubble p) (step p x x₁)) =
  lemVE _ E x₁
lemVE M (VM' ·r E) (V-IΠ b .(bubble p) (step p x x₁)) =
  lemVE _ E x₁
lemVE M (E ·⋆ A / refl) (V-I⇒ b .(bubble p) q (step⋆ p x)) =
  lemVE _ E (V-IΠ b p refl x)
lemVE M (E ·⋆ A / refl) (V-IΠ b .(bubble p) q (step⋆ p x)) =
  lemVE _ E (V-IΠ b p refl x)
lemVE M (wrap E) (V-wrap V) = lemVE _ E V
lemVE M (unwrap E) (V-I⇒ b p q ())
lemVE M (unwrap E) (V-IΠ b p q ())
-}
-}

lemBE : ∀{A B} M (E : EC A B){as a az b}{p : az <>> (a ∷ as) ∈ arity b}
  → BApp b p (E [ M ]ᴱ) → Value M
lemBE M [] {a = Term} q with bappTermLem _ M _ q
... | _ ,, _ ,, refl = V-I⇒ _ _ q
lemBE M [] {a = Type} q with bappTypeLem _ M _ q
... | _ ,, _ ,, refl = V-IΠ _ _ q
lemBE M (E l· x) (step p q x₁) = lemBE _ E q
lemBE M (x ·r E) (step p q x₁) = lemVE _ E x₁
lemBE M (E ·⋆ A / r) (step⋆ p q refl) = lemBE _ E q
lemBE M (wrap E) ()
lemBE M (unwrap E / r) ()


-- these adhoc lemmas about subst are needed as do the uniqueness bits of
-- lemma51! with pattern matching lambdas and can't use with

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

valred : ∀{A}{L N : ∅ ⊢ A} → Value L → L —→⋆ N → ⊥
valred (V-I⇒ b .(bubble p) (step p () x₁)) (β-ƛ VN)
valred (V-IΠ b .(bubble p) (step p () x₁)) (β-ƛ VN)
valred (V-I⇒ b .(bubble p₁) (step⋆ p₁ () .p)) (β-Λ p)
valred (V-IΠ b .(bubble p₁) (step⋆ p₁ () .p)) (β-Λ p)
valred (V-I⇒ b p₁ ()) (β-wrap VN p)
valred (V-IΠ b p₁ ()) (β-wrap VN p)
valred (V-I⇒ b₁ .(bubble p₁) (step p₁ x x₁)) (β-sbuiltin b t p bt u vu)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl
valred (V-IΠ b₁ .(bubble p₁) (step p₁ x x₁)) (β-sbuiltin b t p bt u vu)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl
valred (V-I⇒ b₁ .(bubble p₁) (step⋆ p₁ x q)) (β-sbuiltin⋆ b t p bt A q)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl
valred (V-IΠ b₁ .(bubble p₁) (step⋆ p₁ x q)) (β-sbuiltin⋆ b t p bt A r)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl

{-
bapperr : ∀{A}{L : ∅ ⊢ A}{b az as}{p : az <>> as ∈ arity b}
  → Error L → BApp b p L → ⊥
bapperr () base
bapperr () (step p bs x)
bapperr () (step⋆ p bs)
-}

valerr : ∀{A}{L : ∅ ⊢ A} → Error L → Value L → ⊥
valerr E-error (V-I⇒ b p ())
valerr E-error (V-IΠ b p ())

errred : ∀{A}{L N : ∅ ⊢ A} → Error L → L —→⋆ N → ⊥
errred E-error ()

-- should replace this with something more general if something similar shows
-- up again
substƛVal : ∀{A A' B}{M : ∅ , A ⊢ B} (p : A ≡ A')
  → Value (substEq (λ A → ∅ ⊢ (A ⇒ B)) p (ƛ M))
substƛVal refl = V-ƛ _

BUILTIN-eq : ∀{A b b' az az'}(M : ∅ ⊢ A)(p : az <>> _ ∈ arity b)(p' : az' <>> _ ∈ arity b')(bv : BApp b p M)(bv' : BApp b' p' M)
  → BUILTIN' b p bv ≡ BUILTIN' b' p' bv'
BUILTIN-eq M p p' bv bv'
  with uniqueBApp' M p p' bv bv'
... | refl ,, refl ,, refl ,, refl
  with uniqueBApp p M bv bv'
... | refl = refl

determinism⋆ : ∀{A}{L N N' : ∅ ⊢ A} → L —→⋆ N → L —→⋆ N' → N ≡ N'
determinism⋆ (β-ƛ _) (β-ƛ _) = refl
determinism⋆ (β-Λ refl) (β-Λ refl) = refl
determinism⋆ (β-wrap _ refl) (β-wrap _ refl) = refl
determinism⋆ (β-sbuiltin b t p bt u vu) (β-sbuiltin b' .t p' bt' .u vu') =
  BUILTIN-eq _ (bubble p) (bubble p') (step p bt vu) (step p' bt' vu')
determinism⋆ (β-sbuiltin⋆ b t p bt A refl) (β-sbuiltin⋆ b' .t p' bt' .A refl) =
  BUILTIN-eq _ (bubble p) (bubble p') (step⋆ p bt refl) (step⋆ p' bt' refl)

data Redex {A : ∅ ⊢Nf⋆ *} : ∅ ⊢ A → Set where
  β   : {L N : ∅ ⊢ A} → L —→⋆ N → Redex L
  err : Redex (error A)

valredex : ∀{A}{L : ∅ ⊢ A} → Value L → Redex L → ⊥
valredex V (β r) = valred V r
valredex V err   = valerr E-error V

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

-- these lemmas are needed for the uniqueness cases of lemma51!
-- it might be cleaner to define every uniqueness case directly as a lemma

-- a beta⋆ reduction happened
U·⋆1 : ∀{A : ∅ ⊢Nf⋆ K}{B}{L : ∅ ,⋆ K ⊢ B}{X}
 {B' : ∅ ⊢Nf⋆ *}
 → (p : X ≡ B [ A ]Nf)
 → (E' : EC X  B'){L' : ∅ ⊢ B'}
 → Λ L _⊢_.·⋆ A / p ≡ (E' [ L' ]ᴱ)
 → Redex L' →
 ∃ (λ (q : X ≡ B') → substEq (EC _) q [] ≡ E' × substEq (∅ ⊢_) q (Λ L ·⋆ A / p) ≡ L')
U·⋆1 eq [] refl q = refl ,, refl ,, refl
U·⋆1 eq (E' ·⋆ A / r) p q with lem-·⋆ r eq p
U·⋆1 {L = L} eq (E' ·⋆ A / r) {L'} p q | refl ,, Y ,, refl ,, refl
  with lemΛE'' E' Y
U·⋆1 {_} {A} {L = L} eq (_·⋆_/_ {_} E' A r) {.(Λ L)} p (β ()) | refl ,, Y ,, refl ,, refl | refl ,, X ,, refl

-- M is not a value, it has made a step
U·⋆2 : ∀{K}{C}{A : ∅ ⊢Nf⋆ K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{M : ∅ ⊢ Π B}{E : EC (Π B) C}{L : ∅ ⊢ C}{X}
 {B' : ∅ ⊢Nf⋆ *}
 → ¬ (Value M)
 → (p : X ≡ B [ A ]Nf) →
 (E' : EC X B')
 {L' : ∅ ⊢ B'} →
 M _⊢_.·⋆ A / p ≡ (E' [ L' ]ᴱ) →
 Redex L' →
 (U : {B' : ∅ ⊢Nf⋆ *} (E' : EC (Π B) B') {L' : ∅ ⊢ B'} →
      M ≡ (E' [ L' ]ᴱ) →
      Redex L' →
      ∃ (λ (q : C ≡ B') → substEq (EC _) q E ≡ E' × substEq (_⊢_ ∅) q L ≡ L'))
 →
 ∃
 (λ (p₁ : C ≡ B') →
   substEq
   (EC X)
   p₁ (E EC.·⋆ A / p)
   ≡ E'
   × substEq (_⊢_ ∅) p₁ L ≡ L')
U·⋆2 ¬VM eq [] refl (β (β-Λ .eq)) U = ⊥-elim (¬VM (V-Λ _))
U·⋆2 ¬VM eq [] refl (β (β-sbuiltin⋆ b _ p bt _ .eq)) U =
  ⊥-elim (¬VM (V-IΠ b p bt))
U·⋆2 ¬VM eq (E ·⋆ A / .eq) refl q U with U E refl q
... | refl ,, refl ,, refl = refl ,, refl ,, refl


U·⋆3 : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ⊢ Π B}{B' : ∅ ⊢Nf⋆ *}{X}
      → (p : X ≡ B [ A ]Nf) →
      (E' : EC X B')
      {L' : ∅ ⊢ B'} →
      Value M →
      M _⊢_.·⋆ A / p ≡ (E' [ L' ]ᴱ) →
      Redex L' →
      ∃ λ (q : X ≡ B') → substEq (EC X) q [] ≡ E'
         × substEq (∅ ⊢_) q (M _⊢_.·⋆ A / p) ≡ L'
U·⋆3 eq (E ·⋆ A / .eq) V refl q = ⊥-elim (valredex (lemVE _ E V) q)
U·⋆3 refl [] V refl q = refl ,, refl ,, refl

-- body of wrap made a step, it's not a value
Uwrap : ∀{A C}{B : ∅ ⊢Nf⋆ K}{M : ∅ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}{L : ∅ ⊢ C}{E}{B' : ∅ ⊢Nf⋆ *}
 → (E' : EC (μ A B) B') {L' : ∅ ⊢ B'} →
 _⊢_.wrap A B M ≡ E' [ L' ]ᴱ →
 Redex L' →
 (U : {B' : ∅ ⊢Nf⋆ *}
      (E' : EC _ B')
      {L' : ∅ ⊢ B'} →
      M ≡ (E' [ L' ]ᴱ) →
      Redex L' →
      ∃ (λ p → substEq (EC _) p E ≡ E' × substEq (_⊢_ ∅) p L ≡ L'))
 →
 ∃
 (λ (p₁ : C ≡ B') →
    substEq (EC (μ A B)) p₁ (wrap E) ≡ E' × substEq (_⊢_ ∅) p₁ L ≡ L')
Uwrap (E l· x) () q U
Uwrap (x ·r E) () q U
Uwrap (E ·⋆ A / x) () q U
Uwrap (wrap E) refl q U with U E refl q
... | refl ,, refl ,, refl = refl ,, refl ,, refl
Uwrap (unwrap E / x) () q U
Uwrap [] refl (β ()) U

-- the body of the unwrap, M, is not a value and made a step
Uunwrap1 : ∀{A C}{B : ∅ ⊢Nf⋆ K}{M : ∅ ⊢ μ A B}{L : ∅ ⊢ C}{E}{B' : ∅ ⊢Nf⋆ *}{X}
  → ¬ (Value M)
  → (p : X ≡ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) →
  (E' : EC X B')
  {L' : ∅ ⊢ B'} →
  _⊢_.unwrap M p ≡ (E' [ L' ]ᴱ) →
  Redex L' →
  (U : {B' : ∅ ⊢Nf⋆ *} (E' : EC (μ A B) B') {L' : ∅ ⊢ B'} →
    M ≡ (E' [ L' ]ᴱ) →
    Redex L' →
    ∃ (λ q → substEq (EC (μ A B)) q E ≡ E' × substEq (_⊢_ ∅) q L ≡ L'))
  →
  ∃ (λ (q : C ≡ B') →
    substEq (EC X) q (EC.unwrap E / p) ≡ E' × substEq (_⊢_ ∅) q L ≡ L')
Uunwrap1 ¬VM eq [] refl (β (β-wrap x .eq)) U = ⊥-elim (¬VM (V-wrap x))
Uunwrap1 ¬VM refl (unwrap E / refl) refl q U with U E refl q
... | refl ,, refl ,, refl = refl ,, refl ,, refl

-- beta step
Uunwrap2 : ∀{A}{B : ∅ ⊢Nf⋆ K}{M : ∅ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}{B' : ∅ ⊢Nf⋆ *}{X}
  → Value M
  → (p : X ≡ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) →
  (E' : EC X B')
  {L' : ∅ ⊢ B'} →
  _⊢_.unwrap (wrap A B M) p ≡ (E' [ L' ]ᴱ) →
  Redex L' →
  ∃ (λ (q : X ≡ B')
    → substEq (EC X) q [] ≡ E' × substEq (∅ ⊢_) q (unwrap (wrap A B M) p) ≡ L')
Uunwrap2 VM eq (unwrap E / x) p q with lem-unwrap p
... | refl ,, refl ,, refl ,, X4 =
  ⊥-elim (valredex (lemVE
                     _
                     E
                     (substEq Value (≅-to-≡ X4)
                     (V-wrap VM))) q)
Uunwrap2 VM refl [] refl q = refl ,, refl ,, refl

rlemma51! : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → RProgress M
rlemma51! (ƛ M) = done (V-ƛ M)
rlemma51! (M · N) with rlemma51! M
... | step ¬VM E p q U = step
  (lemV· ¬VM)
  (E l· N)
  p
  (cong (_· N) q)
  λ { [] refl (β (β-ƛ VN)) → ⊥-elim (¬VM (V-ƛ _))
    ; [] refl (β (β-sbuiltin b .M p bt .N vu)) → ⊥-elim (¬VM (V-I⇒ b p bt))
    ; (E' l· N') refl r → let X ,, Y ,, Y' = U E' refl r in
      X ,,  trans ( subst-l· E N X)  (cong (_l· N) Y)  ,, Y'
    ; (VM ·r E') refl r → ⊥-elim (¬VM VM)
    }
... | done VM with rlemma51! N
... | step ¬VN E p q U = step
  (lemV'· ¬VN)
  (VM ·r E)
  p
  (cong (M ·_) q)
  λ { [] refl (β (β-ƛ VN)) → ⊥-elim (¬VN VN)
    ; [] refl (β (β-sbuiltin b .M p bt .N VN)) → ⊥-elim (¬VN VN)
    ; (E' l· N') refl q → ⊥-elim (valredex (lemVE _ _ VM) q)
    ; (VM' ·r E') refl q → let X ,, X'' ,, X''' = U E' refl q in
      X
      ,,
      trans (subst-·r E M VM X)
            (trans (cong (VM ·r_) X'') (cong (_·r E') (uniqueVal M VM VM')))
      ,,
      X'''}
rlemma51! (.(ƛ M) · N) | done (V-ƛ M) | done VN = step
  lemVβ
  []
  (β (β-ƛ VN))
  refl
  λ { [] refl (β (β-ƛ x)) → refl ,, refl ,, refl
    ; (E' l· N') p q → let X ,, Y ,, Y' = proj· p in
      ⊥-elim (valredex (lemVE _ E' (substEq Value Y (substƛVal X))) q)
    ; (VM' ·r E') refl q → ⊥-elim (valredex (lemVE _ E' VN) q)}
rlemma51! (M · N) | done (V-I⇒ b {as' = []}       p x) | done VN = step
  (λ V → valred V (β-sbuiltin b M p x N VN))
  []
  (β (β-sbuiltin b M p x N VN))
  refl
  λ { [] refl (β (β-sbuiltin b .M p bt .N vu)) → refl ,, refl ,, refl
    ; (E' l· N') refl q → ⊥-elim (valredex (lemBE _ E' x) q)
    ; (VM' ·r E') refl q → ⊥-elim (valredex (lemVE _ E' VN) q)}
rlemma51! (M · N) | done (V-I⇒ b {as' = a' ∷ as'} p x) | done VN =
  done (V-I b (bubble p) (step p x VN))
rlemma51! (Λ M) = done (V-Λ M)
rlemma51! (M ·⋆ A / x) with rlemma51! M
... | done (V-Λ M) = step
  lemVβ⋆
  []
  (β (β-Λ x))
  refl
  (U·⋆1 x)
rlemma51! (M ·⋆ A / x) | done (V-IΠ b {as' = []} p q) = step
  (λ V → valred V (β-sbuiltin⋆ b M p q A x))
  []
  (β (β-sbuiltin⋆ b M p q A x))
  refl
  λ E p' q' → U·⋆3 x E (V-IΠ b _ q) p' q'
rlemma51! (M ·⋆ A / x) | done (V-IΠ b {as' = x₁ ∷ as'} p q) =
  done (V-I b (bubble p) (step⋆ p q x))
... | step ¬VM E p q U = step
  (λ V → lemV·⋆ (λ V → ¬VM V) V)
  (E ·⋆ A / x)
  p
  (cong (_·⋆ A / x) q)
  λ E p q → U·⋆2 ¬VM x E p q U
rlemma51! (wrap A B M) with rlemma51! M
... | step ¬VM E p q U = step
  (λ {(V-wrap VM) → ¬VM VM})
  (wrap E)
  p
  (cong (wrap A B) q)
  λ E p' q' → Uwrap E p' q' U
... | done VM = done (V-wrap VM)
rlemma51! (unwrap M x) with rlemma51! M
... | step ¬VM E p q U = step
  (λ V → lemVunwrap V)
  (unwrap E / x)
  p
  (cong (λ M → unwrap M x) q)
  λ E p' q' → Uunwrap1 ¬VM x E p' q' U
... | done (V-wrap VM) = step
  (λ V → valred V (β-wrap VM x))
  []
  (β (β-wrap VM x))
  refl
  λ E p' q' → Uunwrap2 VM x E p' q'
rlemma51! (con c) = done (V-con c)
rlemma51! (builtin b / refl) = done (ival b)
rlemma51! (error _) = step
  (valerr E-error)
  []
  err
  refl
  λ { [] p q → refl ,, refl ,, p}

unique-EC : ∀{A B}(E E' : EC A B)(L : ∅ ⊢ B) → Redex L
  → E [ L ]ᴱ ≡ E' [ L ]ᴱ → E ≡ E'
unique-EC  E E' L p q with rlemma51! (E [ L ]ᴱ)
... | done VEL = ⊥-elim (valredex (lemVE L E VEL) p)
... | step ¬VEL E'' r r' U with U E' q p
... | refl ,, refl ,, refl with U E refl p
... | refl ,, refl ,, refl = refl

notVAL : ∀{A}{L N : ∅ ⊢ A} → Value L → L —→ N → ⊥
notVAL V (ruleEC E p refl r) = valred (lemVE _ E V) p
notVAL V (ruleErr E refl)    =
  valerr E-error (lemVE _ E V)

determinism : ∀{A}{L N N' : ∅ ⊢ A} → L —→ N → L —→ N' → N ≡ N'
determinism {L = L} p q with rlemma51! L
determinism {L = .(E [ _ ]ᴱ)} (ruleEC E p refl p') q | done VL =
  ⊥-elim (valred (lemVE _ E VL) p)
determinism {L = L} (ruleErr E refl)      q | done VL =
  ⊥-elim (valerr E-error (lemVE _ E VL))
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
-- -}
