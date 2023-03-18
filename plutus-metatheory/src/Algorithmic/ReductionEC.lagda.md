```
module Algorithmic.ReductionEC where
```
## Imports

```
open import Agda.Builtin.String using (primStringAppend ; primStringEquality)
open import Data.Bool using (Bool;true;false)
open import Data.Empty using (⊥;⊥-elim)
open import Data.Integer using (_<?_;∣_∣;_≤?_;_≟_)
open import Data.List as List using (List; _∷_; [];length)
open import Data.Maybe using (just;from-just)
open import Data.Product using (_×_;∃) renaming (_,_ to _,,_)
open import Data.String using (String)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_;yes;no)
open import Relation.Binary.PropositionalEquality 
                    using (_≡_;refl;sym;trans;cong)  
                    renaming (subst to substEq)
open import Relation.Binary.HeterogeneousEquality 
        using (_≅_;refl;≅-to-≡) 

open import Utils hiding (TermCon)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z)
open _⊢⋆_
import Type.RenamingSubstitution as T
open import Algorithmic using (Ctx;_⊢_;arity;btype;Term;Type;conv⊢)
open Ctx
open _⊢_
open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.Properties using (lem-·⋆;lem-unwrap)
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf)
open import Type.BetaNormal using (_⊢Nf⋆_;embNf;weakenNf)
open _⊢Nf⋆_
open import Builtin 
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) using (TyCon)
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con using (TermCon)
open TermCon
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

{-
tval : {A : ∅ ⊢Nf⋆ *}{u : ∅ ⊢ A} → Value u → ∅ ⊢Nf⋆ *
tval {A = A} _ = A
-}

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
  con (bool (B<= b b'))
BUILTIN sha2-256 (step _ (base refl) (V-con (bytestring b))) =
  con (bytestring (SHA2-256 b))
BUILTIN sha3-256 (step _ (base refl) (V-con (bytestring b))) =
  con (bytestring (SHA3-256 b))
BUILTIN blake2b-256 (step _ (base refl) (V-con (bytestring b))) =
  con (bytestring (BLAKE2B-256 b))
BUILTIN verifyEd25519Signature (step _ (step _ (step _ (base refl) (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c)))
  with verifyEd25519Sig k d c
... | just b = con (bool b)
... | nothing = error _
BUILTIN verifyEcdsaSecp256k1Signature (step _ (step _ (step _ (base refl) (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c)))
  with verifyEcdsaSecp256k1Sig k d c
... | just b = con (bool b)
... | nothing = error _
BUILTIN verifySchnorrSecp256k1Signature (step _ (step _ (step _ (base refl) (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c)))
  with verifySchnorrSecp256k1Sig k d c
... | just b = con (bool b)
... | nothing = error _
BUILTIN equalsByteString (step _ (step _ (base refl) (V-con (bytestring b))) (V-con (bytestring b'))) =
  con (bool (equals b b'))
BUILTIN ifThenElse (step _ (step _ (step _ (step⋆ _ (base refl) refl) (V-con (bool true))) t) f) = deval t
BUILTIN ifThenElse (step _ (step _ (step _ (step⋆ _ (base refl) refl) (V-con (bool false))) t) f) = deval f
BUILTIN appendString (step _ (step _ (base refl) (V-con (string s))) (V-con (string s'))) =
  con (string (primStringAppend s s'))
BUILTIN trace (step _ (step _ (step⋆ _ (base refl) refl) (V-con (string s))) v) = TRACE s (deval v)
BUILTIN iData (step _ (base refl) (V-con (integer i))) = con (pdata (iDATA i))
BUILTIN bData (step _ (base refl) (V-con (bytestring b))) = con (pdata (bDATA b))
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
BUILTIN unIData (step _ (base refl) (V-con (pdata (iDATA i)))) = con (integer i)
BUILTIN unBData (step _ (base refl) (V-con (pdata (bDATA b)))) = con (bytestring b)
BUILTIN serialiseData (step _ (base refl) (V-con (pdata d))) = con (bytestring (serialiseDATA d))
BUILTIN _ _ = error _

convBApp : (b : Builtin) → ∀{az}{as}(p p' : az <>> as ∈ arity b)
  → ∀{A}(t : ∅ ⊢ A)
  → BApp b p t
  → BApp b p' t
convBApp b p p' t q rewrite unique<>> p p' = q

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

{-
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
-}


## Intrinsically Type Preserving Reduction

### Frames

Frames used by the CC and the CK machine, and their plugging function.
```
data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·_     : {A B : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → Frame B A
  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K) → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (μ A B) (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  unwrap- : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) (μ A B)

_[_]ᶠ : ∀{A B : ∅ ⊢Nf⋆ *} → Frame B A → ∅ ⊢ A → ∅ ⊢ B
(-· M') [ L ]ᶠ = L · M'
(V ·-)  [ L ]ᶠ = deval V · L
-·⋆ A   [ L ]ᶠ = L ·⋆ A / refl
wrap-   [ L ]ᶠ = wrap _ _ L
unwrap- [ L ]ᶠ = unwrap L refl
```

## Evaluation Contexts

```
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

-- Plugging of evaluation contexts
_[_]ᴱ : ∀{A B : ∅ ⊢Nf⋆ *} → EC B A → ∅ ⊢ A → ∅ ⊢ B
[]       [ L ]ᴱ = L
(E l· B) [ L ]ᴱ = E [ L ]ᴱ · B
(V ·r E) [ L ]ᴱ = deval V · E [ L ]ᴱ
(E ·⋆ A / q) [ L ]ᴱ = E [ L ]ᴱ ·⋆ A / q
(wrap   E) [ L ]ᴱ = wrap _ _ (E [ L ]ᴱ)
(unwrap E / q) [ L ]ᴱ = unwrap (E [ L ]ᴱ) q
```

## Evaluation Relation

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


{-
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
-}
```



```
infix 2 _—→_

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

### Reflexive-transitive closure of evaluation relation

```
data _—↠_ : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → ∅ ⊢ A → Set
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

## Some auxiliary proofs used by Progress and Determinism.

```
-- these two proofs are defined by pattern matching on the builtin,
-- they are very long and very ugly.  They could probably be made
-- shorter by giving cases for particular types/arities, and adding a
-- lemma that knocks off a more general class of imposible _<>>_∈_
-- inhabitants.

-- HINT: pattern matching on p rather than the next arg (q) generates
-- fewer cases
postulate bappTermLem : ∀  b {A}{az as}(M : ∅ ⊢ A)(p : az <>> Term ∷ as ∈ arity b) → BApp b p M → ∃ λ A' → ∃ λ A'' → A ≡ A' ⇒ A''
-- FIXME: This is commented out just to get past teh typechecker in the absence of the BLS builtins.
{-
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
bappTermLem verifyEd25519Signature _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem verifyEd25519Signature _ (bubble (start _)) (step (start _) (base refl) _) =
  _ ,, _ ,, refl
bappTermLem verifyEd25519Signature {as = as} _ (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Term) :< Term) :< Term) as p refl
bappTermLem verifyEd25519Signature
            _
            (bubble (bubble (start _)))
            (step _ (step _ (base refl) _) _)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem verifyEcdsaSecp256k1Signature _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem verifyEcdsaSecp256k1Signature _ (bubble (start _)) (step (start _) (base refl) _) =
  _ ,, _ ,, refl
bappTermLem verifyEcdsaSecp256k1Signature {as = as} _ (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Term) :< Term) :< Term) as p refl
bappTermLem verifyEcdsaSecp256k1Signature
            _
            (bubble (bubble (start _)))
            (step _ (step _ (base refl) _) _)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem verifySchnorrSecp256k1Signature _ (start _) (base refl) = _ ,, _ ,, refl
bappTermLem verifySchnorrSecp256k1Signature _ (bubble (start _)) (step (start _) (base refl) _) =
  _ ,, _ ,, refl
bappTermLem verifySchnorrSecp256k1Signature {as = as} _ (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Term) :< Term) :< Term) as p refl
bappTermLem verifySchnorrSecp256k1Signature
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
bappTermLem serialiseData {az = az} {as} M p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem serialiseData _ (start _) (base refl) | refl ,, refl = _ ,, _ ,, refl
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
bappTermLem mkCons _ (bubble (start _)) (step⋆ _ (base refl) refl) =
  _ ,, _ ,, refl
bappTermLem mkCons _ (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Type) :< Term) :< Term) _ p refl
bappTermLem mkCons
            _
            (bubble (bubble (start _)))
            (step _ (step⋆ _ (base refl) refl) x)
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
bappTermLem _ _ _ _ = error  -- FIXME!!!
-}
```

```
postulate bappTypeLem : ∀  b {A}{az as}(M : ∅ ⊢ A)(p : az <>> (Type ∷ as) ∈ arity b) → BApp b p M → ∃ λ K → ∃ λ (B : ∅ ,⋆ K ⊢Nf⋆ *) → A ≡ Π B

{-
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
bappTypeLem verifyEd25519Signature _ (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ([] <>< arity verifyEd25519Signature) _ p refl
... | refl ,, refl ,, ()
bappTypeLem verifyEcdsaSecp256k1Signature _ (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ([] <>< arity verifyEcdsaSecp256k1Signature) _ p refl
... | refl ,, refl ,, ()
bappTypeLem verifySchnorrSecp256k1Signature _ (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ([] <>< arity verifySchnorrSecp256k1Signature) _ p refl
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
bappTypeLem serialiseData {az = az} _ p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
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
bappTypeLem mkCons _ (start _) (base refl) = _ ,, _ ,, refl
bappTypeLem mkCons _ (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ([] <>< arity mkCons) _ p refl
... | _ ,, _ ,, ()
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
-}
```

A smart constructor that looks at the arity and then puts on the
right constructor

```
V-I : ∀ b {A : ∅ ⊢Nf⋆ *}{a as as'}
       → (p : as <>> a ∷ as' ∈ arity b)
       → {t : ∅ ⊢ A}
       → BApp b p t
       → Value t
V-I b {a = Term} p q with bappTermLem b _ p q
... | _ ,, _ ,, refl = V-I⇒ b p q
V-I b {a = Type} p q  with bappTypeLem b _ p q
... | _ ,, _ ,, refl = V-IΠ b p q
```

For each builtin, return the value corresponding to the completely unapplied builtin

```
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
ival verifyEd25519Signature = V-I⇒ verifyEd25519Signature (start _) (base refl) 
ival verifyEcdsaSecp256k1Signature = V-I⇒ verifyEcdsaSecp256k1Signature (start _) (base refl) 
ival verifySchnorrSecp256k1Signature = V-I⇒ verifySchnorrSecp256k1Signature (start _) (base refl) 
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
ival serialiseData = V-I _ (start _) (base refl)
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
ival bls12-381-G1-add = V-I⇒ bls12-381-G1-add (start _) (base refl)
ival bls12-381-G1-neg = V-I⇒ bls12-381-G1-neg (start _) (base refl)
ival bls12-381-G1-scalarMul = V-I⇒ bls12-381-G1-scalarMul (start _) (base refl)
ival bls12-381-G1-equal = V-I⇒ bls12-381-G1-equal (start _) (base refl)
ival bls12-381-G1-hashToGroup = V-I⇒ bls12-381-G1-hashToGroup (start _) (base refl)
ival bls12-381-G1-compress = V-I⇒ bls12-381-G1-compress (start _) (base refl)
ival bls12-381-G1-uncompress = V-I⇒ bls12-381-G1-uncompress (start _) (base refl)
ival bls12-381-G2-add = V-I⇒ bls12-381-G2-add (start _) (base refl)
ival bls12-381-G2-neg = V-I⇒ bls12-381-G2-neg (start _) (base refl)
ival bls12-381-G2-scalarMul = V-I⇒ bls12-381-G2-scalarMul (start _) (base refl)
ival bls12-381-G2-equal = V-I⇒ bls12-381-G2-equal (start _) (base refl)
ival bls12-381-G2-hashToGroup = V-I⇒ bls12-381-G2-hashToGroup (start _) (base refl)
ival bls12-381-G2-compress = V-I⇒ bls12-381-G2-compress (start _) (base refl)
ival bls12-381-G2-uncompress = V-I⇒ bls12-381-G2-uncompress (start _) (base refl)
ival bls12-381-pairing = V-I⇒ bls12-381-pairing (start _) (base refl)
ival bls12-381-mulMlResult = V-I⇒ bls12-381-mulMlResult (start _) (base refl)
ival bls12-381-finalVerify = V-I⇒ bls12-381-finalVerify (start _) (base refl)
```