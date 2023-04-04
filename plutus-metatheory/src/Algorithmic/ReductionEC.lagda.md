```
module Algorithmic.ReductionEC where
```
## Imports

```
open import Agda.Builtin.String using (primStringAppend ; primStringEquality)
open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Bool using (Bool;true;false)
open import Data.Empty using (⊥;⊥-elim)
open import Data.Integer using (_<?_;∣_∣;_≤?_;_≟_)
open import Data.List as List using (List; _∷_; [];length)
open import Data.Maybe using (just;from-just)
open import Data.Product using (_×_;∃;proj₁;proj₂) renaming (_,_ to _,,_)
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
open import Algorithmic using (Ctx;_⊢_;conv⊢)
open import Algorithmic.Signature using (btype;_[_]SigTy)
open Ctx
open _⊢_
open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.Properties using (lem-·⋆;lem-unwrap)
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;embNf;weakenNf)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Builtin 
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) using (TyCon)
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con using (TermCon)
open TermCon

open import Builtin.Signature using (Sig;sig;Args;_⊢♯;nat2Ctx⋆;fin2∈⋆;args♯)
open Sig

open Builtin.Signature.FromSig Ctx⋆ (_⊢Nf⋆ *) nat2Ctx⋆ (λ x → ne (` (fin2∈⋆ x))) con _⇒_ Π 
    using (sig2type;♯2*;SigTy;sig2SigTy;sigTy2type;saturatedSigTy;convSigTy)
open SigTy
```

## Values

``` 
data Value : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Set

data BApp (b : Builtin) : 
    ∀{tn tm tt} → {pt : tn ∔ tm ≣ tt}
  → ∀{an am at} → {pa : an ∔ am ≣ at}
  → ∀{A} → SigTy pt pa A → ∅ ⊢ A → Set where
  base : BApp b (sig2SigTy (signature b)) (builtin b / refl )
  step : ∀{A B}{tn}
    → {pt : tn ∔ 0 ≣ fv♯ (signature b)} 
    → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
    → {σB : SigTy pt (bubble pa) B}
    → {t : ∅ ⊢ A ⇒ B} → BApp b (A B⇒ σB) t
    → {u : ∅ ⊢ A} → Value u → BApp b σB (t · u)
  step⋆ : ∀{C B}
    → ∀{tn tm} {pt : tn ∔ (suc tm) ≣ fv♯ (signature b)} 
    → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
    → {σB : SigTy (bubble pt) pa B}
    → {t : ∅ ⊢ Π B} → BApp b (sucΠ σB) t
    → {A : ∅ ⊢Nf⋆ *}
    → (q : C ≡ B [ A ]Nf)
    → {σC : SigTy (bubble pt) pa C}
    → (σq : σC ≡ convSigTy (sym q) (σB [ A ]SigTy))
    → BApp b σC (t ·⋆ A / q)

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

  V-I⇒ : ∀ b {A B}{tn}
       → {pt : tn ∔ 0 ≣ fv♯ (signature b)} 
       → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
       → {σB : SigTy pt (bubble pa) B}
       → {t : ∅ ⊢ A ⇒ B}
       → BApp b (A B⇒ σB) t
       → Value t
  V-IΠ : ∀ b {A : ∅ ,⋆ * ⊢Nf⋆ *}
       → ∀{tn tm} {pt : tn ∔ (suc tm) ≣ fv♯ (signature b)} 
       → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
       → {σA : SigTy (bubble pt) pa A}
       → {t : ∅ ⊢ Π A}
       → BApp b (sucΠ σA) t
       → Value t


deval : {A : ∅ ⊢Nf⋆ *}{u : ∅ ⊢ A} → Value u → ∅ ⊢ A
deval {u = u} _ = u

BUILTIN : ∀ b {A}{t : ∅ ⊢ A}  {Ab : saturatedSigTy (signature b) A} → BApp b Ab t → ∅ ⊢ A
BUILTIN addInteger (step (step base (V-con (integer i))) (V-con (integer j))) = con (integer (i Data.Integer.+ j))
BUILTIN subtractInteger (step (step base (V-con (integer i))) (V-con (integer j))) = con (integer (i Data.Integer.- j))
BUILTIN multiplyInteger (step (step base (V-con (integer i))) (V-con (integer j))) = con (integer (i Data.Integer.* j))
BUILTIN divideInteger (step (step base (V-con (integer i))) (V-con (integer j)))
  with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = con (integer (div i j))
... | yes p = error _
BUILTIN quotientInteger (step (step base (V-con (integer i))) (V-con (integer j)))
  with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = con (integer (quot i j))
... | yes p = error _
BUILTIN remainderInteger (step (step base (V-con (integer i))) (V-con (integer j)))
  with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = con (integer (rem i j))
... | yes p = error _
BUILTIN modInteger (step (step base (V-con (integer i))) (V-con (integer j)))
  with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = con (integer (mod i j))
... | yes p = error _
BUILTIN lessThanInteger (step (step base (V-con (integer i))) (V-con (integer j)))
  with i <? j
... | no ¬p = con (bool false)
... | yes p = con (bool true)
BUILTIN lessThanEqualsInteger (step (step base (V-con (integer i))) (V-con (integer j)))
  with i ≤? j
... | no ¬p = con (bool false)
... | yes p = con (bool true)
BUILTIN equalsInteger (step (step base (V-con (integer i))) (V-con (integer j)))
  with i ≟ j
... | no ¬p = con (bool false)
... | yes p = con (bool true)
BUILTIN appendByteString (step (step base (V-con (bytestring b))) (V-con (bytestring b'))) =
  con (bytestring (concat b b'))
BUILTIN lessThanByteString (step (step base (V-con (bytestring b))) (V-con (bytestring b'))) =
  con (bool (B< b b'))
BUILTIN lessThanEqualsByteString (step (step base (V-con (bytestring b))) (V-con (bytestring b'))) = 
  con (bool (B<= b b'))
BUILTIN sha2-256 (step base (V-con (bytestring b))) =
  con (bytestring (SHA2-256 b))
BUILTIN sha3-256 (step base (V-con (bytestring b))) =
  con (bytestring (SHA3-256 b))
BUILTIN blake2b-256 (step base (V-con (bytestring b))) =
  con (bytestring (BLAKE2B-256 b))
BUILTIN verifyEd25519Signature (step (step (step base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c)))
  with verifyEd25519Sig k d c
... | just b = con (bool b)
... | nothing = error _
BUILTIN verifyEcdsaSecp256k1Signature (step (step (step base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c)))
  with verifyEcdsaSecp256k1Sig k d c
... | just b = con (bool b)
... | nothing = error _
BUILTIN verifySchnorrSecp256k1Signature (step (step (step base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c)))
  with verifySchnorrSecp256k1Sig k d c
... | just b = con (bool b)
... | nothing = error _
BUILTIN equalsByteString (step (step base (V-con (bytestring b))) (V-con (bytestring b'))) =
  con (bool (equals b b'))
BUILTIN ifThenElse (step (step (step (step⋆ base refl refl) (V-con (bool true))) t) f) = deval t
BUILTIN ifThenElse (step (step (step (step⋆ base refl refl) (V-con (bool false))) t) f) = deval f
BUILTIN appendString (step (step base (V-con (string s))) (V-con (string s'))) =
  con (string (primStringAppend s s'))
BUILTIN trace (step (step (step⋆ base refl refl) (V-con (string s))) v) = TRACE s (deval v)
BUILTIN iData (step base (V-con (integer i))) = con (pdata (iDATA i))
BUILTIN bData (step base (V-con (bytestring b))) = con (pdata (bDATA b))
BUILTIN consByteString (step (step base (V-con (integer i))) (V-con (bytestring b))) = con (bytestring (cons i b))
BUILTIN sliceByteString (step (step (step base (V-con (integer st))) (V-con (integer n))) (V-con (bytestring b))) = con (bytestring (slice st n b))
BUILTIN lengthOfByteString (step base (V-con (bytestring b))) = con (integer (Builtin.length b))
BUILTIN indexByteString (step (step base (V-con (bytestring b))) (V-con (integer i)))
  with Data.Integer.ℤ.pos 0 ≤? i
... | no  _ = error _
... | yes _
  with i <? Builtin.length b
... | no _ =  error _
... | yes _ = con (integer (index b i))
BUILTIN equalsString (step (step base (V-con (string s))) (V-con (string s'))) =
  con (bool (primStringEquality s s'))
BUILTIN encodeUtf8 (step base (V-con (string s))) =
  con (bytestring (ENCODEUTF8 s))
BUILTIN decodeUtf8 (step base (V-con (bytestring b)))
  with DECODEUTF8 b
... | nothing = error _
... | just s  = con (string s)
BUILTIN unIData (step base (V-con (pdata (iDATA i)))) = con (integer i)
BUILTIN unBData (step base (V-con (pdata (bDATA b)))) = con (bytestring b)
BUILTIN serialiseData (step base (V-con (pdata d))) = con (bytestring (serialiseDATA d))
BUILTIN _ _ = error _

BUILTIN' : ∀ b {A}{t : ∅ ⊢ A}
  → ∀{tn} → {pt : tn ∔ 0 ≣ fv♯ (signature b)}
  → ∀{an} → {pa : an ∔ 0 ≣ args♯ (signature b)}
  → {σA : SigTy pt pa A}
  → BApp b σA t
  → ∅ ⊢ A
BUILTIN' b {pt = pt} {pa = pa} bt with trans (sym (+-identityʳ _)) (∔2+ pt) | trans (sym (+-identityʳ _)) (∔2+ pa)
... | refl | refl with unique∔ pt (alldone (fv♯ (signature b))) | unique∔ pa (alldone (args♯ (signature b)))
... | refl | refl = BUILTIN b bt
```

```
data Error :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  -- an actual error term
  E-error : ∀{Φ Γ }{A : Φ ⊢Nf⋆ *} → Error {Γ = Γ} (error {Φ} A)
```

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

  β-builtin : ∀{A B}{tn}
      (b : Builtin)
    → (t : ∅ ⊢ A ⇒ B)
    → {pt : tn ∔ 0 ≣ fv♯ (signature b)} 
    → ∀{an} → {pa : an ∔ 1 ≣  args♯ (signature b)}
    → {σB : SigTy pt (bubble pa) B}
    → (bt : BApp b (A B⇒ σB) t) -- one left
    → (u : ∅ ⊢ A)
    → (vu : Value u)
      -----------------------------
    → t · u —→⋆ BUILTIN' b (step bt vu)
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

A smart constructor that looks at the arity and then puts on the
right constructor

```
V-I :  ∀ (b : Builtin) {A : ∅ ⊢Nf⋆ *}
       → ∀{tn tm} {pt : tn ∔ tm ≣ fv♯ (signature b)}
       → ∀{an am} {pa : an ∔ suc am ≣ args♯ (signature b)}
       → {σA : SigTy pt pa A}
       → {t : ∅ ⊢ A}
       → BApp b σA t
       → Value t
V-I b {tm = zero} {σA = A B⇒ σA} bt = V-I⇒ b bt
V-I b {tm = suc tm} {σA = sucΠ σA} bt = V-IΠ b bt
```

For each builtin, return the value corresponding to the completely unapplied builtin

```
ival : ∀ b → Value (builtin b / refl)
ival b = V-I b base
-- -}
```

