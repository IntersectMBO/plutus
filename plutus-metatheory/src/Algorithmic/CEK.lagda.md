---
title: Algorithmic.CEK
layout: page
---
# CEK machine that discharges builtin args

```
module Algorithmic.CEK where

open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Properties using (+-identityʳ)
open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec as Vec using (Vec;[];_∷_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;cong;trans)
open import Data.Unit using (⊤;tt)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ)
                         renaming (_*_ to _**_)
open import Data.Bool using (true;false)
open import Relation.Nullary using (no;yes)

open import Utils.List
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z;S)
open _⊢⋆_
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;embNf;weakenNf)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf;subNf-id;subNf-cong;extsNf;subNf∅)
open import Algorithmic as A using (Ctx;_⊢_;_∋_;conv⊢;builtin_/_;⟦_⟧;[];_∷_;ConstrArgs;Cases;lookupCase;bwdMkCaseType;lemma-bwdfwdfunction')
open import Algorithmic.Signature using (btype;_[_]SigTy)
open Ctx
open _⊢_
open _∋_
open import Algorithmic.RenamingSubstitution using (Sub;sub;exts;exts⋆;_[_];_[_]⋆)
open import Builtin
open import Utils hiding (List;length) renaming (_,_ to _,,_)

open import Builtin.Constant.AtomicType
open import Builtin.Constant.Type using (TyCon)
open TyCon

open import Builtin.Signature using (Sig;sig;Args;args♯;fv) renaming (_⊢♯ to _⊢b♯)
open Sig

open Builtin.Signature.FromSig _⊢Nf⋆_ _⊢Ne⋆_ ne ` _·_ ^ con _⇒_   Π
    using (sig2type;⊢♯2TyNe♯;SigTy;sig2SigTy;saturatedSigTy;convSigTy)
open SigTy
```

````
data Env : Ctx ∅ → Set

data BApp (b : Builtin) :
    ∀{tn tm tt} → {pt : tn ∔ tm ≣ tt}
  → ∀{an am at} → {pa : an ∔ am ≣ at}
  → (A : ∅ ⊢Nf⋆ *) → SigTy pt pa A → Set

data Value : (A : ∅ ⊢Nf⋆ *) → Set

VList : Bwd (∅ ⊢Nf⋆ *) → Set
VList = IBwd Value

data Value where
  V-ƛ : ∀ {Γ}{A B : ∅ ⊢Nf⋆ *}
    → (M : Γ , A ⊢ B)
    → Env Γ
    → Value (A ⇒ B)

  V-Λ : ∀ {Γ K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
    → (M : Γ ,⋆ K ⊢ B)
    → Env Γ
    → Value (Π B)

  V-wrap : ∀{K}
   → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : ∅ ⊢Nf⋆ K}
   → Value (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
   → Value (μ A B)

  V-con : ∀{A : ∅ ⊢Nf⋆ ♯}
    → ⟦ A ⟧
    → Value (con A)

  V-I⇒ : ∀ b {A B}{tn}
       → {pt : tn ∔ 0 ≣ fv (signature b)}
       → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
       → {σB : SigTy pt (bubble pa) B}
       → BApp b (A ⇒ B) (A B⇒ σB)
       → Value (A ⇒ B)

  V-IΠ : ∀ b {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
       → ∀{tn tm} {pt : tn ∔ (suc tm) ≣ fv (signature b)}
       → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
       → {σB : SigTy (bubble pt) pa B}
       → BApp b (Π B) (sucΠ σB)
       → Value (Π B)
  V-constr : ∀{n}(e : Fin n) Tss {ts} (vs : VList ts) → ts ≡ [] <>< Vec.lookup Tss e → Value (SOP Tss)

data BApp b where
  base : BApp b (sig2type (signature b)) (sig2SigTy (signature b))
  _$_ : ∀{A B}{tn}
    → {pt : tn ∔ 0 ≣ fv (signature b)}
    → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
    → {σB : SigTy pt (bubble pa) B}
    → BApp b (A ⇒ B) (A B⇒ σB)
    → Value A
    → BApp b B σB
  _$$_ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ * }{C}
    → ∀{tn tm} {pt : tn ∔ (suc tm) ≣ fv (signature b)}
    → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
    → {σB : SigTy (bubble pt) pa B}
    → BApp b (Π B) (sucΠ σB)
    → {A : ∅ ⊢Nf⋆ K}
    → (q : C ≡ B [ A ]Nf)
    → {σC : SigTy (bubble pt) pa C}
    → BApp b C σC

infixl 4 _$_
infixl 4 _$$_
pattern Λ̂ A = _$$_ base {A = A} refl
pattern _●_ bapp B = _$$_ bapp {A = B} refl
```

## Environments

```
data Env where
  [] : Env ∅
  _∷_ : ∀{Γ A} → Env Γ → Value A → Env (Γ , A)

lookup : ∀{Γ A} → Γ ∋ A → Env Γ → Value A
lookup Z     (ρ ∷ v) = v
lookup (S x) (ρ ∷ v) = lookup x ρ
```

## Conversion of Values to Terms

```
discharge : ∀{A} → Value A → ∅ ⊢ A

env2sub : ∀{Γ} → Env Γ → Sub (ne ∘ `) Γ ∅
env2sub (ρ ∷ V) Z     = conv⊢ refl (sym (subNf-id _)) (discharge V)
env2sub (ρ ∷ C)                   (S x) = env2sub ρ x

dischargeBody : ∀{Γ A B} → Γ , A ⊢ B → Env Γ → ∅ , A ⊢ B
dischargeBody M ρ = conv⊢
  (cong (∅ ,_) (subNf-id _))
  (subNf-id _)
  (sub (ne ∘ `) (exts (ne ∘ `) (env2sub ρ)) M)

dischargeBody⋆ : ∀{Γ K A} → Γ ,⋆ K ⊢ A → Env Γ → ∅ ,⋆ K ⊢ A
dischargeBody⋆ {A = A} M ρ = conv⊢
  refl
  (trans
    (subNf-cong
      {f = extsNf (ne ∘ `)}
      {g = ne ∘ `}
      (λ{ Z → refl; (S α) → refl})
      A)
    (subNf-id A))
  (sub (extsNf (ne ∘ `)) (exts⋆ (ne ∘ `) (env2sub ρ)) M)

dischargeB : ∀{b : Builtin}
          → ∀{tn tm} → {pt : tn ∔ tm ≣ fv (signature b)}
          → ∀{an am} → {pa : an ∔ am ≣ args♯ (signature b)}
          → ∀{C} → {Cb : SigTy pt pa C} → (bp : BApp b C Cb)
          → ∅ ⊢ C
dischargeB {b} base = builtin b / refl
dischargeB (bt $ x) = dischargeB bt · discharge x
dischargeB (bt $$ q) = dischargeB bt  ·⋆ _ /  q

dischargeStack-aux : ∀{A B C} → (s : VList A) → IList (∅ ⊢_) B → A <>> B ≡ C → IList (∅ ⊢_) C
dischargeStack-aux [] a refl = a
dischargeStack-aux (s :< x) a refl = dischargeStack-aux s (discharge x ∷ a) refl

dischargeStack : ∀{Ts} → IBwd Value ([] <>< Ts) → IList (_⊢_ ∅) Ts
dischargeStack bs = dischargeStack-aux bs [] (lemma<>1 [] _)

discharge (V-ƛ M ρ)  = ƛ (dischargeBody M ρ)
discharge (V-Λ M ρ)  = Λ (dischargeBody⋆ M ρ)
discharge (V-wrap V) = wrap _ _ (discharge V)
discharge (V-con c)  = con c refl
discharge (V-I⇒ b bt) = dischargeB bt
discharge (V-IΠ b bt) = dischargeB bt
discharge (V-constr i Tss s refl) = constr i Tss refl (dischargeStack s)
```

## Builtin Semantics

If a builtin returns a value, then this function produces a `Value`, otherwise it produces
a type that could be used in constructing the error term.
```
BUILTIN : ∀ b {A} → {Ab : saturatedSigTy (signature b) A} → BApp b A Ab → Either (∅ ⊢Nf⋆ *) (Value A)
BUILTIN addInteger (base $ V-con i $ V-con i') = inj₂ (V-con (i + i'))
BUILTIN subtractInteger (base $ V-con i $ V-con i') = inj₂ (V-con (i - i'))
BUILTIN multiplyInteger (base $ V-con i $ V-con i') = inj₂ (V-con (i ** i'))
BUILTIN divideInteger (base $ V-con i $ V-con i') = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con (ne (^ (atomic aInteger)))))
  (inj₂ (V-con (div i i')))
BUILTIN quotientInteger (base $ V-con i $ V-con i') = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con (ne (^ (atomic aInteger)))))
  (inj₂ (V-con (quot i i')))
BUILTIN remainderInteger (base $ V-con i $ V-con i') = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con (ne (^ (atomic aInteger)))))
  (inj₂ (V-con (rem i i')))
BUILTIN modInteger (base $ V-con i $ V-con i') = decIf
  (i' ≟ ℤ.pos 0)
   (inj₁ (con (ne (^ (atomic aInteger)))))
  (inj₂ (V-con (mod i i')))
BUILTIN lessThanInteger (base $ V-con i $ V-con i') = decIf (i <? i') (inj₂ (V-con true)) (inj₂ (V-con false))
BUILTIN lessThanEqualsInteger (base $ V-con i $ V-con i') = decIf (i ≤? i') (inj₂ (V-con true)) (inj₂ (V-con false))
BUILTIN equalsInteger (base $ V-con i $ V-con i') = decIf (i ≟ i') (inj₂ (V-con true)) (inj₂ (V-con false))
BUILTIN appendByteString (base $ V-con b $ V-con b') = inj₂ (V-con (concat b b'))
BUILTIN lessThanByteString (base $ V-con b $ V-con b') = inj₂ (V-con (B< b b'))
BUILTIN lessThanEqualsByteString (base $ V-con b $ V-con b') = inj₂ (V-con (B<= b b'))
BUILTIN sha2-256 (base $ V-con b) = inj₂ (V-con (SHA2-256 b))
BUILTIN sha3-256 (base $ V-con b) = inj₂ (V-con (SHA3-256 b))
BUILTIN blake2b-224 (base $ V-con b) = inj₂ (V-con (BLAKE2B-224 b))
BUILTIN blake2b-256 (base $ V-con b) = inj₂ (V-con (BLAKE2B-256 b))
BUILTIN keccak-256 (base $ V-con b) = inj₂ (V-con (KECCAK-256 b))
BUILTIN ripemd-160 (base $ V-con b) = inj₂ (V-con (RIPEMD-160 b))
BUILTIN verifyEd25519Signature (base $ V-con k $ V-con d $ V-con c) with (verifyEd25519Sig k d c)
... | just b = inj₂ (V-con b)
... | nothing = inj₁ (con (ne (^ (atomic aBool))))
BUILTIN verifyEcdsaSecp256k1Signature (base $ V-con k $ V-con d $ V-con c) with (verifyEcdsaSecp256k1Sig k d c)
... | just b = inj₂ (V-con b)
... | nothing = inj₁ (con (ne (^ (atomic aBool))))
BUILTIN verifySchnorrSecp256k1Signature (base $ V-con k $ V-con d $ V-con c) with (verifySchnorrSecp256k1Sig k d c)
... | just b = inj₂ (V-con b)
... | nothing = inj₁ (con (ne (^ (atomic aBool))))
BUILTIN encodeUtf8 (base $ V-con s) = inj₂ (V-con (ENCODEUTF8 s))
BUILTIN decodeUtf8 (base $ V-con b) with DECODEUTF8 b
... | nothing = inj₁ (con (ne (^ (atomic aString))))
... | just s  = inj₂ (V-con s)
BUILTIN equalsByteString (base $ V-con b $ V-con b') = inj₂ (V-con (equals b b'))
BUILTIN ifThenElse (Λ̂ A $ V-con false $ vt $ vf) = inj₂ vf
BUILTIN ifThenElse (Λ̂ A $ V-con true  $ vt $ vf) = inj₂ vt
BUILTIN appendString (base $ V-con s $ V-con s') = inj₂ (V-con (primStringAppend s s'))
BUILTIN trace (Λ̂ A $ V-con s $  v) =  inj₂ (TRACE s v)
BUILTIN iData (base $ V-con i) = inj₂ (V-con (iDATA i))
BUILTIN bData (base $ V-con b) = inj₂ (V-con (bDATA b))
BUILTIN consByteString (base $ V-con i $ V-con b) with cons i b
... | just b' = inj₂ (V-con b')
... | nothing = inj₁ (con (ne (^ (atomic aBytestring))))
BUILTIN sliceByteString (base $ V-con st $ V-con n $ V-con b) = inj₂ (V-con (slice st n b))
BUILTIN lengthOfByteString (base $ V-con b) = inj₂ (V-con (lengthBS b))
BUILTIN indexByteString (base $ V-con b $ V-con i) with Data.Integer.ℤ.pos 0 ≤? i
... | no  _ = inj₁ (con (ne (^ (atomic aInteger))))
... | yes _ with i <? lengthBS b
... | no _  = inj₁ (con (ne (^ (atomic aInteger))))
... | yes _ = inj₂ (V-con (index b i))
BUILTIN equalsString (base $ V-con s $ V-con s') = inj₂ (V-con (primStringEquality s s'))
BUILTIN unIData (base $ V-con (iDATA i)) = inj₂ (V-con i)
BUILTIN unIData (base $ V-con _) = inj₁ (con (ne (^ (atomic aData))))
BUILTIN unBData (base $ V-con (bDATA b)) = inj₂ (V-con b)
BUILTIN unBData (base $ V-con _) = inj₁ (con (ne (^ (atomic aData))))
BUILTIN unConstrData (base $ V-con (ConstrDATA i xs)) = inj₂ (V-con (i ,, xs))
BUILTIN unConstrData (base $ V-con _) = inj₁ (con (ne (^ (atomic aData))))
BUILTIN unMapData (base $ V-con (MapDATA x)) = inj₂ (V-con x)
BUILTIN unMapData (base $ V-con _) =  inj₁ (con (ne (^ (atomic aData))))
BUILTIN unListData (base $ V-con (ListDATA x)) = inj₂ (V-con x)
BUILTIN unListData (base $ V-con _) = inj₁ (con (ne (^ (atomic aData))))
BUILTIN serialiseData (base $ V-con d) = inj₂ (V-con (serialiseDATA d))
BUILTIN mkNilData (base $ V-con _) = inj₂ (V-con [])
BUILTIN mkNilPairData (base $ V-con _) = inj₂ (V-con [])
BUILTIN chooseUnit (Λ̂ A $ x $ V-con _) = inj₂ x
BUILTIN equalsData (base $ V-con d $ V-con d') = inj₂ (V-con (eqDATA d d'))
BUILTIN mkPairData (base $ V-con x $ V-con y) = inj₂ (V-con (x ,, y))
BUILTIN constrData (base $ V-con i $ V-con xs) = inj₂ (V-con (ConstrDATA i xs))
BUILTIN mapData (base $ V-con xs) = inj₂ (V-con (MapDATA xs))
BUILTIN listData (base $ V-con xs) = inj₂ (V-con (ListDATA xs))
BUILTIN fstPair (Λ̂ A ● B $ V-con (x ,, _)) = inj₂ (V-con x)
BUILTIN sndPair (Λ̂ A ● B $ V-con (_ ,, y)) = inj₂ (V-con y)
BUILTIN chooseList (Λ̂ A ● B $ V-con [] $ n $ c) = inj₂ n
BUILTIN chooseList (Λ̂ A ● B  $ V-con (x ∷ xs) $ n $ c) = inj₂ c
BUILTIN chooseList (() $$ _ $$ _ $ _ $ _)
BUILTIN chooseList (() $$ _ $$ _ $ _)
BUILTIN mkCons (Λ̂ A $ V-con x $ V-con xs) = inj₂ (V-con (x ∷ xs))
BUILTIN headList {A} (Λ̂ B $ V-con [])   = inj₁ A
BUILTIN headList (Λ̂ A $ V-con (x ∷ _)) = inj₂ (V-con x)
BUILTIN tailList (Λ̂ A $ V-con []) = inj₁ (con (ne ((^ list) · A)))
BUILTIN tailList (Λ̂ A $ V-con (_ ∷ xs)) = inj₂ (V-con xs)
BUILTIN nullList (Λ̂ B $ V-con []) = inj₂ (V-con true)
BUILTIN nullList (Λ̂ B $ V-con (_ ∷ _)) = inj₂ (V-con false)
BUILTIN lengthOfArray (Λ̂ A $ V-con as) = inj₂ (V-con (Utils.HSlengthOfArray as))
BUILTIN listToArray (Λ̂ A $ V-con ls) = inj₂ (V-con (Utils.HSlistToArray ls))
BUILTIN indexArray {A = A'} (Λ̂ A $ V-con as $ V-con i) with Data.Integer.ℤ.pos 0 ≤? i
... | no  _ = inj₁ (con A)
... | yes _ with i <? Utils.HSlengthOfArray as
... | no _  = inj₁ (con A)
... | yes _ = inj₂ (V-con (Utils.HSindexArray as i))
BUILTIN chooseData (Λ̂ A $ V-con (ConstrDATA _ _) $ c $ _ $ _ $ _ $ _) = inj₂ c
BUILTIN chooseData (Λ̂ A $ V-con (MapDATA _)      $ _ $ m $ _ $ _ $ _) = inj₂ m
BUILTIN chooseData (Λ̂ A $ V-con (ListDATA _)     $ _ $ _ $ l $ _ $ _) = inj₂ l
BUILTIN chooseData (Λ̂ A $ V-con (iDATA _)        $ _ $ _ $ _ $ i $ _) = inj₂ i
BUILTIN chooseData (Λ̂ A $ V-con (bDATA _)        $ _ $ _ $ _ $ _ $ b) = inj₂ b
BUILTIN bls12-381-G1-add (base $ V-con e $ V-con e') = inj₂ (V-con (BLS12-381-G1-add e e'))
BUILTIN bls12-381-G1-neg (base $ V-con e) = inj₂ (V-con (BLS12-381-G1-neg e))
BUILTIN bls12-381-G1-scalarMul (base $ V-con i $ V-con e) = inj₂ (V-con (BLS12-381-G1-scalarMul i e))
BUILTIN bls12-381-G1-equal (base $ V-con e $ V-con e') = inj₂ (V-con (BLS12-381-G1-equal e e'))
BUILTIN bls12-381-G1-hashToGroup (base $ V-con msg $ V-con dst) with BLS12-381-G1-hashToGroup msg dst
... | nothing = inj₁ (con (ne (^ (atomic aBls12-381-g1-element))))
... | just p  = inj₂ (V-con p)
BUILTIN bls12-381-G1-compress (base $ V-con e) = inj₂ (V-con (BLS12-381-G1-compress e))
BUILTIN bls12-381-G1-uncompress (base $ V-con b) with BLS12-381-G1-uncompress b
... | nothing = inj₁ (con (ne (^ (atomic aBls12-381-g1-element))))
... | just e  = inj₂ (V-con e)
BUILTIN bls12-381-G2-add (base $ V-con e $ V-con e') = inj₂ (V-con (BLS12-381-G2-add e e'))
BUILTIN bls12-381-G2-neg (base $ V-con e) = inj₂ (V-con (BLS12-381-G2-neg e))
BUILTIN bls12-381-G2-scalarMul (base $ V-con i $ V-con e) = inj₂ (V-con (BLS12-381-G2-scalarMul i e))
BUILTIN bls12-381-G2-equal (base $ V-con e $ V-con e') = inj₂ (V-con (BLS12-381-G2-equal e e'))
BUILTIN bls12-381-G2-hashToGroup (base $ V-con msg $ V-con dst) with BLS12-381-G2-hashToGroup msg dst
... | nothing = inj₁ (con (ne (^ (atomic aBls12-381-g2-element))))
... | just p  = inj₂ (V-con p)
BUILTIN bls12-381-G2-compress (base $ V-con e) = inj₂ (V-con (BLS12-381-G2-compress e))
BUILTIN bls12-381-G2-uncompress (base $ V-con b) with BLS12-381-G2-uncompress b
... | nothing = inj₁ (con (ne (^ (atomic aBls12-381-g2-element))))
... | just e  = inj₂ (V-con e)
BUILTIN bls12-381-millerLoop (base $ V-con e1 $ V-con e2) = inj₂ (V-con (BLS12-381-millerLoop e1 e2))
BUILTIN bls12-381-mulMlResult (base $ V-con r $ V-con r') = inj₂ (V-con (BLS12-381-mulMlResult r r'))
BUILTIN bls12-381-finalVerify (base $ V-con r $ V-con r') = inj₂ (V-con (BLS12-381-finalVerify r r'))
BUILTIN byteStringToInteger (base $ V-con e $ V-con s) = inj₂ (V-con (BStoI e s))
BUILTIN integerToByteString (base $ V-con e $ V-con w $ V-con n) with ItoBS e w n
... | just s = inj₂ (V-con s)
... | nothing = inj₁ (con (ne (^ (atomic aBytestring))))
BUILTIN andByteString (base  $ V-con b $ V-con s $ V-con s') = inj₂ (V-con (andBYTESTRING b s s'))
BUILTIN orByteString  (base  $ V-con b $ V-con s $ V-con s') = inj₂ (V-con (orBYTESTRING b s s'))
BUILTIN xorByteString (base  $ V-con b $ V-con s $ V-con s') = inj₂ (V-con (xorBYTESTRING b s s'))
BUILTIN complementByteString (base $ V-con s) = inj₂ (V-con (complementBYTESTRING s))
BUILTIN readBit (base $ V-con s $ V-con i) with readBIT s i
... | just r = inj₂ (V-con r)
... | nothing  = inj₁ (con (ne (^ (atomic aBool))))
BUILTIN writeBits (base $ V-con s $ V-con ps $ V-con u) with writeBITS s (toList ps) u
... | just r = inj₂ (V-con r)
... | nothing  = inj₁ (con (ne (^ (atomic aBytestring))))
BUILTIN replicateByte (base  $ V-con l $ V-con w) with replicateBYTE l w
... | just r = inj₂ (V-con r)
... | nothing  = inj₁ (con (ne (^ (atomic aBytestring))))
BUILTIN shiftByteString (base $ V-con s $ V-con i) with shiftBYTESTRING s i
... | just r = inj₂ (V-con r)
... | nothing = inj₁ (con (ne (^ (atomic aBytestring))))
BUILTIN rotateByteString (base $ V-con s $ V-con i) with rotateBYTESTRING s i
... | just r = inj₂ (V-con r)
... | nothing = inj₁ (con (ne (^ (atomic aBytestring))))
BUILTIN countSetBits (base $ V-con  s) = inj₂ (V-con (countSetBITS s))
BUILTIN findFirstSetBit (base $ V-con s) = inj₂ (V-con (findFirstSetBIT s))
BUILTIN expModInteger (base  $ V-con b $ V-con e $ V-con m) with expModINTEGER b e m
... | just r = inj₂ (V-con r)
... | nothing  = inj₁ (con (ne (^ (atomic aInteger))))
BUILTIN dropList (Λ̂ A $ V-con n $ V-con l) = inj₂ (V-con (dropLIST n l))
BUILTIN bls12-381-G1-multiScalarMul (base $ V-con is $ V-con es) with BLS12-381-G1-multiScalarMul (toList is) (toList es)
... | just r = inj₂ (V-con r)
... | nothing = inj₁ (con (ne (^ (atomic aBls12-381-g1-element))))
BUILTIN bls12-381-G2-multiScalarMul (base $ V-con is $ V-con es) with BLS12-381-G2-multiScalarMul (toList is) (toList es)
... | just r = inj₂ (V-con r)
... | nothing = inj₁ (con (ne (^ (atomic aBls12-381-g2-element))))
BUILTIN' : ∀ b {A}
  → ∀{tn} → {pt : tn ∔ 0 ≣ fv (signature b)}
  → ∀{an} → {pa : an ∔ 0 ≣ args♯ (signature b)}
  → {σA : SigTy pt pa A}
  → BApp b A σA
  → ∅ ⊢ A
BUILTIN' b {pt = pt} {pa = pa} bt with trans (sym (+-identityʳ _)) (∔2+ pt) | trans (sym (+-identityʳ _)) (∔2+ pa)
... | refl | refl with unique∔ pt (alldone (fv (signature b))) | unique∔ pa (alldone (args♯ (signature b)))
... | refl | refl with BUILTIN b bt
... | inj₁ A = error _
... | inj₂ V = discharge V
```

```
V-I : ∀ (b : Builtin) {A : ∅ ⊢Nf⋆ *}
       → ∀{tn tm} {pt : tn ∔ tm ≣ fv (signature b)}
       → ∀{an am} {pa : an ∔ suc am ≣ args♯ (signature b)}
       → {σA : SigTy pt pa A}
       → BApp b A σA
       → Value A
V-I b {tm = zero} {σA = A B⇒ σA} bt = V-I⇒ b bt
V-I b {tm = suc tm} {σA = sucΠ σA} bt = V-IΠ b bt

data Error : ∅ ⊢Nf⋆ * → Set where
  -- an actual error term
  E-error : (A : ∅ ⊢Nf⋆ *) → Error A
```

## Frames

```
data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·      : ∀{Γ}{A B : ∅ ⊢Nf⋆ *} → Γ ⊢ A → Env Γ → Frame B (A ⇒ B)
  -·v     : ∀{A B : ∅ ⊢Nf⋆ *} → Value A → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *} → Value (A ⇒ B) → Frame B A

  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K)
    → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (μ A B)
            (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  unwrap- : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
            (μ A B)
  constr- : ∀{Γ n Vs H Ts}
          → (i : Fin n)
          → (Tss : Vec _ n)
          → Env Γ
          → ∀{Xs} → (Xs ≡ Vec.lookup Tss i)
          → {tidx : Xs ≣ Vs <>> (H ∷ Ts)} → VList Vs → ConstrArgs Γ Ts
          → Frame (SOP Tss) H
  case- : ∀{Γ A n}{Tss : Vec _ n} → (ρ : Env Γ) → Cases Γ A Tss → Frame A (SOP Tss)

data Stack (T : ∅ ⊢Nf⋆ *) : (H : ∅ ⊢Nf⋆ *) → Set where
  ε   : Stack T T
  _,_ : ∀{H1 H2} → Stack T H1 → Frame H1 H2 → Stack T H2

data State (T : ∅ ⊢Nf⋆ *) : Set where
  _;_▻_ : ∀{Γ}{H : ∅ ⊢Nf⋆ *} → Stack T H → Env Γ → Γ ⊢ H → State T
  _◅_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → Value H → State T
  □     : Value T → State T
  ◆     : ∅ ⊢Nf⋆ * → State T

ival : ∀(b : Builtin) → Value (btype b)
ival b = V-I b base

pushValueFrames : ∀{T H Bs Xs} → Stack T H → VList Bs → Xs ≡ bwdMkCaseType Bs H → Stack T Xs
pushValueFrames s [] refl = s
pushValueFrames s (vs :< v) refl = pushValueFrames (s , -·v v) vs refl

step : ∀{T} → State T → State T
step (s ; ρ ▻ ` x) = s ◅ lookup x ρ
step (s ; ρ ▻ ƛ L) = s ◅ V-ƛ L ρ
step (s ; ρ ▻ (L · M)) = (s , -· M ρ) ; ρ ▻ L
step (s ; ρ ▻ Λ L) = s ◅ V-Λ L ρ
step (s ; ρ ▻ (L ·⋆ A / refl)) = (s , -·⋆ A) ; ρ ▻ L
step (s ; ρ ▻ wrap A B L) = (s , wrap-) ; ρ ▻ L
step (s ; ρ ▻ unwrap L refl) = (s , unwrap-) ; ρ ▻ L
step (s ; ρ ▻ con c refl) = s ◅ V-con c
step (s ; ρ ▻ (builtin b / refl)) = s ◅ ival b
step (s ; ρ ▻ error A) = ◆ A
step (s ; ρ ▻ constr e Tss refl as) with Vec.lookup Tss e in eq
step (s ; ρ ▻ constr e Tss refl []) | []  = s ◅ V-constr e Tss [] (cong ([] <><_) (sym eq))
step (_;_▻_ {Γ} s ρ (constr e Tss refl (_∷_ {xty} {xsty} x xs))) | _ ∷ _ = (s , constr- e Tss ρ (sym eq) {start} [] xs) ; ρ ▻ x
step (s ; ρ ▻ case t ts) = (s , case- ρ ts) ; ρ ▻ t
step (ε ◅ V) = □ V
step ((s , -· M ρ') ◅ V) = (s , V ·-) ; ρ' ▻ M
step ((s , -·v v) ◅ vf)  = (s , vf ·-) ◅ v
step ((s , (V-ƛ M ρ ·-)) ◅ V) = s ; ρ ∷ V ▻ M
step ((s , (V-I⇒ b {am = 0} bapp ·-)) ◅ V) = s ; [] ▻ (BUILTIN' b (bapp $ V))
step ((s , (V-I⇒ b {am = suc _} bapp ·-)) ◅ V) = s ◅ V-I b (bapp $ V)
step ((s , -·⋆ A) ◅ V-Λ M ρ) = s ; ρ ▻ (M [ A ]⋆)
step ((s , -·⋆ A) ◅ V-IΠ b {σB = σ} bapp) = s ◅ V-I b (_$$_ bapp refl {σ [ A ]SigTy})
step ((s , wrap-) ◅ V) = s ◅ V-wrap V
step ((s , unwrap-) ◅ V-wrap V) = s ◅ V
step ((s , constr- i Tss ρ refl {tidx} vs ts) ◅ v)
    with Vec.lookup Tss i in eq
... | [] with no-empty-≣-<>> tidx
... | ()
step ((s , constr- i Tss ρ refl {r} vs []) ◅ v) | A ∷ As  = s ◅ V-constr i Tss (vs :< v)
                 (sym (trans (cong ([] <><_) (trans eq (lem-≣-<>> r))) (lemma<>2 _ (_ ∷ []))))
step ((s , constr- i Tss ρ refl {r} vs (t ∷ ts)) ◅ v) | A ∷ As = (s , constr- i Tss ρ (sym eq) {bubble r} (vs :< v) ts) ; ρ ▻ t
step {t} ((s , case- ρ cases) ◅ V-constr e Tss vs refl) = pushValueFrames s vs (lemma-bwdfwdfunction' (Vec.lookup Tss e)) ; ρ ▻ (lookupCase e cases)
step (□ V) = □ V
step (◆ A) = ◆ A


stepper : ℕ → ∀{T} → State T → Either RuntimeError (State T)
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ; ρ ▻ M) = stepper n (s ; ρ ▻ M)
stepper (suc n) st | (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)
