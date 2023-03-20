# CEK machine that discharges builtin args

```
module Algorithmic.CEK where

open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Properties using (+-identityʳ)
open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Function using (_∘_)
--open import Data.Product using (proj₁;proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;cong;trans) 
                                                  renaming (subst to substEq)
open import Data.Unit using (⊤;tt)
open import Data.Product using (_×_;Σ) 
                         renaming (_,_ to _,,_)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) 
                         renaming (_*_ to _**_)
open import Data.Bool using (true;false)
open import Relation.Nullary using (no;yes)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z;S)
open _⊢⋆_
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;embNf;weakenNf)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf;subNf-id;subNf-cong;extsNf)
open import Algorithmic using (Ctx;_⊢_;_∋_;conv⊢;builtin_/_)
open import Algorithmic.Signature using (btype;_[_]SigTy)
open Ctx
open _⊢_
open _∋_
open import Algorithmic.RenamingSubstitution using (Sub;sub;exts;exts⋆;_[_];_[_]⋆)
open import Builtin
open import Utils hiding (TermCon)

open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) using (TyCon)
open TyCon

open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con using (TermCon)
open TermCon

open import Builtin.Signature using (Sig;sig;Args;_⊢♯;nat2Ctx⋆;fin2∈⋆;args♯)
open Sig

open Builtin.Signature.FromSig Ctx⋆ (_⊢Nf⋆ *) nat2Ctx⋆ (λ x → ne (` (fin2∈⋆ x))) con _⇒_ Π 
    using (sig2type;♯2*;SigTy;sig2SigTy;saturatedSigTy;convSigTy)
open SigTy

data Env : Ctx ∅ → Set

data BApp (b : Builtin) : 
    ∀{tn tm tt} → {pt : tn ∔ tm ≣ tt}
  → ∀{an am at} → {pa : an ∔ am ≣ at}
  → (A : ∅ ⊢Nf⋆ *) → SigTy pt pa A → Set

data Value : (A : ∅ ⊢Nf⋆ *) → Set where
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

  V-con : {tcn : TyCon _}
    → (cn : TermCon {∅} (con tcn))
    → Value (con tcn)

  V-I⇒ : ∀ b {A B}{tn}
       → {pt : tn ∔ 0 ≣ fv♯ (signature b)} 
       → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
       → {σB : SigTy pt (bubble pa) B}
       → BApp b (A ⇒ B) (A B⇒ σB)
       → Value (A ⇒ B)

  V-IΠ : ∀ b {B : ∅ ,⋆ * ⊢Nf⋆ *}
       → ∀{tn tm} {pt : tn ∔ (suc tm) ≣ fv♯ (signature b)} 
       → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
       → {σB : SigTy (bubble pt) pa B}
       → BApp b (Π B) (sucΠ σB)
       → Value (Π B)

data BApp b where
  base : BApp b (sig2type (signature b)) (sig2SigTy (signature b))
  app : ∀{A B}{tn}
    → {pt : tn ∔ 0 ≣ fv♯ (signature b)} 
    → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
    → {σB : SigTy pt (bubble pa) B}
    → BApp b (A ⇒ B) (A B⇒ σB)
    → Value A 
    → BApp b B σB
  app⋆ : ∀{B C}
    → ∀{tn tm} {pt : tn ∔ (suc tm) ≣ fv♯ (signature b)} 
    → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
    → {σB : SigTy (bubble pt) pa B}
    → BApp b (Π B) (sucΠ σB)
    → {A : ∅ ⊢Nf⋆ *}
    → (q : C ≡ B [ A ]Nf)
    → {σC : SigTy (bubble pt) pa C}
    → (σq : σC ≡ convSigTy (sym q) (σB [ A ]SigTy))
    → BApp b C σC
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

dischargeB : ∀(b : Builtin)
          → ∀{tn tm} → {pt : tn ∔ tm ≣ fv♯ (signature b)}
          → ∀{an am} → {pa : an ∔ am ≣ args♯ (signature b)}
          → ∀{C} → {Cb : SigTy pt pa C} → (bp : BApp b C Cb) 
          → ∅ ⊢ C
dischargeB b base = builtin b / refl
dischargeB b (app bt x) = dischargeB b bt · discharge x
dischargeB b (app⋆ bt q _) = dischargeB b bt  ·⋆ _ /  q

discharge (V-ƛ M ρ)  = ƛ (dischargeBody M ρ)
discharge (V-Λ M ρ)  = Λ (dischargeBody⋆ M ρ)
discharge (V-wrap V) = wrap _ _ (discharge V)
discharge (V-con c)  = con c
discharge (V-I⇒ b bt) = dischargeB b bt
discharge (V-IΠ b bt) = dischargeB b bt 
```

## Builtin Semantics

```
BUILTIN : ∀ b {A} → {Ab : saturatedSigTy (signature b) A} → BApp b A Ab → Either (∅ ⊢Nf⋆ *) (Value A)
BUILTIN addInteger (app (app base (V-con (integer i))) (V-con (integer i'))) = inj₂ (V-con (integer (i + i')))
BUILTIN subtractInteger (app (app base (V-con (integer i))) (V-con (integer i'))) = inj₂ (V-con (integer (i - i')))
BUILTIN multiplyInteger (app (app base (V-con (integer i))) (V-con (integer i'))) = inj₂ (V-con (integer (i ** i')))
BUILTIN divideInteger (app (app base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (integer (div i i'))))
BUILTIN quotientInteger (app (app base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (integer (quot i i'))))
BUILTIN remainderInteger (app (app base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (integer (rem i i'))))
BUILTIN modInteger (app (app base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (integer (mod i i'))))
BUILTIN lessThanInteger (app (app base (V-con (integer i))) (V-con (integer i'))) = decIf (i <? i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
BUILTIN lessThanEqualsInteger (app (app base (V-con (integer i))) (V-con (integer i'))) = decIf (i ≤? i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
BUILTIN equalsInteger (app (app base (V-con (integer i))) (V-con (integer i'))) = decIf (i ≟ i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
BUILTIN appendByteString (app (app base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bytestring (concat b b')))
BUILTIN lessThanByteString (app (app base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bool (B< b b')))
BUILTIN lessThanEqualsByteString (app (app base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bool (B<= b b')))
BUILTIN sha2-256 (app base (V-con (bytestring b))) = inj₂ (V-con
  (bytestring (SHA2-256 b)))
BUILTIN sha3-256 (app base (V-con (bytestring b))) =
  inj₂ (V-con (bytestring (SHA3-256 b)))
BUILTIN blake2b-256 (app base (V-con (bytestring b))) =
  inj₂ (V-con (bytestring (BLAKE2B-256 b)))
BUILTIN verifyEd25519Signature (app (app (app base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) with (verifyEd25519Sig k d c)
... | just b = inj₂ (V-con (bool b))
... | nothing = inj₁ (con bool)
BUILTIN verifyEcdsaSecp256k1Signature (app (app (app base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) with (verifyEcdsaSecp256k1Sig k d c)
... | just b = inj₂ (V-con (bool b))
... | nothing = inj₁ (con bool)
BUILTIN verifySchnorrSecp256k1Signature (app (app (app base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) with (verifySchnorrSecp256k1Sig k d c)
... | just b = inj₂ (V-con (bool b))
... | nothing = inj₁ (con bool)
BUILTIN encodeUtf8 (app base (V-con (string s))) =
  inj₂ (V-con (bytestring (ENCODEUTF8 s)))
BUILTIN decodeUtf8 (app base (V-con (bytestring b))) with DECODEUTF8 b
... | nothing = inj₁ (con string)
... | just s  = inj₂ (V-con (string s))
BUILTIN equalsByteString (app (app base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bool (equals b b')))
BUILTIN ifThenElse (app (app (app (app⋆ base refl refl) (V-con (bool false))) vt) vf) = inj₂ vf
BUILTIN ifThenElse (app (app (app (app⋆ base refl refl) (V-con (bool true))) vt) vf) = inj₂ vt
BUILTIN appendString (app (app base (V-con (string s))) (V-con (string s'))) = inj₂ (V-con (string (primStringAppend s s')))
BUILTIN trace (app (app (app⋆ base refl refl) (V-con (string s))) v) =
  inj₂ (TRACE s v)
BUILTIN iData (app base (V-con (integer i))) =
  inj₂ (V-con (pdata (iDATA i)))
BUILTIN bData (app base (V-con (bytestring b))) =
  inj₂ (V-con (pdata (bDATA b)))
BUILTIN consByteString (app (app base (V-con (integer i))) (V-con (bytestring b))) = inj₂ (V-con (bytestring (cons i b)))
BUILTIN sliceByteString (app (app (app base (V-con (integer st))) (V-con (integer n))) (V-con (bytestring b))) = inj₂ (V-con (bytestring (slice st n b)))
BUILTIN lengthOfByteString (app base (V-con (bytestring b))) =
  inj₂ (V-con (integer (length b)))
BUILTIN indexByteString (app (app base (V-con (bytestring b))) (V-con (integer i))) with Data.Integer.ℤ.pos 0 ≤? i
... | no  _ = inj₁ (con integer)
... | yes _ with i <? length b
... | no _  = inj₁ (con integer)
... | yes _ = inj₂ (V-con (integer (index b i)))
BUILTIN equalsString (app (app base (V-con (string s))) (V-con (string s'))) = inj₂ (V-con (bool (primStringEquality s s')))
BUILTIN unIData (app base (V-con (pdata (iDATA i)))) = inj₂ (V-con (integer i))
BUILTIN unBData (app base (V-con (pdata (bDATA b)))) =
  inj₂ (V-con (bytestring b))
BUILTIN serialiseData (app base (V-con (pdata d))) =
  inj₂ (V-con (bytestring (serialiseDATA d)))
BUILTIN _ {A = A} _ = inj₁ A

BUILTIN' : ∀ b {A}
  → ∀{tn} → {pt : tn ∔ 0 ≣ fv♯ (signature b)}
  → ∀{an} → {pa : an ∔ 0 ≣ args♯ (signature b)}
  → {σA : SigTy pt pa A}
  → BApp b A σA
  → ∅ ⊢ A
BUILTIN' b {pt = pt} {pa = pa} bt with trans (sym (+-identityʳ _)) (∔2+ pt) | trans (sym (+-identityʳ _)) (∔2+ pa)
... | refl | refl with unique∔ pt (alldone (fv♯ (signature b))) | unique∔ pa (alldone (args♯ (signature b)))
... | refl | refl with BUILTIN b bt
... | inj₁ A = error _
... | inj₂ V = discharge V
```

<<<<<<< HEAD
postulate bappTermLem : ∀  b {A}{az as}(p : az <>> (Term ∷ as) ∈ arity b) → BApp b p A → ∃ λ A' → ∃ λ A'' → A ≡ A' ⇒ A''

{-
bappTermLem addInteger _ base = _ ,, _ ,, refl
bappTermLem addInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem addInteger {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem addInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem subtractInteger _ base = _ ,, _ ,, refl
bappTermLem subtractInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem subtractInteger {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem subtractInteger {as = as} (bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem multiplyInteger _ base = _ ,, _ ,, refl
bappTermLem multiplyInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem multiplyInteger {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem multiplyInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem divideInteger _ base = _ ,, _ ,, refl
bappTermLem divideInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem divideInteger {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem divideInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem quotientInteger _ base = _ ,, _ ,, refl
bappTermLem quotientInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem quotientInteger {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem quotientInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem remainderInteger _ base = _ ,, _ ,, refl
bappTermLem remainderInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem remainderInteger {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem remainderInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem modInteger _ base = _ ,, _ ,, refl
bappTermLem modInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem modInteger {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem modInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem lessThanInteger _ base = _ ,, _ ,, refl
bappTermLem lessThanInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem lessThanInteger {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem lessThanInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem lessThanEqualsInteger _ base = _ ,, _ ,, refl
bappTermLem lessThanEqualsInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem lessThanEqualsInteger {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem lessThanEqualsInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem equalsInteger _ base = _ ,, _ ,, refl
bappTermLem equalsInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem equalsInteger {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem equalsInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem appendByteString _ base = _ ,, _ ,, refl
bappTermLem appendByteString {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem appendByteString {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem appendByteString {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem lessThanByteString _ base = _ ,, _ ,, refl
bappTermLem lessThanByteString {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem lessThanByteString {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem lessThanByteString {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()

bappTermLem lessThanEqualsByteString _ base = _ ,, _ ,, refl
bappTermLem lessThanEqualsByteString {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem lessThanEqualsByteString {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem lessThanEqualsByteString {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem sha2-256 {az = az} {as} p q with <>>-cancel-both az ([] :< Term) as p
bappTermLem sha2-256 {az = .[]} {.[]} .(start (Term ∷ [])) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem sha3-256 {az = az} {as} p q with <>>-cancel-both az ([] :< Term) as p
bappTermLem sha3-256 {az = .[]} {.[]} .(start (Term ∷ [])) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem verifyEd25519Signature .(start (Term ∷ Term ∷ Term ∷ [])) base = _ ,, _ ,, refl
bappTermLem verifyEd25519Signature .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (app .(start (Term ∷ Term ∷ Term ∷ [])) base x) = _ ,, _ ,, refl
bappTermLem verifyEd25519Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x₁) x) with <>>-cancel-both az ((([] :< Term) :< Term) :< Term) as p
bappTermLem verifyEd25519Signature {as = .[]} (bubble (bubble .(start (Term ∷ Term ∷ Term ∷ [])))) (app .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (app {az = _} .(start (Term ∷ Term ∷ Term ∷ [])) base x₁) x) | refl ,, refl = _ ,, _ ,, refl
bappTermLem verifyEd25519Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₁₁) x) with <>>-cancel-both' az ((([] :< Type) :< Term) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifyEd25519Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₁) q₁)  with <>>-cancel-both' az ((([] :< Term) :< Type) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifyEd25519Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₂) q₁) with <>>-cancel-both' az ((([] :< Type) :< Type) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifyEcdsaSecp256k1Signature .(start (Term ∷ Term ∷ Term ∷ [])) base = _ ,, _ ,, refl
bappTermLem verifyEcdsaSecp256k1Signature .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (app .(start (Term ∷ Term ∷ Term ∷ [])) base x) = _ ,, _ ,, refl
bappTermLem verifyEcdsaSecp256k1Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x₁) x) with <>>-cancel-both az ((([] :< Term) :< Term) :< Term) as p
bappTermLem verifyEcdsaSecp256k1Signature {as = .[]} (bubble (bubble .(start (Term ∷ Term ∷ Term ∷ [])))) (app .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (app {az = _} .(start (Term ∷ Term ∷ Term ∷ [])) base x₁) x) | refl ,, refl = _ ,, _ ,, refl
bappTermLem verifyEcdsaSecp256k1Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₁₁) x) with <>>-cancel-both' az ((([] :< Type) :< Term) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifyEcdsaSecp256k1Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₁) q₁)  with <>>-cancel-both' az ((([] :< Term) :< Type) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifyEcdsaSecp256k1Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₂) q₁) with <>>-cancel-both' az ((([] :< Type) :< Type) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifySchnorrSecp256k1Signature .(start (Term ∷ Term ∷ Term ∷ [])) base = _ ,, _ ,, refl
bappTermLem verifySchnorrSecp256k1Signature .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (app .(start (Term ∷ Term ∷ Term ∷ [])) base x) = _ ,, _ ,, refl
bappTermLem verifySchnorrSecp256k1Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x₁) x) with <>>-cancel-both az ((([] :< Term) :< Term) :< Term) as p
bappTermLem verifySchnorrSecp256k1Signature {as = .[]} (bubble (bubble .(start (Term ∷ Term ∷ Term ∷ [])))) (app .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (app {az = _} .(start (Term ∷ Term ∷ Term ∷ [])) base x₁) x) | refl ,, refl = _ ,, _ ,, refl
bappTermLem verifySchnorrSecp256k1Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₁₁) x) with <>>-cancel-both' az ((([] :< Type) :< Term) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifySchnorrSecp256k1Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₁) q₁)  with <>>-cancel-both' az ((([] :< Term) :< Type) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifySchnorrSecp256k1Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₂) q₁) with <>>-cancel-both' az ((([] :< Type) :< Type) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem equalsByteString _ base = _ ,, _ ,, refl
bappTermLem equalsByteString {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem equalsByteString {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem equalsByteString {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x₂) x₁) x) with <>>-cancel-both' az (((([] :< Term) :< Term) :< Term) :< Term) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₁) x₁) x) with <>>-cancel-both az (((([] :< Type) :< Term) :< Term) :< Term) as p
bappTermLem ifThenElse {as = .[]} (bubble (bubble (bubble .(start (Type ∷ Term ∷ Term ∷ Term ∷ []))))) (app .(bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ [])))) (app .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) (app⋆ {az = _} .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl) x₁) x) | refl ,, refl = _ ,, _ ,, refl
bappTermLem ifThenElse .(bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ [])))) (app .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) (app⋆ (start .(Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl) x) = _ ,, _ ,, refl
bappTermLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app .(bubble (bubble p)) (app⋆ (bubble {as = as₁} p) q q₁₁) x) with <>>-cancel-both' as₁ (((([] :< _) :< Type) :< Term) :< Term) (((([] :< Type) :< Term) :< Term) :< Term)as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) (app⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl) = _ ,, _ ,, refl
bappTermLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app⋆ .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x₂) x₁) q₁) with <>>-cancel-both' az (((([] :< Term) :< Term) :< Type) :< Term) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app⋆ .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₂) x₁) q₁) with <>>-cancel-both' az (((([] :< Type) :< Term) :< Type) :< Term) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app⋆ .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₂) q₂) q₁) with <>>-cancel-both' az (((([] :< Term) :< Type) :< Type) :< Term) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app⋆ .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₃) q₂) q₁) with <>>-cancel-both' az (((([] :< Type) :< Type) :< Type) :< Term) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem appendString _ base = _ ,, _ ,, refl
bappTermLem appendString {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both az (([] :< Term) :< Term) as p
bappTermLem appendString {as = .[]} (bubble (start .(Term ∷ Term ∷ []))) (app {az = _} (start .(Term ∷ Term ∷ [])) base x)
  | refl ,, refl = _ ,, _ ,, refl
bappTermLem appendString {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Term) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem trace (bubble (start _)) (app⋆ _ base refl) = _ ,, _ ,, refl
bappTermLem trace {as = as} (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ([] <>< arity trace) _ p refl
bappTermLem trace (bubble (bubble (start _))) (app _ (app⋆ _ base refl) v) | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem equalsString (start _) base = _ ,, _ ,, refl
bappTermLem equalsString {as = as} (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem equalsString (bubble (start _)) (app _ base _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem encodeUtf8 {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem encodeUtf8 (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem decodeUtf8 {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem decodeUtf8 (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem fstPair (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ([] <>< arity fstPair) _ p refl
bappTermLem fstPair
            (bubble (bubble (start _)))
            (app⋆ _ (app⋆ _ base refl) refl)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem sndPair (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ([] <>< arity fstPair) _ p refl
bappTermLem sndPair
            (bubble (bubble (start _)))
            (app⋆ _ (app⋆ _ base refl) refl)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem nullList (bubble {as = az} p) q
  with <>>-cancel-both' az _ ([] <>< arity nullList) _ p refl
bappTermLem nullList (bubble (start _)) (app⋆ _ base refl)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem headList (bubble {as = az} p) q
  with <>>-cancel-both' az _ ([] <>< arity nullList) _ p refl
bappTermLem headList (bubble (start _)) (app⋆ _ base refl)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem tailList (bubble {as = az} p) q
  with <>>-cancel-both' az _ ([] <>< arity nullList) _ p refl
bappTermLem tailList (bubble (start _)) (app⋆ _ base refl)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem chooseList
            (bubble (bubble (start _)))
            (app⋆ _ (app⋆ _ base refl) refl)
            = _ ,, _ ,, refl
bappTermLem chooseList
            (bubble (bubble (bubble (start _))))
            (app _ (app⋆ _ (app⋆ _ base refl) refl) x)
            = _ ,, _ ,, refl
bappTermLem chooseList (bubble (bubble (bubble (bubble {as = az} p)))) q
  with <>>-cancel-both' az _ ([] <>< arity chooseList) _ p refl
bappTermLem chooseList
            (bubble (bubble (bubble (bubble (start _)))))
            (app _ (app _ (app⋆ _ (app⋆ _ base refl) refl) _) _)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem constrData (start _) base = _ ,, _ ,, refl
bappTermLem constrData {as = as} (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem constrData (bubble (start _)) (app _ base _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem mapData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem mapData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem listData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem listData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem iData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem iData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem bData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem bData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem unConstrData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem unConstrData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem unMapData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem unMapData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem unListData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem unListData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem unIData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem unIData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem unBData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem unBData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem equalsData (start _) base = _ ,, _ ,, refl
bappTermLem equalsData {as = as} (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem equalsData (bubble (start _)) (app _ base _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem serialiseData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem serialiseData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem chooseData (bubble (start _)) (app⋆ _ base refl) =
  _ ,, _ ,, refl
bappTermLem chooseData
            (bubble (bubble (start _)))
            (app _ (app⋆ _ base refl) _)
            = _ ,, _ ,, refl
bappTermLem chooseData
            (bubble (bubble (bubble (start _))))
            (app _ (app _ (app⋆ _ base refl) _) _)
            = _ ,, _ ,, refl
bappTermLem chooseData
            (bubble (bubble (bubble (bubble (start _)))))
            (app _ (app _ (app _ (app⋆ _ base refl) _) _) _)
            = _ ,, _ ,, refl
bappTermLem chooseData
            (bubble (bubble (bubble (bubble (bubble (start _))))))
            (app _ (app _ (app _ (app _ (app⋆ _ base refl) _) _) _) _)
            = _ ,, _ ,, refl
bappTermLem chooseData
            (bubble (bubble (bubble (bubble (bubble (bubble {as = az} p)))))) q
  with <>>-cancel-both' az _ ([] <>< arity chooseData) _ p refl
bappTermLem
  chooseData
  (bubble (bubble (bubble (bubble (bubble (bubble (start _)))))))
  (app _ (app _ (app _ (app _ (app _ (app⋆ _ base refl)_)_)_)_)_)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem chooseUnit (bubble (start _)) (app⋆ _ base refl) =
  _ ,, _ ,, refl
bappTermLem chooseUnit (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Type) :< Term) :< Term) _ p refl
bappTermLem chooseUnit
            (bubble (bubble (start _)))
            (app _ (app⋆ _ base refl) x)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem mkPairData (start _) base = _ ,, _ ,, refl
bappTermLem mkPairData {as = as} (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem mkPairData (bubble (start _)) (app _ base _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem mkNilData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem mkNilData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem mkNilPairData {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem mkNilPairData (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem mkCons (bubble (start _)) (app⋆ _ base refl) =
  _ ,, _ ,, refl
bappTermLem mkCons (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Type) :< Term) :< Term) _ p refl
bappTermLem mkCons
            (bubble (bubble (start _)))
            (app _ (app⋆ _ base refl) x)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem consByteString (start _) base = _ ,, _ ,, refl
bappTermLem consByteString {as = as} (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem consByteString (bubble (start _)) (app _ base _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem sliceByteString (start _) base = _ ,, _ ,, refl
bappTermLem sliceByteString (bubble (start _)) (app (start _) base _) =
  _ ,, _ ,, refl
bappTermLem sliceByteString {as = as} (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Term) :< Term) :< Term) as p refl
bappTermLem sliceByteString
            (bubble (bubble (start _)))
            (app _ (app _ base _) _)
            | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem lengthOfByteString {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem lengthOfByteString (start _) base | refl ,, refl = _ ,, _ ,, refl
bappTermLem indexByteString (start _) base = _ ,, _ ,, refl
bappTermLem indexByteString {as = as} (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem indexByteString (bubble (start _)) (app _ base _)
  | refl ,, refl ,, refl = _ ,, _ ,, refl
bappTermLem blake2b-256 {az = az} {as} p q
  with <>>-cancel-both az ([] :< Term) as p
bappTermLem blake2b-256 (start _) base | refl ,, refl = _ ,, _ ,, refl
-}

postulate bappTypeLem : ∀  b {A}{az as}(p : az <>> (Type ∷ as) ∈ arity b) → BApp b p A → ∃ λ K → ∃ λ (B : ∅ ,⋆ K ⊢Nf⋆ *) → A ≡ Π B

{-
bappTypeLem addInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem addInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()

bappTypeLem subtractInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem subtractInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()

bappTypeLem multiplyInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem multiplyInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()

bappTypeLem divideInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem divideInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()

bappTypeLem quotientInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem quotientInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()

bappTypeLem remainderInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem remainderInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem modInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem modInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem lessThanInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanEqualsInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem lessThanEqualsInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem equalsInteger {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem equalsInteger {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem appendByteString {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem appendByteString {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanByteString {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem lessThanByteString {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem lessThanEqualsByteString {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem lessThanEqualsByteString {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem sha2-256 {az = az} {as} p q
  with <>>-cancel-both' az ([] :< Type) ([] :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem sha3-256 {az = az} {as} p q
  with <>>-cancel-both' az ([] :< Type) ([] :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifyEd25519Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x) x')
  with <>>-cancel-both' az ((([] :< Term) :< Term) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifyEd25519Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₁₁) x)
  with <>>-cancel-both' az ((([] :< Type) :< Term) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifyEd25519Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₁) q₁) with <>>-cancel-both' az ((([] :< Term) :< Type) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifyEd25519Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₂) q₁) with <>>-cancel-both' az ((([] :< Type) :< Type) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifyEcdsaSecp256k1Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x) x')
  with <>>-cancel-both' az ((([] :< Term) :< Term) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifyEcdsaSecp256k1Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₁₁) x)
  with <>>-cancel-both' az ((([] :< Type) :< Term) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifyEcdsaSecp256k1Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₁) q₁) with <>>-cancel-both' az ((([] :< Term) :< Type) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifyEcdsaSecp256k1Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₂) q₁) with <>>-cancel-both' az ((([] :< Type) :< Type) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySchnorrSecp256k1Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x) x')
  with <>>-cancel-both' az ((([] :< Term) :< Term) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySchnorrSecp256k1Signature {as = as} .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₁₁) x)
  with <>>-cancel-both' az ((([] :< Type) :< Term) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySchnorrSecp256k1Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₁) q₁) with <>>-cancel-both' az ((([] :< Term) :< Type) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySchnorrSecp256k1Signature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₂) q₁) with <>>-cancel-both' az ((([] :< Type) :< Type) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem equalsByteString {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem equalsByteString {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base = _ ,, _ ,, refl
bappTypeLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x₂) x₁) x)
  with <>>-cancel-both' az (((([] :< Term) :< Term) :< Term) :< Type) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₁₂) x₁) x) with <>>-cancel-both' az (((([] :< Type) :< Term) :< Term) :< Type) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₂) q₁₁) x) with <>>-cancel-both' az (((([] :< Term) :< Type) :< Term) :< Type) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₂) q₁) x)  with <>>-cancel-both' az (((([] :< Type) :< Type) :< Term) :< Type) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app⋆ .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x₂) x₁) q₁)  with <>>-cancel-both' az (((([] :< Term) :< Term) :< Type) :< Type) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app⋆ .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₂) x₁) q₁)  with <>>-cancel-both' az (((([] :< Type) :< Term) :< Type) :< Type) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app⋆ .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₂) q₂) q₁)  with <>>-cancel-both' az (((([] :< Term) :< Type) :< Type) :< Type) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem ifThenElse {as = as} .(bubble (bubble (bubble p))) (app⋆ .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₃) q₂) q₁) with <>>-cancel-both' az (((([] :< Type) :< Type) :< Type) :< Type) (((([] :< Type) :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem appendString {as = as} .(bubble p) (app {az = az} p q x)
  with <>>-cancel-both' az (([] :< Term) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, () 
bappTypeLem appendString {as = as} .(bubble p) (app⋆ {az = az} p q q₁)
  with <>>-cancel-both' az (([] :< Type) :< Type) (([] :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem trace (start _) base = _ ,, _ ,, refl
bappTypeLem trace {as = as} (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ([] <>< arity trace) _ p refl
... | refl ,, refl ,, ()
bappTypeLem equalsString (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem encodeUtf8 {az = az} p _
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem decodeUtf8 {az = az} p _
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem fstPair (start _) base = _ ,, _ ,, refl
bappTypeLem fstPair (bubble (start _)) (app⋆ _ base refl) =
  _ ,, _ ,, refl
bappTypeLem fstPair (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ((([] :< Type) :< Type) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem sndPair (start _) base = _ ,, _ ,, refl
bappTypeLem sndPair (bubble (start _)) (app⋆ _ base refl) =
  _ ,, _ ,, refl
bappTypeLem sndPair (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ((([] :< Type) :< Type) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem bData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem unConstrData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem unMapData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem unListData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem unIData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem unBData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem equalsData (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem serialiseData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem chooseData (start _) base = _ ,, _ ,, refl
bappTypeLem chooseData (bubble (bubble (bubble (bubble (bubble (bubble {as = az} p)))))) _
  with <>>-cancel-both' az _ ([] <>< arity chooseData) _ p refl
... | _ ,, _ ,, ()
bappTypeLem chooseUnit (start _) base = _ ,, _ ,, refl
bappTypeLem chooseUnit (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ([] <>< arity chooseUnit) _ p refl
... | _ ,, _ ,, ()
bappTypeLem mkPairData (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem mkNilData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem mkNilPairData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem mkCons (start _) base = _ ,, _ ,, refl
bappTypeLem mkCons (bubble (bubble {as = az} p)) _
  with <>>-cancel-both' az _ ([] <>< arity chooseUnit) _ p refl
... | _ ,, _ ,, ()
bappTypeLem nullList (start _) base = _ ,, _ ,, refl
bappTypeLem nullList (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Type) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem headList (start _) base = _ ,, _ ,, refl
bappTypeLem headList (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Type) :< Term) _ p refl
... | refl ,, refl ,, ()  
bappTypeLem tailList (start _) base = _ ,, _ ,, refl
bappTypeLem tailList (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Type) :< Term) _ p refl
... | refl ,, refl ,, ()  
bappTypeLem chooseList (start _) base = _ ,, _ ,, refl
bappTypeLem chooseList (bubble (start _)) (app⋆ _ base refl) =
  _ ,, _ ,, refl
bappTypeLem chooseList (bubble (bubble (bubble (bubble {as = az} p)))) _
  with <>>-cancel-both' az _ ([] <>< arity chooseList) _ p refl
... | _ ,, _ ,, ()
bappTypeLem constrData (bubble {as = az} p) _
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem mapData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem listData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem iData {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem consByteString (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem sliceByteString (bubble (bubble {as = az} p)) q
  with <>>-cancel-both' az _ ((([] :< Term) :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem lengthOfByteString {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem indexByteString (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
bappTypeLem blake2b-256 {az = az} p q
  with <>>-cancel-both' az _ ([] :< Term) _ p refl
... | refl ,, refl ,, ()
-}

V-I : ∀ b {A : ∅ ⊢Nf⋆ *}{a as as'}
       → (p : as <>> a ∷ as' ∈ arity b)
       → BApp b p A
=======
```
V-I : ∀ (b : Builtin) {A : ∅ ⊢Nf⋆ *}
       → ∀{tn tm} {pt : tn ∔ tm ≣ fv♯ (signature b)}
       → ∀{an am} {pa : an ∔ suc am ≣ args♯ (signature b)}
       → {σA : SigTy pt pa A}
       → BApp b A σA
>>>>>>> master
       → Value A
V-I b {tm = zero} {σA = A B⇒ σA} bt = V-I⇒ b bt
V-I b {tm = suc tm} {σA = sucΠ σA} bt = V-IΠ b bt

data Error : ∅ ⊢Nf⋆ * → Set where
  -- an actual error term
  E-error : (A : ∅ ⊢Nf⋆ *) → Error A

data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·     : ∀{Γ}{A B : ∅ ⊢Nf⋆ *} → Γ ⊢ A → Env Γ → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *} → Value (A ⇒ B) → Frame B A

  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K)
    → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (μ A B)
            (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  unwrap- : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
            (μ A B)

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

step : ∀{T} → State T → State T
step (s ; ρ ▻ ` x) = s ◅ lookup x ρ
step (s ; ρ ▻ ƛ L) = s ◅ V-ƛ L ρ
step (s ; ρ ▻ (L · M)) = (s , -· M ρ) ; ρ ▻ L
step (s ; ρ ▻ Λ L) = s ◅ V-Λ L ρ
step (s ; ρ ▻ (L ·⋆ A / refl)) = (s , -·⋆ A) ; ρ ▻ L
step (s ; ρ ▻ wrap A B L) = (s , wrap-) ; ρ ▻ L
step (s ; ρ ▻ unwrap L refl) = (s , unwrap-) ; ρ ▻ L
step (s ; ρ ▻ con c) = s ◅ V-con c
step (s ; ρ ▻ (builtin b / refl)) = s ◅ ival b
step (s ; ρ ▻ error A) = ◆ A
step (ε ◅ V) = □ V
step ((s , -· M ρ') ◅ V) = (s , V ·-) ; ρ' ▻ M
step ((s , (V-ƛ M ρ ·-)) ◅ V) = s ; ρ ∷ V ▻ M
step ((s , (V-I⇒ b {am = 0} bapp ·-)) ◅ V) = s ; [] ▻ (BUILTIN' b (app bapp V))
step ((s , (V-I⇒ b {am = suc _} bapp ·-)) ◅ V) = s ◅ V-I b (app bapp V)
step ((s , -·⋆ A) ◅ V-Λ M ρ) = s ; ρ ▻ (M [ A ]⋆)
step ((s , -·⋆ A) ◅ V-IΠ b bapp) = s ◅ V-I b (app⋆ bapp refl refl)
step ((s , wrap-) ◅ V) = s ◅ V-wrap V
step ((s , unwrap-) ◅ V-wrap V) = s ◅ V
step (□ V) = □ V
step (◆ A) = ◆ A


stepper : ℕ → ∀{T} → State T → Either RuntimeError (State T)
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ; ρ ▻ M) = stepper n (s ; ρ ▻ M)
stepper (suc n) st | (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)
-- -}
 