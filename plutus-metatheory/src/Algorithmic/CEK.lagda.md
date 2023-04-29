# CEK machine that discharges builtin args

```
module Algorithmic.CEK where

open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Properties using (+-identityʳ)
open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Function using (_∘_)
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
open import Utils

open import Builtin.Constant.AtomicType
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) using (TyCon;integer;bool;bytestring;string;pdata)
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

dischargeB : ∀{b : Builtin}
          → ∀{tn tm} → {pt : tn ∔ tm ≣ fv♯ (signature b)}
          → ∀{an am} → {pa : an ∔ am ≣ args♯ (signature b)}
          → ∀{C} → {Cb : SigTy pt pa C} → (bp : BApp b C Cb) 
          → ∅ ⊢ C
dischargeB {b} base = builtin b / refl
dischargeB (app bt x) = dischargeB bt · discharge x
dischargeB (app⋆ bt q _) = dischargeB bt  ·⋆ _ /  q

discharge (V-ƛ M ρ)  = ƛ (dischargeBody M ρ)
discharge (V-Λ M ρ)  = Λ (dischargeBody⋆ M ρ)
discharge (V-wrap V) = wrap _ _ (discharge V)
discharge (V-con c)  = con c
discharge (V-I⇒ b bt) = dischargeB bt
discharge (V-IΠ b bt) = dischargeB bt 
```

## Builtin Semantics

```
BUILTIN : ∀ b {A} → {Ab : saturatedSigTy (signature b) A} → BApp b A Ab → Either (∅ ⊢Nf⋆ *) (Value A)
BUILTIN addInteger (app (app base (V-con (tmInteger i))) (V-con (tmInteger i'))) = inj₂ (V-con (tmInteger (i + i')))
BUILTIN subtractInteger (app (app base (V-con (tmInteger i))) (V-con (tmInteger i'))) = inj₂ (V-con (tmInteger (i - i')))
BUILTIN multiplyInteger (app (app base (V-con (tmInteger i))) (V-con (tmInteger i'))) = inj₂ (V-con (tmInteger (i ** i')))
BUILTIN divideInteger (app (app base (V-con (tmInteger i))) (V-con (tmInteger i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (tmInteger (div i i'))))
BUILTIN quotientInteger (app (app base (V-con (tmInteger i))) (V-con (tmInteger i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (tmInteger (quot i i'))))
BUILTIN remainderInteger (app (app base (V-con (tmInteger i))) (V-con (tmInteger i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (tmInteger (rem i i'))))
BUILTIN modInteger (app (app base (V-con (tmInteger i))) (V-con (tmInteger i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (tmInteger (mod i i'))))
BUILTIN lessThanInteger (app (app base (V-con (tmInteger i))) (V-con (tmInteger i'))) = decIf (i <? i') (inj₂ (V-con (tmBool true))) (inj₂ (V-con (tmBool false)))
BUILTIN lessThanEqualsInteger (app (app base (V-con (tmInteger i))) (V-con (tmInteger i'))) = decIf (i ≤? i') (inj₂ (V-con (tmBool true))) (inj₂ (V-con (tmBool false)))
BUILTIN equalsInteger (app (app base (V-con (tmInteger i))) (V-con (tmInteger i'))) = decIf (i ≟ i') (inj₂ (V-con (tmBool true))) (inj₂ (V-con (tmBool false)))
BUILTIN appendByteString (app (app base (V-con (tmBytestring b))) (V-con (tmBytestring b'))) = inj₂ (V-con (tmBytestring (concat b b')))
BUILTIN lessThanByteString (app (app base (V-con (tmBytestring b))) (V-con (tmBytestring b'))) = inj₂ (V-con (tmBool (B< b b')))
BUILTIN lessThanEqualsByteString (app (app base (V-con (tmBytestring b))) (V-con (tmBytestring b'))) = inj₂ (V-con (tmBool (B<= b b')))
BUILTIN sha2-256 (app base (V-con (tmBytestring b))) = inj₂ (V-con
  (tmBytestring (SHA2-256 b)))
BUILTIN sha3-256 (app base (V-con (tmBytestring b))) =
  inj₂ (V-con (tmBytestring (SHA3-256 b)))
BUILTIN blake2b-256 (app base (V-con (tmBytestring b))) =
  inj₂ (V-con (tmBytestring (BLAKE2B-256 b)))
BUILTIN verifyEd25519Signature (app (app (app base (V-con (tmBytestring k))) (V-con (tmBytestring d))) (V-con (tmBytestring c))) with (verifyEd25519Sig k d c)
... | just b = inj₂ (V-con (tmBool b))
... | nothing = inj₁ (con bool)
BUILTIN verifyEcdsaSecp256k1Signature (app (app (app base (V-con (tmBytestring k))) (V-con (tmBytestring d))) (V-con (tmBytestring c))) with (verifyEcdsaSecp256k1Sig k d c)
... | just b = inj₂ (V-con (tmBool b))
... | nothing = inj₁ (con bool)
BUILTIN verifySchnorrSecp256k1Signature (app (app (app base (V-con (tmBytestring k))) (V-con (tmBytestring d))) (V-con (tmBytestring c))) with (verifySchnorrSecp256k1Sig k d c)
... | just b = inj₂ (V-con (tmBool b))
... | nothing = inj₁ (con bool)
BUILTIN encodeUtf8 (app base (V-con (tmString s))) =
  inj₂ (V-con (tmBytestring (ENCODEUTF8 s)))
BUILTIN decodeUtf8 (app base (V-con (tmBytestring b))) with DECODEUTF8 b
... | nothing = inj₁ (con string)
... | just s  = inj₂ (V-con (tmString s))
BUILTIN equalsByteString (app (app base (V-con (tmBytestring b))) (V-con (tmBytestring b'))) = inj₂ (V-con (tmBool (equals b b')))
BUILTIN ifThenElse (app (app (app (app⋆ base refl refl) (V-con (tmBool false))) vt) vf) = inj₂ vf
BUILTIN ifThenElse (app (app (app (app⋆ base refl refl) (V-con (tmBool true))) vt) vf) = inj₂ vt
BUILTIN appendString (app (app base (V-con (tmString s))) (V-con (tmString s'))) = inj₂ (V-con (tmString (primStringAppend s s')))
BUILTIN trace (app (app (app⋆ base refl refl) (V-con (tmString s))) v) =
  inj₂ (TRACE s v)
BUILTIN iData (app base (V-con (tmInteger i))) =
  inj₂ (V-con (tmData (iDATA i)))
BUILTIN bData (app base (V-con (tmBytestring b))) =
  inj₂ (V-con (tmData (bDATA b)))
BUILTIN consByteString (app (app base (V-con (tmInteger i))) (V-con (tmBytestring b))) with cons i b 
... | just b' = inj₂ (V-con (tmBytestring b'))
... | nothing = inj₁ (con bytestring)
BUILTIN sliceByteString (app (app (app base (V-con (tmInteger st))) (V-con (tmInteger n))) (V-con (tmBytestring b))) = inj₂ (V-con (tmBytestring (slice st n b)))
BUILTIN lengthOfByteString (app base (V-con (tmBytestring b))) =
  inj₂ (V-con (tmInteger (length b)))
BUILTIN indexByteString (app (app base (V-con (tmBytestring b))) (V-con (tmInteger i))) with Data.Integer.ℤ.pos 0 ≤? i
... | no  _ = inj₁ (con integer)
... | yes _ with i <? length b
... | no _  = inj₁ (con integer)
... | yes _ = inj₂ (V-con (tmInteger (index b i)))
BUILTIN equalsString (app (app base (V-con (tmString s))) (V-con (tmString s'))) = inj₂ (V-con (tmBool (primStringEquality s s')))
BUILTIN unIData (app base (V-con (tmData (iDATA i)))) = inj₂ (V-con (tmInteger i))
BUILTIN unIData (app base (V-con (tmData _))) = inj₁ (con pdata)
BUILTIN unBData (app base (V-con (tmData (bDATA b)))) = inj₂ (V-con (tmBytestring b))
BUILTIN unBData (app base (V-con (tmData _))) = inj₁ (con pdata)
BUILTIN unConstrData {A} (app base (V-con (tmData (ConstrDATA i xs)))) = inj₁ A --unimplemented  inj₂ (V-con (pair i xs))
BUILTIN unConstrData {A} (app base (V-con (tmData _))) = inj₁ (con pdata)
BUILTIN unMapData {A} (app base (V-con (tmData (MapDATA x)))) = inj₁ A --unimplemented inj₂ (V-con (listPair x))
BUILTIN unMapData {A} (app base (V-con (tmData _))) = inj₁ (con pdata)
BUILTIN unListData {A} (app base (V-con (tmData (ListDATA x)))) = inj₁ A --unimplemented inj₂ (V-con (listData x))
BUILTIN unListData {A} (app base (V-con (tmData _))) = inj₁ (con pdata)
BUILTIN serialiseData {A} (app base (V-con (tmData d))) = inj₂ (V-con (tmBytestring (serialiseDATA d)))
BUILTIN mkNilData {A} (app base (V-con tmUnit)) = inj₁ A --unimplemented inj₂ (V-con (listData []))
BUILTIN mkNilPairData {A} (app base (V-con tmUnit)) = inj₁ A --unimplemented inj₂ (V-con (listPair []))
BUILTIN chooseUnit {A} (app (app (app⋆ base refl refl) x) (V-con tmUnit)) = inj₂ x
BUILTIN equalsData {A}  (app (app base (V-con (tmData d))) (V-con (tmData d'))) = inj₂ (V-con (tmBool (eqDATA d d')))
BUILTIN mkPairData {A} (app (app base (V-con (tmData x))) (V-con (tmData y))) = inj₁ A --unimplemented 
BUILTIN constrData {A} (app (app base (V-con (tmInteger i))) (V-con xs)) = inj₁ A --unimplemented
BUILTIN mapData {A} (app base (V-con xs)) = inj₁ A --unimplemented 
BUILTIN listData {A} (app base (V-con xs)) = inj₁ A --unimplemented 
BUILTIN fstPair {A} bapp = inj₁ A --unimplemented
BUILTIN sndPair {A} bapp = inj₁ A --unimplemented
BUILTIN chooseList {A} bapp = inj₁ A --unimplemented
BUILTIN mkCons {A} (app (app (app⋆ base refl refl) x) (V-con xs)) = inj₁ A --unimplemented
BUILTIN headList {A} bapp = inj₁ A --unimplemented
BUILTIN tailList {A} bapp = inj₁ A --unimplemented
BUILTIN nullList {A} (app (app⋆ base refl refl) (V-con cn)) = inj₁ A  --unimplemented
BUILTIN chooseData {A} bapp =  inj₁ A --unimplemented

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

```
V-I : ∀ (b : Builtin) {A : ∅ ⊢Nf⋆ *}
       → ∀{tn tm} {pt : tn ∔ tm ≣ fv♯ (signature b)}
       → ∀{an am} {pa : an ∔ suc am ≣ args♯ (signature b)}
       → {σA : SigTy pt pa A}
       → BApp b A σA
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
