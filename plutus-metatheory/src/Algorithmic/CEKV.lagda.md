# CEK machine that discharges builtin args

```
{-# OPTIONS --rewriting #-}

module Algorithmic.CEKV where

open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Function hiding (_∋_)
open import Data.Product using (proj₁;proj₂)
open import Data.List using ([];_∷_)
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]];subst to substEq)
open import Data.Unit using (⊤;tt)
open import Data.Product using (_×_;Σ) renaming (_,_ to _,,_)
open import Data.Sum
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Data.Bool using (true;false)
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Debug.Trace as Debug
open import Type
open import Type.BetaNormal
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Builtin
open import Utils hiding (TermCon)
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *)
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Data.Empty

data Env : Ctx ∅ → Set

data BApp (b : Builtin) : ∀{az}{as}
  → az <>> as ∈ arity b
  → (A : ∅ ⊢Nf⋆ *) → Set

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

  V-I⇒ : ∀ b {A B as as'}
       → (p : as <>> (Term ∷ as') ∈ arity b)
       → BApp b p (A ⇒ B)
       → Value (A ⇒ B)

  V-IΠ : ∀ b {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{as as'}
       → (p : as <>> (Type ∷ as') ∈ arity b)
       → BApp b p (Π B)
       → Value (Π B)

data BApp b where
  base : BApp b (start (arity b)) (btype b)
  app : ∀{A B}{az as}
    → (p : az <>> (Term ∷ as) ∈ arity b)
    → BApp b p (A ⇒ B)
    → Value A → BApp b (bubble p) B
  app⋆ : ∀{B C}{az as}
    → (p : az <>> (Type ∷ as) ∈ arity b)
    → BApp b p (Π B)
    → {A : ∅ ⊢Nf⋆ K}
    → (q : C ≡ B [ A ]Nf)
    → BApp b (bubble p) C

data Env where
  [] : Env ∅
  _∷_ : ∀{Γ A} → Env Γ → Value A → Env (Γ , A)

lookup : ∀{Γ A} → Γ ∋ A → Env Γ → Value A
lookup Z     (ρ ∷ v) = v
lookup (S x) (ρ ∷ v) = lookup x ρ

convValue : ∀{A A'}(p : A ≡ A') → Value A → Value A'
convValue refl v = v

data Error : ∅ ⊢Nf⋆ * → Set where
  -- an actual error term
  E-error : (A : ∅ ⊢Nf⋆ *) → Error A

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



dischargeB : ∀{b A}{az}{as}{p : az <>> as ∈ arity b} → BApp b p A → ∅ ⊢ A
dischargeB {b = b} base = builtin b / refl
dischargeB (app p bt vu) = dischargeB bt · discharge vu
dischargeB (app⋆ p bt refl) = dischargeB bt ·⋆ _ / refl

discharge (V-ƛ M ρ)  = ƛ (dischargeBody M ρ)
discharge (V-Λ M ρ)  = Λ (dischargeBody⋆ M ρ)
discharge (V-wrap V) = wrap _ _ (discharge V)
discharge (V-con c)  = con c
discharge (V-I⇒ b p bt) = dischargeB bt
discharge (V-IΠ b p bt) = dischargeB bt

BUILTIN : ∀ b {A} → BApp b (saturated (arity b)) A → Either (∅ ⊢Nf⋆ *) (Value A)
BUILTIN addInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = inj₂ (V-con (integer (i + i')))
BUILTIN subtractInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = inj₂ (V-con (integer (i - i')))
BUILTIN multiplyInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = inj₂ (V-con (integer (i ** i')))
BUILTIN divideInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (integer (div i i'))))
BUILTIN quotientInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (integer (quot i i'))))
BUILTIN remainderInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (integer (rem i i'))))
BUILTIN modInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₁ (con integer))
  (inj₂ (V-con (integer (mod i i'))))
BUILTIN lessThanInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i <? i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
BUILTIN lessThanEqualsInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i ≤? i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
BUILTIN equalsInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i ≟ i') (inj₂ (V-con (bool true))) (inj₂ (V-con (bool false)))
BUILTIN appendByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bytestring (concat b b')))
BUILTIN lessThanByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bool (B< b b')))
BUILTIN lessThanEqualsByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bool (B> b b')))
BUILTIN sha2-256 (app _ base (V-con (bytestring b))) = inj₂ (V-con
  (bytestring (SHA2-256 b)))
BUILTIN sha3-256 (app _ base (V-con (bytestring b))) =
  inj₂ (V-con (bytestring (SHA3-256 b)))
BUILTIN blake2b-256 (app _ base (V-con (bytestring b))) =
  inj₂ (V-con (bytestring (BLAKE2B-256 b)))
BUILTIN verifySignature (app _ (app _ (app _ base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) with (verifySig k d c)
... | just b = inj₂ (V-con (bool b))
... | nothing = inj₁ (con bool)
BUILTIN encodeUtf8 (app _ base (V-con (string s))) =
  inj₂ (V-con (bytestring (ENCODEUTF8 s)))
BUILTIN decodeUtf8 (app _ base (V-con (bytestring b))) with DECODEUTF8 b
... | nothing = inj₁ (con string)
... | just s  = inj₂ (V-con (string s))
BUILTIN equalsByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₂ (V-con (bool (equals b b')))
BUILTIN ifThenElse (app _ (app _ (app _ (app⋆ _ base refl) (V-con (bool false))) vt) vf) = inj₂ vf
BUILTIN ifThenElse (app _ (app _ (app _ (app⋆ _ base refl) (V-con (bool true))) vt) vf) = inj₂ vt
BUILTIN appendString (app _ (app _ base (V-con (string s))) (V-con (string s'))) = inj₂ (V-con (string (primStringAppend s s')))
BUILTIN trace (app _ (app _ (app⋆ _ base refl) (V-con (string s))) v) =
  inj₂ (TRACE s v)
BUILTIN iData (app _ base (V-con (integer i))) =
  inj₂ (V-con (Data (iDATA i)))
BUILTIN bData (app _ base (V-con (bytestring b))) =
  inj₂ (V-con (Data (bDATA b)))
BUILTIN consByteString (app _ (app _ base (V-con (integer i))) (V-con (bytestring b))) = inj₂ (V-con (bytestring (cons i b)))
BUILTIN sliceByteString (app _ (app _ (app _ base (V-con (integer st))) (V-con (integer n))) (V-con (bytestring b))) = inj₂ (V-con (bytestring (slice st n b)))
BUILTIN lengthOfByteString (app _ base (V-con (bytestring b))) =
  inj₂ (V-con (integer (length b)))
BUILTIN indexByteString (app _ (app _ base (V-con (bytestring b))) (V-con (integer i))) with Data.Integer.ℤ.pos 0 ≤? i
... | no  _ = inj₁ (con integer)
... | yes _ with i <? length b
... | no _  = inj₁ (con integer)
... | yes _ = inj₂ (V-con (integer (index b i)))
BUILTIN equalsString (app _ (app _ base (V-con (string s))) (V-con (string s'))) = inj₂ (V-con (bool (primStringEquality s s')))
BUILTIN unIData (app _ base (V-con (Data (iDATA i)))) = inj₂ (V-con (integer i))
BUILTIN unBData (app _ base (V-con (Data (bDATA b)))) =
  inj₂ (V-con (bytestring b))
BUILTIN _ {A} _ = inj₁ A
  
convBApp : (b : Builtin) → ∀{az}{as}(p p' : az <>> as ∈ arity b)
  → ∀{A}
  → BApp b p A
  → BApp b p' A
convBApp b p p' q rewrite unique<>> p p' = q

BUILTIN' : ∀ b {A}{az}(p : az <>> [] ∈ arity b)
  → BApp b p A
  → ∅ ⊢ A
BUILTIN' b {az = az} p q
  with sym (trans (cong ([] <><_) (sym (<>>2<>>' _ _ _ p))) (lemma<>2 az []))
... | refl with BUILTIN b (convBApp b p (saturated (arity b)) q)
... | inj₂ V = discharge V
... | inj₁ A = error _

open import Data.Product using (∃)

bappTermLem : ∀  b {A}{az as}(p : az <>> (Term ∷ as) ∈ arity b)
    → BApp b p A → ∃ λ A' → ∃ λ A'' → A ≡ A' ⇒ A''
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
bappTermLem verifySignature .(start (Term ∷ Term ∷ Term ∷ [])) base = _ ,, _ ,, refl
bappTermLem verifySignature .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (app .(start (Term ∷ Term ∷ Term ∷ [])) base x) = _ ,, _ ,, refl
bappTermLem verifySignature {as = as} .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x₁) x) with <>>-cancel-both az ((([] :< Term) :< Term) :< Term) as p
bappTermLem verifySignature {as = .[]} (bubble (bubble .(start (Term ∷ Term ∷ Term ∷ [])))) (app .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (app {az = _} .(start (Term ∷ Term ∷ Term ∷ [])) base x₁) x) | refl ,, refl = _ ,, _ ,, refl
bappTermLem verifySignature {as = as} .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₁₁) x) with <>>-cancel-both' az ((([] :< Type) :< Term) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifySignature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₁) q₁)  with <>>-cancel-both' az ((([] :< Term) :< Type) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTermLem verifySignature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₂) q₁) with <>>-cancel-both' az ((([] :< Type) :< Type) :< Term) ((([] :< Term) :< Term) :< Term) as p refl
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
bappTermLem mkCons (start _) base = _ ,, _ ,, refl
bappTermLem mkCons {as = as} (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) as p refl
bappTermLem mkCons (bubble (start _)) (app _ base _)
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

bappTypeLem : ∀  b {A}{az as}(p : az <>> (Type ∷ as) ∈ arity b)
    → BApp b p A → ∃ λ K → ∃ λ (B : ∅ ,⋆ K ⊢Nf⋆ *) → A ≡ Π B
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
bappTypeLem verifySignature {as = as} .(bubble (bubble p)) (app .(bubble p) (app {az = az} p q x) x')
  with <>>-cancel-both' az ((([] :< Term) :< Term) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySignature {as = as} .(bubble (bubble p)) (app .(bubble p) (app⋆ {az = az} p q q₁₁) x)
  with <>>-cancel-both' az ((([] :< Type) :< Term) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySignature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app {az = az} p q x₁) q₁) with <>>-cancel-both' az ((([] :< Term) :< Type) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
... | refl ,, refl ,, ()
bappTypeLem verifySignature {as = as} .(bubble (bubble p)) (app⋆ .(bubble p) (app⋆ {az = az} p q q₂) q₁) with <>>-cancel-both' az ((([] :< Type) :< Type) :< Type) ((([] :< Term) :< Term) :< Term) as p refl
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
bappTypeLem mkCons (bubble {as = az} p) q
  with <>>-cancel-both' az _ (([] :< Term) :< Term) _ p refl
... | refl ,, refl ,, ()
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

V-I : ∀ b {A : ∅ ⊢Nf⋆ *}{a as as'}
       → (p : as <>> a ∷ as' ∈ arity b)
       → BApp b p A
       → Value A
V-I b {a = Term} p q with bappTermLem b p q
... | _ ,, _ ,, refl = V-I⇒ b p q
V-I b {a = Type} p q  with bappTypeLem b p q
... | _ ,, _ ,, refl = V-IΠ b p q

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



ival : ∀ b → Value (btype b)
ival addInteger = V-I⇒ addInteger _ base
ival subtractInteger = V-I⇒ subtractInteger _ base
ival multiplyInteger = V-I⇒ multiplyInteger _ base
ival divideInteger = V-I⇒ divideInteger _ base
ival quotientInteger = V-I⇒ quotientInteger _ base
ival remainderInteger = V-I⇒ remainderInteger _ base
ival modInteger = V-I⇒ modInteger _ base
ival lessThanInteger = V-I⇒ lessThanInteger _ base
ival lessThanEqualsInteger = V-I⇒ lessThanEqualsInteger _ base
ival equalsInteger = V-I⇒ equalsInteger _ base
ival appendByteString = V-I⇒ appendByteString _ base
ival lessThanByteString = V-I⇒ lessThanByteString _ base
ival lessThanEqualsByteString = V-I⇒ lessThanEqualsByteString _ base
ival sha2-256 = V-I⇒ sha2-256 _ base
ival sha3-256 = V-I⇒ sha3-256 _ base
ival verifySignature = V-I⇒ verifySignature _ base
ival equalsByteString = V-I⇒ equalsByteString _ base
ival ifThenElse = V-IΠ ifThenElse _ base
ival appendString = V-I⇒ appendString _ base
ival trace = V-IΠ trace _ base
ival equalsString = V-I⇒ equalsString (start _) base
ival encodeUtf8 = V-I⇒ encodeUtf8 (start _) base
ival decodeUtf8 = V-I⇒ decodeUtf8 (start _) base
ival fstPair = V-IΠ fstPair (start _) base
ival sndPair = V-IΠ sndPair (start _) base
ival nullList = V-IΠ nullList (start _) base
ival headList = V-IΠ headList (start _) base
ival tailList = V-IΠ tailList (start _) base
ival chooseList = V-IΠ chooseList (start _) base
ival constrData = V-I⇒ constrData (start _) base
ival mapData = V-I⇒ mapData (start _) base
ival listData = V-I⇒ listData (start _) base
ival iData = V-I⇒ iData (start _) base
ival bData = V-I⇒ bData (start _) base
ival unConstrData = V-I⇒ unConstrData (start _) base
ival unMapData = V-I⇒ unMapData (start _) base
ival unListData = V-I⇒ unListData (start _) base
ival unIData = V-I⇒ unIData (start _) base
ival unBData = V-I⇒ unBData (start _) base
ival equalsData = V-I⇒ equalsData (start _) base
ival chooseData = V-IΠ chooseData (start _) base
ival chooseUnit = V-IΠ chooseUnit (start _) base
ival mkPairData = V-I⇒ mkPairData (start _) base
ival mkNilData = V-I⇒ mkNilData (start _) base
ival mkNilPairData = V-I⇒ mkNilPairData (start _) base
ival mkCons = V-I⇒ mkCons (start _) base
ival consByteString = V-I⇒ consByteString (start _) base
ival sliceByteString = V-I⇒ sliceByteString (start _) base
ival lengthOfByteString = V-I⇒ lengthOfByteString (start _) base
ival indexByteString = V-I⇒ indexByteString (start _) base
ival blake2b-256 = V-I⇒ blake2b-256 (start _) base

step : ∀{T} → State T → State T
step (s ; ρ ▻ ` x)                    = s ◅ lookup x ρ
step (s ; ρ ▻ ƛ L)                    = s ◅ V-ƛ L ρ
step (s ; ρ ▻ (L · M))                = (s , -· M ρ) ; ρ ▻ L
step (s ; ρ ▻ Λ L)                    = s ◅ V-Λ L ρ
step (s ; ρ ▻ (L ·⋆ A / refl))        = (s , -·⋆ A) ; ρ ▻ L
step (s ; ρ ▻ wrap A B L)             = (s , wrap-) ; ρ ▻ L
step (s ; ρ ▻ unwrap L refl)          = (s , unwrap-) ; ρ ▻ L
step (s ; ρ ▻ con c)                  = s ◅ V-con c
step (s ; ρ ▻ (builtin b / refl))     = s ◅ ival b
step (s ; ρ ▻ error A)                = ◆ A
step (ε ◅ V)                          = □ V
step ((s , -· M ρ') ◅ V)              = (s , V ·-) ; ρ' ▻ M
step ((s , (V-ƛ M ρ ·-)) ◅ V)         = s ; ρ ∷ V ▻ M
step ((s , -·⋆ A) ◅ V-Λ M ρ)          = s ; ρ ▻ (M [ A ]⋆)
step ((s , wrap- {A = A}{B = B}) ◅ V) = s ◅ V-wrap V
step ((s , unwrap-) ◅ V-wrap V)       = s ◅ V
step ((s , (V-I⇒ b {as' = []} p vs ·-)) ◅ V) =
  s ; [] ▻ (BUILTIN' b (bubble p) (app p vs V))
step ((s , (V-I⇒ b {as' = x₂ ∷ as'} p vs ·-)) ◅ V) =
  s ◅ V-I b (bubble p) (app p vs V)
step ((s , -·⋆ A) ◅ V-IΠ b {as' = []} p vs) =
  s ; [] ▻ BUILTIN' b (bubble p) (app⋆ p vs refl) 
step ((s , -·⋆ A) ◅ V-IΠ b {as' = x₂ ∷ as'} p vs) =
  s ◅ V-I b (bubble p) (app⋆ p vs refl)
step (□ V)                            = □ V
step (◆ A)                            = ◆ A

open import Data.Nat

stepper : ℕ → ∀{T} → State T → Either RuntimeError (State T)
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ; ρ ▻ M) = stepper n (s ; ρ ▻ M)
stepper (suc n) st | (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)

-- convert CK things to CEK things

import Algorithmic.ReductionEC as Red

ck2cekVal : ∀{A}{L : ∅ ⊢ A} → Red.Value L → Value A
ck2cekBApp : ∀{b az as}{p : az <>> as ∈ arity b}{A}{L : ∅ ⊢ A}
  → Red.BApp b p L → BApp b p A

ck2cekBApp (Red.base refl) = base
ck2cekBApp (Red.step p x x₁) = app p (ck2cekBApp x) (ck2cekVal x₁)
ck2cekBApp (Red.step⋆ p x refl) = app⋆ p (ck2cekBApp x) refl

ck2cekVal (Red.V-ƛ M) = V-ƛ M []
ck2cekVal (Red.V-Λ M) = V-Λ M []
ck2cekVal (Red.V-wrap V) = V-wrap (ck2cekVal V)
ck2cekVal (Red.V-con cn) = V-con cn
ck2cekVal (Red.V-I⇒ b p x) = V-I⇒ b p (ck2cekBApp x)
ck2cekVal (Red.V-IΠ b p x) = V-IΠ b p (ck2cekBApp x)

ck2cekFrame : ∀{A B} → Red.Frame A B → Frame A B
ck2cekFrame (Red.-· M) = -· M []
ck2cekFrame (VM Red.·-) = ck2cekVal VM ·-
ck2cekFrame (Red.-·⋆ A) = -·⋆ A
ck2cekFrame Red.wrap- = wrap-
ck2cekFrame Red.unwrap- = unwrap-

import Algorithmic.CK as CK

ck2cekStack : ∀{A B} → CK.Stack A B → Stack A B
ck2cekStack CK.ε = ε
ck2cekStack (s CK., f) = ck2cekStack s , ck2cekFrame f

ck2cekState : ∀{A} → CK.State A → State A
ck2cekState (s CK.▻ L) = ck2cekStack s ; [] ▻ L
ck2cekState (s CK.◅ V) = ck2cekStack s ◅ ck2cekVal V
ck2cekState (CK.□ V) = □ (ck2cekVal V)
ck2cekState (CK.◆ A) = ◆ A


-- convert CEK things to CK things

cek2ckVal : ∀{A} → (V : Value A) → Red.Value (discharge V)

cek2ckBApp : ∀{b az as}{p : az <>> as ∈ arity b}{A}
  → (vs : BApp b p A) → Red.BApp b p (dischargeB vs)
cek2ckBApp base = Red.base refl
cek2ckBApp (app p vs v) = Red.step p (cek2ckBApp vs) (cek2ckVal v)
cek2ckBApp (app⋆ p vs refl) = Red.step⋆ p (cek2ckBApp vs) refl

cek2ckVal (V-ƛ M ρ) = Red.V-ƛ _
cek2ckVal (V-Λ M ρ) = Red.V-Λ _
cek2ckVal (V-wrap V) = Red.V-wrap (cek2ckVal V)
cek2ckVal (V-con cn) = Red.V-con cn
cek2ckVal (V-I⇒ b p x) = Red.V-I⇒ b p (cek2ckBApp x)
cek2ckVal (V-IΠ b p x) = Red.V-IΠ b p (cek2ckBApp x)

cek2ckClos : ∀{A Γ} → Γ ⊢ A → Env Γ → ∅ ⊢ A
-- cek2ckClos L ρ = conv⊢ refl (subNf-id _) (sub (ne ∘ `) (env2sub ρ) L)
cek2ckClos (` x) ρ = discharge (lookup x ρ)
cek2ckClos (ƛ L) ρ = ƛ (dischargeBody L ρ)
cek2ckClos (L · M) ρ = cek2ckClos L ρ · cek2ckClos M ρ
cek2ckClos (Λ L) ρ = Λ (dischargeBody⋆ L ρ)
cek2ckClos (L ·⋆ A / refl) ρ = cek2ckClos L ρ ·⋆ A / refl
cek2ckClos (wrap A B L) ρ = wrap A B (cek2ckClos L ρ)
cek2ckClos (unwrap L refl) ρ = unwrap (cek2ckClos L ρ) refl
cek2ckClos (con c) ρ = con c
cek2ckClos (builtin b / refl) ρ = builtin b / refl
cek2ckClos (error _) ρ = error _

cek2ckFrame : ∀{A B} → Frame A B → Red.Frame A B
cek2ckFrame (-· N ρ) = Red.-· cek2ckClos N ρ
cek2ckFrame (V ·-) = cek2ckVal V Red.·-
cek2ckFrame (-·⋆ A) = Red.-·⋆ A
cek2ckFrame wrap- = Red.wrap-
cek2ckFrame unwrap- = Red.unwrap-

cek2ckStack : ∀{A B} → Stack A B → CK.Stack A B
cek2ckStack ε = CK.ε
cek2ckStack (s , f) = cek2ckStack s CK., cek2ckFrame f
 
cek2ckState : ∀{A} → State A → CK.State A
cek2ckState (s ; ρ ▻ L) = cek2ckStack s CK.▻ cek2ckClos L ρ
cek2ckState (s ◅ V) = cek2ckStack s CK.◅ cek2ckVal V
cek2ckState (□ V) = CK.□ (cek2ckVal V)
cek2ckState (◆ A) = CK.◆ A

data _-→s_ {A : ∅ ⊢Nf⋆ *} : State A → State A → Set where
  base  : {s : State A} → s -→s s
  step* : {s s' s'' : State A}
        → step s ≡ s'
        → s' -→s s''
        → s -→s s''

step** : ∀{A}{s : State A}{s' : State A}{s'' : State A}
        → s -→s s'
        → s' -→s s''
        → s -→s s''
step** base q = q
step** (step* x p) q = step* x (step** p q)

-- some syntactic assumptions

postulate ival-lem : ∀ b {A}{s : CK.Stack A _} → (s CK.◅ Red.ival b) ≡ (s CK.◅ cek2ckVal (ival b))

postulate dischargeBody-lem' : ∀{B}{Γ}{C}(M : Γ , C ⊢ B) ρ V → (dischargeBody M ρ [ CK.discharge (cek2ckVal V) ]) ≡ cek2ckClos M (ρ ∷ V)

{- proof sketch for dischargeBody-lem'

-- type level stuff omitted for simplicity below

dischargeBody M ρ [ discharge (cek2ckVal V) ]
= { def dischargeBody }
sub (exts (env2sub ρ)) M [ discharge (cek2ckVal V) ] 
= { def of [_] }
sub (sub-cons ` (discharge (cek2ckVal V)))
    (sub (exts (env2sub ρ)) (discharge (cek2ckVal V)))
    M
= { sub-comp (lemma required) }
sub (sub (sub-cons ` (discharge (cek2ckVal V))) ∘ (exts (env2sub ρ)))
    M
= { ? }
sub (sub-cons (env2sub ρ) (discharge (cek2ckVal V))) M
= { ? }
sub (env2sub (ρ ∷ V)) M
= { lemma required }
cek2ckClos M (ρ ∷ V)

-}

dischargeBody-lem : ∀{A B}{Γ}{C}{s : CK.Stack A B}(M : Γ , C ⊢ _) ρ V → (s CK.▻ (dischargeBody M ρ [ CK.discharge (cek2ckVal V) ])) ≡ (s CK.▻ cek2ckClos M (ρ ∷ V))
dischargeBody-lem M ρ V = cong (_ CK.▻_) (dischargeBody-lem' M ρ V)

postulate discharge-lem : ∀{A}(V : Value A) → Red.deval (cek2ckVal V) ≡ discharge V

postulate dischargeBody⋆-lem' : ∀{Γ K B A}(M : Γ ,⋆ K ⊢ B) ρ → dischargeBody⋆ M ρ [ A ]⋆ ≡ (cek2ckClos (M [ A ]⋆) ρ)

dischargeBody⋆-lem : ∀{Γ K B A C}{s : CK.Stack C _}(M : Γ ,⋆ K ⊢ B) ρ → (s CK.▻ (dischargeBody⋆ M ρ [ A ]⋆)) ≡ (s CK.▻ cek2ckClos (M [ A ]⋆) ρ)
dischargeBody⋆-lem M ρ = cong (_ CK.▻_) (dischargeBody⋆-lem' M ρ)

postulate dischargeB-lem : ∀ {K A}{B : ∅ ,⋆ K ⊢Nf⋆ *}{C b}{as a as'}{p : as <>> Type ∷ a ∷ as' ∈ arity b}{x : BApp b p (Π B)} (s : CK.Stack C (B [ A ]Nf)) → s CK.◅ Red.V-I b (bubble p) (Red.step⋆ p (cek2ckBApp x) refl) ≡ (s CK.◅ cek2ckVal (V-I b (bubble p) (app⋆ p x refl)))

postulate dischargeB'-lem : ∀ {A}{C b}{as a as'}{p : as <>> a ∷ as' ∈ arity b}{x : BApp b p A} (s : CK.Stack C _) → s CK.◅ Red.V-I b p (cek2ckBApp x) ≡ (s CK.◅ cek2ckVal (V-I b p x))

postulate dischargeB-lem' : ∀ {A}{b}{as a as'}{p : as <>> a ∷ as' ∈ arity b}{x : BApp b p A} → dischargeB x ≡ discharge (V-I b p x)

postulate dischargeB-lem'' : ∀ {A}{b}{as a as'}{p : as <>> a ∷ as' ∈ arity b}{x : BApp b p A} → substEq Red.Value dischargeB-lem' (Red.V-I b p (cek2ckBApp x)) ≡ cek2ckVal (V-I b p x)

-- assuming that buitins work the same way for CEK and red/CK

postulate BUILTIN-lem : ∀ b {A}{az}(p : az <>> [] ∈ arity b)(q : BApp b p A) → Red.BUILTIN' b p (cek2ckBApp q) ≡ cek2ckClos (BUILTIN' b p q) []

import Algorithmic.CC as CC
thm65a : ∀{A}(s s' : State A) → s -→s s' → cek2ckState s CK.-→s cek2ckState s'
thm65a s s  base        = CK.base
thm65a (s ; ρ ▻ ` x) s' (step* refl q) = CK.step** (CK.lemV (discharge (lookup x ρ)) (cek2ckVal (lookup x ρ)) (cek2ckStack s)) (thm65a _ s' q)
thm65a (s ; ρ ▻ ƛ L) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ (L · M)) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ Λ L) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ (L ·⋆ A / refl)) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ wrap A B L) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ unwrap L refl) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ con c) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ (builtin b / refl)) s' (step* refl q) = CK.step* (ival-lem b) (thm65a _ s' q)
thm65a (s ; ρ ▻ error _) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (ε ◅ V) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a ((s , -· L ρ) ◅ V) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a ((s , (V-ƛ M ρ ·-)) ◅ V) s' (step* refl q)    = CK.step*
  (dischargeBody-lem M ρ V)
  (thm65a _ s' q)
thm65a ((s , (V-I⇒ b {as' = []} p x ·-)) ◅ V) s' (step* refl q) = CK.step*
  (cong (cek2ckStack s CK.▻_) (BUILTIN-lem b (bubble p) (app p x V)))
  (thm65a _ s' q)
thm65a ((s , (V-I⇒ b {as' = x₁ ∷ as'} p x ·-)) ◅ V) s' (step* refl q) = CK.step* (dischargeB'-lem (cek2ckStack s)) (thm65a _ s' q)
thm65a ((s , -·⋆ A) ◅ V-Λ M ρ) s' (step* refl q) = CK.step* (dischargeBody⋆-lem M ρ) (thm65a _ s' q)
thm65a ((s , -·⋆ A) ◅ V-IΠ b {as' = []} p x) s' (step* refl q) = CK.step*
  (cong (cek2ckStack s CK.▻_) (BUILTIN-lem b (bubble p) (app⋆ p x refl)))
  (thm65a _ s' q)
thm65a ((s , -·⋆ A) ◅ V-IΠ b {as' = x₁ ∷ as'} p x) s' (step* refl q) = CK.step* (dischargeB-lem (cek2ckStack s)) (thm65a _ s' q)
thm65a ((s , wrap-) ◅ V) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a ((s , unwrap-) ◅ V-wrap V) s' (step* refl q) = CK.step* (cong (cek2ckStack s CK.▻_) (discharge-lem V)) (CK.step** (CK.lemV _ (cek2ckVal V) (cek2ckStack s)) (thm65a _ s' q))
thm65a (□ V) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (◆ A) s' (step* refl q) = CK.step* refl (thm65a _ s' q)


postulate clos-lem : ∀{A}(M : ∅ ⊢ A) → M ≡ cek2ckClos M []

lem□ : ∀{A}(W V : Value A) → □ W -→s □ V → W ≡ V
lem□ W .W base = refl
lem□ W V (step* refl p) = lem□ W V p

-- the below lemmas/assumptions consider the case that where M is a
--  variable in M' == clos M ρ, but I am not sure if these cases ever
--  occur when the CEK machine is in value mode. This may be overkill
--  for our machine, in the textbook there is not such a clear
--  distinction between term and value mode and this analysis is needed.

-- note N cannot be a variable because if it was then the result of
-- the lookup in ρ would be a value that is then discharged which
-- couldn't be an application as applications are not values
postulate cek2ckClos-·lem : ∀{A B}{L : ∅ ⊢ A ⇒ B}{M : ∅ ⊢ A}{Γ}{ρ : Env Γ}{N : Γ ⊢ B} → L · M ≡ cek2ckClos N ρ → ∃ λ L' → ∃ λ M' → N ≡ L' · M' × L ≡ cek2ckClos L' ρ × M ≡ cek2ckClos M' ρ

-- as ƛ is a value, it can be the result of a variable lookup
postulate cek2ckClos-ƛlem : ∀{A B}{L : ∅ , A ⊢ B}{Γ}{ρ : Env Γ}{N : Γ ⊢ A ⇒ B} → (p : ƛ L ≡ cek2ckClos N ρ) → (∃ λ L' → N ≡ ƛ L' × L ≡ dischargeBody L' ρ) ⊎ ∃ λ x → N ≡ ` x × ∃ λ (p : ƛ L ≡ discharge (lookup x ρ)) → substEq Red.Value p (Red.V-ƛ L) ≡ cek2ckVal (lookup x ρ)

postulate cek2ckClos-·⋆lem : ∀{K B}{L : ∅ ⊢ Π B}{A : ∅ ⊢Nf⋆ K}{Γ}{ρ : Env Γ}{N : Γ ⊢ B [ A ]Nf} → L ·⋆ A / refl ≡ cek2ckClos N ρ → ∃ λ L' → N ≡ L' ·⋆ A / refl × L ≡ cek2ckClos L' ρ

postulate cek2ckClos-Λlem : ∀{K B}{L : ∅ ,⋆ K ⊢ B}{Γ}{ρ : Env Γ}{N : Γ ⊢ Π B} → (p : Λ L ≡ cek2ckClos N ρ) → (∃ λ L' → N ≡ Λ L' × L ≡ dischargeBody⋆ L' ρ) ⊎ ∃ λ x → N ≡ ` x × ∃ λ (p : Λ L ≡ discharge (lookup x ρ)) → substEq Red.Value p (Red.V-Λ L) ≡ cek2ckVal (lookup x ρ)

postulate cek2ckClos-wraplem : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}{L}{Γ}{ρ : Env Γ}{N : Γ ⊢ μ A B} → (p : wrap A B L ≡ cek2ckClos N ρ) → (∃ λ L' → N ≡ wrap A B L' × L ≡ cek2ckClos L' ρ) ⊎ ∃ λ x → N ≡ ` x × ∃ λ V → ∃ λ (q : V-wrap V ≡ lookup x ρ) → discharge V ≡ L × substEq Red.Value (cong discharge q) (Red.V-wrap (cek2ckVal V)) ≡ cek2ckVal (lookup x ρ)

postulate cek2ckClos-unwraplem : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}{L : ∅ ⊢ μ A B}{Γ}{ρ : Env Γ}{N : Γ ⊢ _} → (p : unwrap L refl ≡ cek2ckClos N ρ) → (∃ λ L' → N ≡ unwrap L' refl × L ≡ cek2ckClos L' ρ)

postulate cek2ckClos-conlem : ∀{tc : TyCon ∅}(c : TermCon (con tc)){Γ}{M' : Γ ⊢ con tc}{ρ : Env Γ} → con c ≡ cek2ckClos M' ρ → M' ≡ con c ⊎ ∃ λ x → M' ≡ ` x × V-con c ≡ lookup x ρ

postulate cek2ckClos-ibuiltinlem : ∀{b}{Γ}{M' : Γ ⊢ btype b}{ρ : Env Γ} → builtin b / refl ≡ cek2ckClos M' ρ → (M' ≡ builtin b / refl × ∃ λ p → substEq Red.Value p (Red.ival b) ≡ cek2ckVal (ival b)) ⊎ ∃ λ x → M' ≡ ` x × ∃ λ (p : builtin b / refl ≡ discharge (lookup x ρ)) → substEq Red.Value p (Red.ival b) ≡ cek2ckVal (lookup x ρ)

cek2ckStack-εlem : ∀{A}(s : Stack A A) → CK.ε ≡ cek2ckStack s → s ≡ ε
cek2ckStack-εlem ε       p = refl
cek2ckStack-εlem (s , f) ()

cek2ckStack-,lem : ∀{A B C}(s : CK.Stack A B)(s' : Stack A C)(f : Red.Frame B C)
  → s CK., f ≡ cek2ckStack s' →
  ∃ λ (s'' : Stack A B) → ∃ λ (f' : Frame B C) → s' ≡ (s'' Stack., f')
  × s ≡ cek2ckStack s'' × f ≡ cek2ckFrame f'
cek2ckStack-,lem _ (s' , f) _ refl =
  _ ,, _ ,, refl ,, refl ,, refl

cek2ckFrame-·-lem : ∀{A B} f {M : ∅ ⊢ A ⇒ B}(W : Red.Value M)
  → W Red.·- ≡ cek2ckFrame f →
  ∃ λ W' → f ≡ (W' ·-) × ∃ λ (p : M ≡ discharge W') → substEq Red.Value p W ≡ cek2ckVal W'
cek2ckFrame-·-lem (x ·-) .(cek2ckVal x) refl = _ ,, refl ,, refl ,, refl

postulate cek2ckFrame--·lem : ∀{A B}(f : Frame B (A ⇒ B)){M : ∅ ⊢ A} → (Red.-· M) ≡ cek2ckFrame f → ∃ λ Γ → ∃ λ (M' : Γ ⊢ A) → ∃ λ (ρ : Env Γ) → f ≡ (-· M' ρ) × M ≡ cek2ckClos M' ρ

postulate cek2ckFrame--·⋆lem : ∀{K A}{B : ∅ ,⋆ K ⊢Nf⋆ *}(f : Frame (B [ A ]Nf) (Π B)) → Red.-·⋆ A ≡ cek2ckFrame f → f ≡ -·⋆ A
   
postulate cek2ckFrame-unwrap-lem : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}(f : Frame _ (μ A B)) → Red.unwrap- {A = A}{B = B} ≡ cek2ckFrame f → f ≡ unwrap-

postulate cek2ckFrame-wrap-lem : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}(f : Frame (μ A B) _) → Red.wrap- {A = A}{B = B} ≡ cek2ckFrame f → f ≡ wrap-

thm65bV : ∀{A B}{L : ∅ ⊢ A}{M}{s : CK.Stack A B}{V : Red.Value L}
  {W : Red.Value M}{W'}{s'}
  → (p : M ≡ discharge W')
  → substEq Red.Value p W ≡ cek2ckVal W'
  → s ≡ cek2ckStack s'
  → (s CK.◅ W) CK.-→s CK.□ V
  → ∃ λ V' → ((s' ◅ W') -→s □ V') × ∃ λ p → cek2ckVal V' ≡ substEq Red.Value p V

substLem : {A : Set}(P : A → Set){a a' : A}(p q : a ≡ a')(x : P a) →
  substEq P p x ≡ substEq P q x
substLem P refl refl x = refl

postulate fast-forward : ∀{A B}(s : CK.Stack A B)(s' : CK.State A)(M : ∅ ⊢ B)
                 → (V : Red.Value M)
                 → (s CK.▻ M) CK.-→s s' → (s CK.◅ V) CK.-→s s'

{-# TERMINATING #-}
-- this is needed as in the wrap case we fast-forward the CK machine state
-- and recurse on something which is quite a bit shorter

thm65b : ∀{A B}{L : ∅ ⊢ A}{Γ M}{s : CK.Stack A B}{V : Red.Value L}
  {M'}{ρ : Env Γ}{s'}
  → M ≡ cek2ckClos M' ρ
  → s ≡ cek2ckStack s'
  → (s CK.▻ M) CK.-→s CK.□ V
  → ∃ λ V' → ((s' ; ρ ▻ M') -→s □ V') × ∃ λ p → cek2ckVal V' ≡ substEq Red.Value p V
thm65b {M = ƛ M} {s = s} {M' = N} {ρ} {s'} p q (CK.step* refl r)
  with cek2ckClos-ƛlem {ρ = ρ}{N = N} p
thm65b {M = ƛ M} {s = s} {M' = N} {ρ} {s'} refl q (CK.step* refl r) | inj₁ (L' ,, refl ,, z) with thm65bV refl refl q r
... | V ,, r' ,, y ,, y' = V ,, step* refl r' ,, y ,, y'
thm65b {Γ = _} {ƛ M} {s = s} {M' = .(` x)} {ρ} {s'} p q (CK.step* refl r) | inj₂ (x ,, refl ,, y' ,, y'') with thm65bV p (trans (substLem Red.Value p y' _) y'') q r
... | V ,, r' ,, y ,, y' = V ,, step* refl r' ,, y ,, y'
thm65b {M = L · M} {s = s} {M' = N}{ρ}{s'} p q (CK.step* refl r)
  with cek2ckClos-·lem {ρ = ρ}{N = N} p
... | L' ,, M' ,, refl ,, Lp ,, refl
  with thm65b Lp (cong (CK._, (Red.-· M)) q) r
... | x ,, y ,, z  ,, z' = x ,, step* refl y ,, z ,, z'
thm65b {M = Λ M} {s = s}{M' = N}{ρ}{s'} p q (CK.step* refl r)
  with cek2ckClos-Λlem {ρ = ρ}{N = N} p
thm65b {M' = .(Λ L')} {ρ} {s'} refl q (CK.step* refl r) | inj₁ (L' ,, refl ,, z) with thm65bV refl refl q r
... | V ,, r' ,, y ,, y' = V ,, step* refl r' ,, y ,, y'
thm65b {M = Λ M} {s = s}{M' = N}{ρ}{s'} p q (CK.step* refl r) | inj₂ (x ,, refl ,, y' ,, y'') with thm65bV p (trans (substLem Red.Value p y' _) y'') q r
... | V ,, r' ,, y ,, y' = V ,, step* refl r' ,, y ,, y'
thm65b {M = M ·⋆ A / refl} {s = s}{M' = N}{ρ}{s' = s'} p q (CK.step* refl r)
  with cek2ckClos-·⋆lem {ρ = ρ}{N = N} p
... | L' ,, refl ,, y'
  with thm65b y' (cong (CK._, (Red.-·⋆ A)) q) r
... | x ,, y ,, z ,, z' = x ,, step* refl y ,, z ,, z'
thm65b {M = wrap A B M} {s = s}{M' = N}{ρ}{s' = s'} p q (CK.step* refl r)
  with cek2ckClos-wraplem {ρ = ρ}{N = N} p
thm65b {M = wrap A B M} {s = s}{M' = N}{ρ}{s' = s'} p refl r | inj₂ (x ,, refl ,, W ,, y1 ,, refl ,, y3) with thm65bV (cong discharge y1) y3 refl (fast-forward _ _ _ (cek2ckVal (V-wrap W)) r)
... | V ,, r' ,, z ,, z' = V ,, step* refl r' ,, z ,, z'
thm65b {Γ = _} {wrap _ _ .(cek2ckClos V ρ)} {s = s} {M' = .(wrap _ _ V)} {ρ} {s' = s'} refl refl (CK.step* refl r) | inj₁ (V ,, refl ,, y) with thm65b refl refl r
... | x ,, y ,, z ,, z' = x ,, step* refl y ,, z ,, z'

thm65b {M = unwrap M refl} {s = s}{M' = N}{ρ = ρ} {s' = s'} p q (CK.step* refl r)
  with cek2ckClos-unwraplem {ρ = ρ}{N = N} p
... | L' ,, refl ,, x2 with thm65b x2 (cong (CK._, Red.unwrap-) q) r
... | V' ,, r' ,, y1 ,, y2 = _ ,, step* refl r' ,, y1 ,, y2
thm65b {M = con c}{s = s}{M' = M'}{ρ = ρ}{s' = s'} p q (CK.step* refl r)
  with thm65bV refl refl q r
... | W ,, r' ,, x1 ,, x2
  with cek2ckClos-conlem c {M' = M'}{ρ = ρ} p
... | inj₁ refl = _ ,, step* refl r' ,, x1 ,, x2
... | inj₂ (var ,, refl ,, y2) = _ ,, step* (cong (s' ◅_) (sym y2)) r' ,, x1 ,, x2

thm65b {M = builtin b / refl} {s = s}{M' = N}{ρ = ρ}{s' = s'} p q (CK.step* refl r)
  with cek2ckClos-ibuiltinlem {M' = N}{ρ = ρ} p
thm65b {M = builtin b / refl} {s = s}{M' = N}{ρ = ρ}{s' = s'} p q (CK.step* refl r) | inj₂ (x ,, refl ,, y2 ,, y3) with thm65bV y2 y3 q r
... | V' ,, r' ,, y1 ,, y2 = V' ,, step* refl r' ,, y1 ,, y2
thm65b {M = builtin b / refl} {s = s}{M' = N}{ρ = ρ}{s' = s'} p q (CK.step* refl r) | inj₁ (refl ,, x1 ,, x2)
  with thm65bV x1 x2 q r
... | V' ,, r' ,, y1 ,, y2 = V' ,, step* refl r' ,, y1 ,, y2

thm65b {M = error _} {s = s} {s' = s'} p q (CK.step* refl r) = ⊥-elim (CK.lem◆' _ r)

thm65bV {s = CK.ε} {W = W} {s' = s'} refl refl r (CK.step* refl x)
  rewrite cek2ckStack-εlem s' r
  with CK.lem□ _ _ x
... | refl ,, refl = _ ,, step* refl base ,, refl ,, refl
thm65bV {s = s CK., (Red.-· x₁)} {W = W} {s' = s'} refl refl r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | _ ,, _ ,, refl ,, refl ,, z1
  with cek2ckFrame--·lem _ z1
... | Γ ,, M' ,, ρ ,, refl ,, z2
  with thm65b z2 refl x
... | _ ,, x' ,, refl ,, refl = _ ,, step* refl x' ,, refl ,, refl
thm65bV {s = s CK., (x₁ Red.·-)} {W = W} {s' = s'} p q r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | _ ,, _ ,, refl ,, refl ,, z1
  with cek2ckFrame-·-lem _ _ z1
thm65bV {M = _} {.(cek2ckStack fst) CK., (.(cek2ckVal (V-ƛ M x₁)) Red.·-)} {W = W} {_} {.(fst , (V-ƛ M x₁ ·-))} refl refl r (CK.step* refl x) | fst ,, .(V-ƛ M x₁ ·-) ,, refl ,, refl ,, z1 | V-ƛ M x₁ ,, refl ,, refl ,, refl
  with thm65b (dischargeBody-lem' M x₁ _) refl x
... | V'' ,, x' ,, refl ,, refl = _ ,, step* refl x' ,, refl ,, refl
thm65bV {M = _} {.(cek2ckStack fst) CK., (.(cek2ckVal (V-I⇒ b p₁ x₁)) Red.·-)} {W = W} {_} {.(fst , (V-I⇒ b p₁ x₁ ·-))} refl refl r (CK.step* refl x) | fst ,, .(V-I⇒ b p₁ x₁ ·-) ,, refl ,, refl ,, z1 | V-I⇒ b {as' = []} p₁ x₁ ,, refl ,, refl ,, refl with thm65b (BUILTIN-lem b (bubble p₁) (app p₁ x₁ _)) refl x
... | V' ,, r' ,, y1 ,, y2 = V' ,, step* refl r' ,, y1 ,, y2
thm65bV {M = _} {.(cek2ckStack fst) CK., (.(cek2ckVal (V-I⇒ b p₁ x₁)) Red.·-)} {W = W} {_} {.(fst , (V-I⇒ b p₁ x₁ ·-))} refl refl r (CK.step* refl x) | fst ,, .(V-I⇒ b p₁ x₁ ·-) ,, refl ,, refl ,, z1 | V-I⇒ b {as' = x₂ ∷ as'} p₁ x₁ ,, refl ,, refl ,, refl with thm65bV dischargeB-lem'  dischargeB-lem'' refl x
... | V' ,, r' ,, y1 ,, y2 = V' ,, step* refl r' ,, y1 ,, y2
thm65bV {s = s CK., Red.-·⋆ A} {W = .(cek2ckVal (V-Λ M x₁))} {V-Λ M x₁} {s' = s'} refl refl r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | x1 ,, x2 ,, refl ,, z0 ,, z1
  with thm65b {M' = M [ A ]⋆}{ρ = x₁} (dischargeBody⋆-lem' M x₁) z0 x
... | f ,, x' ,, refl ,, z2
  with cek2ckFrame--·⋆lem x2 z1
... | refl = _ ,, step* refl x' ,, refl ,, z2
thm65bV {s = s CK., Red.-·⋆ A} {W = .(cek2ckVal (V-IΠ b p x₁))} {V-IΠ b {as' = []} p x₁} {s' = s'} refl refl r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | x1 ,, x2 ,, refl ,, z0 ,, z1
  with cek2ckFrame--·⋆lem x2 z1
... | refl
  with thm65b (BUILTIN-lem b (bubble p) (app⋆ p x₁ refl)) z0 x
... | V' ,, r' ,, y1 ,, y2 = V' ,, step* refl r' ,, y1 ,, y2
thm65bV {s = s CK., Red.-·⋆ A} {W = .(cek2ckVal (V-IΠ b p x₁))} {V-IΠ b {as' = x₂ ∷ as'} p x₁} {s' = s'} refl refl r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | x1 ,, x2 ,, refl ,, z0 ,, z1
  with cek2ckFrame--·⋆lem x2 z1
... | refl with thm65bV (dischargeB-lem' {b = b}{x = app⋆ p x₁ refl}) dischargeB-lem'' z0 x
... | V' ,, x' ,, y1 ,, y2 = V' ,, step* refl x' ,, y1 ,, y2
thm65bV {s = s CK., Red.wrap- } {W = W} {s' = s'} refl q r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | s' ,, f' ,, refl ,, x2 ,, x3
  with cek2ckFrame-wrap-lem _ x3
... | refl with thm65bV refl (cong Red.V-wrap q) x2 x
... | _  ,, x' ,, _ ,, y1 = _ ,, step* refl x' ,, _ ,, y1
thm65bV {s = s CK., Red.unwrap- } {W = W} {s' = s'} p q r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
thm65bV {M = wrap _ _ M} {.(cek2ckStack s') CK., Red.unwrap- } {W = Red.V-wrap W} {W' = V-wrap W'} refl refl r (CK.step* refl x) | s' ,, f' ,, refl ,, refl ,, x3
  with thm65bV refl refl refl (fast-forward (cek2ckStack s') (CK.□ _) (Red.deval (cek2ckVal W')) (cek2ckVal W') x)
... | _ ,, x' ,, _ ,, y1
  with cek2ckFrame-unwrap-lem _ x3
thm65bV {L = _} {.(wrap _ _ _)} {.(cek2ckStack s') CK., Red.unwrap- } {_} {Red.V-wrap W} {V-wrap W'} {.(s' , unwrap-)} p q r (CK.step* refl x) | s' ,, .unwrap- ,, refl ,, refl ,, x1 | _ ,, x' ,, _ ,, y1 | refl = _ ,, step* refl x' ,, _ ,, y1
-- -}
