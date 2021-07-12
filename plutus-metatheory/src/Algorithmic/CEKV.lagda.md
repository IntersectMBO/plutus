# CEK machine that discharges builtin args

```
{-# OPTIONS --rewriting #-}

module Algorithmic.CEKV where

open import Agda.Builtin.String using (primStringFromList; primStringAppend)
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
open import Utils

open import Type
open import Type.BetaNormal
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Builtin
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Utils using (decIf;just;nothing)

open import Algorithmic.ReductionEC using (Arg;Term;Type;_<>>_∈_;start;bubble;arity;saturated;_<><_;<>>2<>>';lemma<>2;unique<>>;Bwd;[];_∷_)

data Env : Ctx ∅ → Set

data BAPP (b : Builtin) : ∀{az}{as}
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

  V-con : {tcn : TyCon}
    → (cn : TermCon {∅} (con tcn))
    → Value (con tcn)

  V-I⇒ : ∀ b {A B as as'}
       → (p : as <>> (Term ∷ as') ∈ arity b)
       → BAPP b p (A ⇒ B)
       → Value (A ⇒ B)

  V-IΠ : ∀ b {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{as as'}
       → (p : as <>> (Type ∷ as') ∈ arity b)
       → BAPP b p (Π B)
       → Value (Π B)

data BAPP b where
  base : BAPP b (start (arity b)) (itype b)
  app : ∀{A B}{az as}
    → (p : az <>> (Term ∷ as) ∈ arity b)
    → BAPP b p (A ⇒ B)
    → Value A → BAPP b (bubble p) B
  app⋆ : ∀{B C}{az as}
    → (p : az <>> (Type ∷ as) ∈ arity b)
    → BAPP b p (Π B)
    → {A : ∅ ⊢Nf⋆ K}
    → (q : C ≡ B [ A ]Nf)
    → BAPP b (bubble p) C

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

env2ren : ∀{Γ} → Env Γ → Sub (ne ∘ `) Γ ∅
env2ren (ρ ∷ V) Z     = conv⊢ refl (sym (subNf-id _)) (discharge V)
env2ren (ρ ∷ C)                   (S x) = env2ren ρ x

dischargeBody : ∀{Γ A B} → Γ , A ⊢ B → Env Γ → ∅ , A ⊢ B
dischargeBody M ρ = conv⊢
  (cong (∅ ,_) (subNf-id _))
  (subNf-id _)
  (sub (ne ∘ `) (exts (ne ∘ `) (env2ren ρ)) M)

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
  (sub (extsNf (ne ∘ `)) (exts⋆ (ne ∘ `) (env2ren ρ)) M)

dischargeB : ∀{b A}{az}{as}{p : az <>> as ∈ arity b} → BAPP b p A → ∅ ⊢ A
dischargeB {b = b} base = ibuiltin b
dischargeB (app p bt vu) = dischargeB bt · discharge vu
dischargeB (app⋆ p bt refl) = dischargeB bt ·⋆ _

discharge (V-ƛ M ρ)  = ƛ (dischargeBody M ρ)
discharge (V-Λ M ρ)  = Λ (dischargeBody⋆ M ρ)
discharge (V-wrap V) = wrap _ _ (discharge V)
discharge (V-con c)  = con c
discharge (V-I⇒ b p bt) = dischargeB bt
discharge (V-IΠ b p bt) = dischargeB bt

BUILTIN : ∀ b {A} → BAPP b (saturated (arity b)) A → Value A ⊎ ∅ ⊢Nf⋆ *
BUILTIN addInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = inj₁ (V-con (integer (i + i')))
BUILTIN subtractInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = inj₁ (V-con (integer (i - i')))
BUILTIN multiplyInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = inj₁ (V-con (integer (i ** i')))
BUILTIN divideInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₂ (con integer))
  (inj₁ (V-con (integer (div i i'))))
BUILTIN quotientInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₂ (con integer))
  (inj₁ (V-con (integer (quot i i'))))
BUILTIN remainderInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₂ (con integer))
  (inj₁ (V-con (integer (rem i i'))))
BUILTIN modInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf
  (i' ≟ ℤ.pos 0)
  (inj₂ (con integer))
  (inj₁ (V-con (integer (mod i i'))))
BUILTIN lessThanInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i <? i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN lessThanEqualsInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i ≤? i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN greaterThanInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i I>? i')
  (inj₁ (V-con (bool true)))
  (inj₁ (V-con (bool false)))
BUILTIN greaterThanEqualsInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i I≥? i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN equalsInteger (app _ (app _ base (V-con (integer i))) (V-con (integer i'))) = decIf (i ≟ i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN concatenate (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₁ (V-con (bytestring (concat b b')))
BUILTIN takeByteString (app _ (app _ base (V-con (integer i))) (V-con (bytestring b))) = inj₁ (V-con (bytestring (take i b)))
BUILTIN dropByteString (app _ (app _ base (V-con (integer i))) (V-con (bytestring b))) = inj₁ (V-con (bytestring (drop i b)))
BUILTIN lessThanByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₁ (V-con (bool (B< b b')))
BUILTIN greaterThanByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₁ (V-con (bool (B> b b')))
BUILTIN sha2-256 (app _ base (V-con (bytestring b))) =
  inj₁ (V-con (bytestring (SHA2-256 b)))
BUILTIN sha3-256 (app _ base (V-con (bytestring b))) =
  inj₁ (V-con (bytestring (SHA3-256 b)))
BUILTIN verifySignature (app _ (app _ (app _ base (V-con (bytestring k))) (V-con (bytestring d))) (V-con (bytestring c))) with (verifySig k d c)
... | just b = inj₁ (V-con (bool b))
... | nothing = inj₂ (con bool)

BUILTIN equalsByteString (app _ (app _ base (V-con (bytestring b))) (V-con (bytestring b'))) = inj₁ (V-con (bool (equals b b')))
BUILTIN ifThenElse (app _ (app _ (app _ (app⋆ _ base refl) (V-con (bool false))) vt) vf) = inj₁ vf
BUILTIN ifThenElse (app _ (app _ (app _ (app⋆ _ base refl) (V-con (bool true))) vt) vf) = inj₁ vt
BUILTIN charToString (app _ base (V-con (char c))) = inj₁ (V-con (string (primStringFromList Data.List.[ c ])))
BUILTIN append (app _ (app _ base (V-con (string s))) (V-con (string s'))) = inj₁ (V-con (string (primStringAppend s s')))
BUILTIN trace (app _ base (V-con (string s))) =
  inj₁ (V-con (Debug.trace s unit))

convBApp : (b : Builtin) → ∀{az}{as}(p p' : az <>> as ∈ arity b)
  → ∀{A}
  → BAPP b p A
  → BAPP b p' A
convBApp b p p' q rewrite unique<>> p p' = q

BUILTIN' : ∀ b {A}{az}(p : az <>> [] ∈ arity b)
  → BAPP b p A
  → Value A ⊎ ∅ ⊢Nf⋆ *
BUILTIN' b {az = az} p q
  with sym (trans (cong ([] <><_) (sym (<>>2<>>' _ _ _ p))) (lemma<>2 az []))
... | refl = BUILTIN b (convBApp b p (saturated (arity b)) q)

open import Data.Product using (∃)

postulate
  bappTermLem : ∀  b {A}{az as}(p : az <>> (Term ∷ as) ∈ arity b)
    → BAPP b p A → ∃ λ A' → ∃ λ A'' → A ≡ A' ⇒ A''
  bappTypeLem : ∀  b {A}{az as}(p : az <>> (Type ∷ as) ∈ arity b)
    → BAPP b p A → ∃ λ K → ∃ λ (B : ∅ ,⋆ K ⊢Nf⋆ *) → A ≡ Π B

V-I : ∀ b {A : ∅ ⊢Nf⋆ *}{a as as'}
       → (p : as <>> a ∷ as' ∈ arity b)
       → BAPP b p A
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



ival : ∀ b → Value (itype b)
ival addInteger = V-I⇒ addInteger _ base
ival subtractInteger = V-I⇒ subtractInteger _ base
ival multiplyInteger = V-I⇒ multiplyInteger _ base
ival divideInteger = V-I⇒ divideInteger _ base
ival quotientInteger = V-I⇒ quotientInteger _ base
ival remainderInteger = V-I⇒ remainderInteger _ base
ival modInteger = V-I⇒ modInteger _ base
ival lessThanInteger = V-I⇒ lessThanInteger _ base
ival lessThanEqualsInteger = V-I⇒ lessThanEqualsInteger _ base
ival greaterThanInteger = V-I⇒ greaterThanInteger _ base
ival greaterThanEqualsInteger = V-I⇒ greaterThanEqualsInteger _ base
ival equalsInteger = V-I⇒ equalsInteger _ base
ival concatenate = V-I⇒ concatenate _ base
ival takeByteString = V-I⇒ takeByteString _ base
ival dropByteString = V-I⇒ dropByteString _ base
ival lessThanByteString = V-I⇒ lessThanByteString _ base
ival greaterThanByteString = V-I⇒ greaterThanByteString _ base
ival sha2-256 = V-I⇒ sha2-256 _ base
ival sha3-256 = V-I⇒ sha3-256 _ base
ival verifySignature = V-I⇒ verifySignature _ base
ival equalsByteString = V-I⇒ equalsByteString _ base
ival ifThenElse = V-IΠ ifThenElse _ base
ival charToString = V-I⇒ charToString _ base
ival append = V-I⇒ append _ base
ival trace = V-I⇒ trace _ base

{-
IBUILTIN : (b : Builtin)
    → let Φ ,, Γ ,, C = ISIG b in
      (σ : SubNf Φ ∅)
    → (tel : ITel b Γ σ)
      -----------------------------
    → Value (subNf σ C) ⊎ Error (subNf σ C)
IBUILTIN addInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (V-con (integer (i + j)))
IBUILTIN subtractInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (V-con (integer (i - j)))
IBUILTIN multiplyInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (V-con (integer (i ** j)))
IBUILTIN divideInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = inj₁ (V-con (integer (div i j)))
... | yes p = inj₂ (E-error (con integer))-- divide by zero
IBUILTIN quotientInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = inj₁ (V-con (integer (quot i j)))
... | yes p = inj₂ (E-error (con integer)) -- divide by zero
IBUILTIN remainderInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = inj₁ (V-con (integer (rem i j)))
... | yes p = inj₂ (E-error (con integer)) -- divide by zero
IBUILTIN modInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) with j ≟ Data.Integer.ℤ.pos 0
... | no ¬p = inj₁ (V-con (integer (mod i j)))
... | yes p = inj₂ (E-error (con integer)) -- divide by zero
IBUILTIN lessThanInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (decIf (i <? j) (V-con (bool true)) (V-con (bool false)))
IBUILTIN lessThanEqualsInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (decIf (i ≤? j) (V-con (bool true)) (V-con (bool false)))
IBUILTIN greaterThanInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (decIf (i I>? j) (V-con (bool true)) (V-con (bool false)))
IBUILTIN greaterThanEqualsInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (decIf (i I≥? j) (V-con (bool true)) (V-con (bool false)))
IBUILTIN equalsInteger σ ((tt ,, V-con (integer i)) ,, V-con (integer j)) =
  inj₁ (decIf (i ≟ j) (V-con (bool true)) (V-con (bool false)))
IBUILTIN concatenate σ ((tt ,, V-con (bytestring b)) ,, V-con (bytestring b')) =
  inj₁ (V-con (bytestring (concat b b')))
IBUILTIN takeByteString σ ((tt ,, V-con (integer i)) ,, V-con (bytestring b)) = inj₁ (V-con (bytestring (take i b)))
IBUILTIN dropByteString σ ((tt ,, V-con (integer i)) ,, V-con (bytestring b)) = inj₁ (V-con (bytestring (drop i b)))
IBUILTIN lessThanByteString σ ((tt ,, V-con (bytestring b)) ,, V-con (bytestring b')) = inj₁ (V-con (bool (B< b b')))
IBUILTIN greaterThanByteString σ ((tt ,, V-con (bytestring b)) ,, V-con (bytestring b')) = inj₁ (V-con (bool (B> b b')))
IBUILTIN sha2-256 σ (tt ,, V-con (bytestring b)) = inj₁ (V-con (bytestring (SHA2-256 b)))
IBUILTIN sha3-256 σ (tt ,, V-con (bytestring b)) = inj₁ (V-con (bytestring (SHA3-256 b)))
IBUILTIN verifySignature σ ((((tt ,, V-con (bytestring k)) ,, V-con (bytestring d))) ,, V-con (bytestring c)) with verifySig k d c
... | just false = inj₁ (V-con (bool false))
... | just true = inj₁ (V-con (bool true))
... | nothing = inj₂ (E-error (con bool)) -- not sure what this is for
IBUILTIN equalsByteString σ ((tt ,, V-con (bytestring b)) ,, V-con (bytestring b')) = inj₁ (V-con (bool (equals b b')))
IBUILTIN ifThenElse σ ((((tt ,, A) ,, V-con (bool true)) ,, t) ,, f) = inj₁ t
IBUILTIN ifThenElse σ ((((tt ,, A) ,, V-con (bool false)) ,, t) ,, f) = inj₁ f
IBUILTIN charToString σ (tt ,, V-con (char c)) =
  inj₁ (V-con (string (primStringFromList L.[ c ])))
IBUILTIN append σ ((tt ,, V-con (string s)) ,, V-con (string s')) = inj₁ (V-con (string (primStringAppend s s')))
IBUILTIN trace σ _ = inj₁ (V-con unit)

IBUILTIN' : (b : Builtin)
    → let Φ ,, Γ ,, C = ISIG b in
      ∀{Φ'}{Γ' : Ctx Φ'}
    → (p : Φ ≡ Φ')
    → (q : substEq Ctx p Γ ≡ Γ')
      (σ : SubNf Φ' ∅)
    → (tel : ITel b Γ' σ)
    → (C' : Φ' ⊢Nf⋆ *)
    → (r : substEq (_⊢Nf⋆ *) p C ≡ C')
      -----------------------------
    → Value (subNf σ C') ⊎ Error (subNf σ C')
    
IBUILTIN' b refl refl σ tel _ refl = IBUILTIN b σ tel
-}


step : ∀{T} → State T → State T
step (s ; ρ ▻ ` x)             = s ◅ lookup x ρ
step (s ; ρ ▻ ƛ L)             = s ◅ V-ƛ L ρ
step (s ; ρ ▻ (L · M))         = (s , -· M ρ) ; ρ ▻ L
step (s ; ρ ▻ Λ L)             = s ◅ V-Λ L ρ
step (s ; ρ ▻ (L ·⋆ A))        = (s , -·⋆ A) ; ρ ▻ L
step (s ; ρ ▻ wrap A B L) = (s , wrap-) ; ρ ▻ L
step (s ; ρ ▻ unwrap L) = (s , unwrap-) ; ρ ▻ L
step (s ; ρ ▻ con c) = s ◅ V-con c
step (s ; ρ ▻ ibuiltin b) = s ◅ ival b
  -- ^ this is constant here, so we drop the env
step (s ; ρ ▻ error A) = ◆ A
step (ε ◅ V) = □ V
step ((s , -· M ρ') ◅ V) = (s , V ·-) ; ρ' ▻ M
step ((s , (V-ƛ M ρ ·-)) ◅ V) = s ; ρ ∷ V ▻ M
step ((s , -·⋆ A) ◅ V-Λ M ρ) = s ; ρ ▻ (M [ A ]⋆)
step ((s , wrap- {A = A}{B = B}) ◅ V) = s ◅ V-wrap V
step ((s , unwrap-) ◅ V-wrap V) = s ◅ V
step ((s , (V-I⇒ b {as' = []} p x₁ ·-)) ◅ V)
  with BUILTIN' b (bubble p) (app p x₁ V)
... | inj₁ V = s ◅ V
... | inj₂ A = ◆ A
step ((s , (V-I⇒ b {as' = x₂ ∷ as'} p x₁ ·-)) ◅ V) =
  s ◅ V-I b (bubble p) (app p x₁ V)
step ((s , -·⋆ A) ◅ V-IΠ b {as' = []} p x₁)
  with BUILTIN' b (bubble p) (app⋆ p x₁ refl)
... | inj₁ V = s ◅ V
... | inj₂ A = ◆ A
step ((s , -·⋆ A) ◅ V-IΠ b {as' = x₂ ∷ as'} p x₁) =
  s ◅ V-I b (bubble p) (app⋆ p x₁ refl)
step (□ V) = □ V
step (◆ A) = ◆ A

open import Data.Nat

stepper : ℕ → ∀{T} → State T → Either RuntimeError (State T)
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ; ρ ▻ M) = stepper n (s ; ρ ▻ M)
stepper (suc n) st | (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)

