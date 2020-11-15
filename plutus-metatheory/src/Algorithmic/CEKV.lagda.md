# CEK machine that discharges builtin args

```
module Algorithmic.CEKV where

open import Agda.Builtin.String using (primStringFromList; primStringAppend)
open import Function hiding (_∋_)
open import Data.Product using (proj₁;proj₂)
import Data.List as L
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]];subst to substEq)
open import Data.Unit using (⊤;tt)
open import Data.Product using (_×_) renaming (_,_ to _,,_)
open import Data.Sum
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Data.Bool using (true;false)
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

data Env : Ctx ∅ → Set

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

data Env where
  [] : Env ∅
  _∷_ : ∀{Γ A} → Env Γ → Value A → Env (Γ , A)

lookup : ∀{Γ A} → Γ ∋ A → Env Γ → Value A
lookup Z     (ρ ∷ v) = v
lookup (S x) (ρ ∷ v) = lookup x ρ

discharge : ∀{A} → Value A → ∅ ⊢ A

env2ren : ∀{Γ} → Env Γ → Sub (ne ∘ `) Γ ∅
env2ren (ρ ∷ V) Z     = conv⊢ refl (sym (substNf-id _)) (discharge V)
env2ren (ρ ∷ C)                   (S x) = env2ren ρ x

dischargeBody : ∀{Γ A B} → Γ , A ⊢ B → Env Γ → ∅ , A ⊢ B
dischargeBody M ρ = conv⊢
  (cong (∅ ,_) (substNf-id _))
  (substNf-id _)
  (subst (ne ∘ `) (exts (ne ∘ `) (env2ren ρ)) M)

dischargeBody⋆ : ∀{Γ K A} → Γ ,⋆ K ⊢ A → Env Γ → ∅ ,⋆ K ⊢ A
dischargeBody⋆ {A = A} M ρ = conv⊢
  refl
  (trans
    (substNf-cong
      {f = extsNf (ne ∘ `)}
      {g = ne ∘ `}
      (λ{ Z → refl; (S α) → refl})
      A)
    (substNf-id A))
  (subst (extsNf (ne ∘ `)) (exts⋆ (ne ∘ `) (env2ren ρ)) M)

discharge (V-ƛ M ρ)  = ƛ (dischargeBody M ρ)
discharge (V-Λ M ρ)  = Λ (dischargeBody⋆ M ρ)
discharge (V-wrap V) = wrap _ _ (discharge V)
discharge (V-con c)  = con c

VTel : ∀ Δ → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)(As : L.List (Δ ⊢Nf⋆ *)) → Set
VTel Δ σ L.[]       = ⊤
VTel Δ σ (A L.∷ As) = Value (substNf σ A) × VTel Δ σ As

extendVTel : ∀{Δ As} Bs
    → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (vs : VTel Δ σ Bs)
    → ∀{C}(v : Value (substNf σ C))
    → (p : Bs L.++ (C L.∷ L.[]) ≡ As)
    → VTel Δ σ As
extendVTel L.[] σ vs v refl = v ,, _
extendVTel (B L.∷ Bs) σ (v ,, vs) v' refl = v ,, extendVTel Bs σ vs v' refl

BUILTIN : (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (vtel : VTel Δ σ As)
      -----------------------------
    → Value (substNf σ C) ⊎ ∅ ⊢Nf⋆ *
BUILTIN addInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  inj₁ (V-con (integer (i + i')))
BUILTIN subtractInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  inj₁ (V-con (integer (i - i')))
BUILTIN multiplyInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  inj₁ (V-con (integer (i ** i')))
BUILTIN divideInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i' ≟ ℤ.pos 0) (inj₂ (con integer)) (inj₁ (V-con (integer (div i i'))))
BUILTIN quotientInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i' ≟ ℤ.pos 0) (inj₂ (con integer)) (inj₁ (V-con (integer (quot i i'))))
BUILTIN remainderInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i' ≟ ℤ.pos 0) (inj₂ (con integer)) (inj₁ (V-con (integer (rem i i'))))
BUILTIN modInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i' ≟ ℤ.pos 0) (inj₂ (con integer)) (inj₁ (V-con (integer (mod i i'))))
BUILTIN lessThanInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i <? i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN
  lessThanEqualsInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i ≤? i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN greaterThanInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i Builtin.Constant.Type.>? i')
        (inj₁ (V-con (bool true)))
        (inj₁ (V-con (bool false)))
BUILTIN
  greaterThanEqualsInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i ≥? i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN equalsInteger σ (V-con (integer i) ,, V-con (integer i') ,, tt) =
  decIf (i ≟ i') (inj₁ (V-con (bool true))) (inj₁ (V-con (bool false)))
BUILTIN concatenate σ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) =
  inj₁ (V-con (bytestring (concat b b')))
BUILTIN takeByteString σ (V-con (integer i) ,, V-con (bytestring b) ,, tt) =
  inj₁ (V-con (bytestring (take i b)))
BUILTIN dropByteString σ (V-con (integer i) ,, V-con (bytestring b) ,, tt) =
  inj₁ (V-con (bytestring (drop i b)))
BUILTIN sha2-256 σ (V-con (bytestring b) ,, tt) =
  inj₁ (V-con (bytestring (SHA2-256 b)))
BUILTIN sha3-256 σ (V-con (bytestring b) ,, tt) =
  inj₁ (V-con (bytestring (SHA3-256 b)))
BUILTIN
  verifySignature
  σ
  (V-con (bytestring k)
   ,,
   V-con (bytestring d)
   ,,
   V-con (bytestring c)
   ,,
   tt) with (verifySig k d c)
... | just b = inj₁ (V-con (bool b))
... | nothing = inj₂ (con bool)

BUILTIN equalsByteString σ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) = inj₁ (V-con (bool (equals b b')))
BUILTIN ifThenElse σ (V-con (bool false) ,, VT ,, VF ,, tt) = inj₁ VF
BUILTIN ifThenElse σ (V-con (bool true)  ,, VT ,, VF ,, tt) = inj₁ VT
BUILTIN charToString σ (V-con (char c) ,, tt) = inj₁ (V-con (string (primStringFromList L.[ c ])))
BUILTIN append σ (V-con (string s) ,, V-con (string t) ,, tt) = inj₁ (V-con (string (primStringAppend s t)))
BUILTIN trace σ (V-con (string s) ,, tt) = inj₁ (V-con (Debug.trace s unit))

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

  builtin- : ∀{Γ}(b : Builtin)
    → (σ : ∀ {K} → proj₁ (SIG b) ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (As : L.List (proj₁ (SIG b) ⊢Nf⋆ *))
    → (vs : VTel (proj₁ (SIG b)) σ As)
    → (A : (proj₁ (SIG b) ⊢Nf⋆ *))
    → (As' : L.List (proj₁ (SIG b) ⊢Nf⋆ *))
    → proj₁ (proj₂ (SIG b)) ≡ As L.++ A L.∷ As'
    → Tel Γ (proj₁ (SIG b)) σ As'
    → Env Γ
    → Frame (substNf σ (proj₂ (proj₂ (SIG b)))) (substNf σ A)

data Stack (T : ∅ ⊢Nf⋆ *) : (H : ∅ ⊢Nf⋆ *) → Set where
  ε   : Stack T T
  _,_ : ∀{H1 H2} → Stack T H1 → Frame H1 H2 → Stack T H2

data State (T : ∅ ⊢Nf⋆ *) : Set where
  _;_▻_ : ∀{Γ}{H : ∅ ⊢Nf⋆ *} → Stack T H → Env Γ → Γ ⊢ H → State T
  _◅_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → Value H → State T
  □     : Value T → State T
  ◆     : ∅ ⊢Nf⋆ * → State T

step : ∀{T} → State T → State T
step (s ; ρ ▻ ` x)             = s ◅ lookup x ρ
step (s ; ρ ▻ ƛ L)             = s ◅ V-ƛ L ρ
step (s ; ρ ▻ (L · M))         = (s , -· M ρ) ; ρ ▻ L
step (s ; ρ ▻ Λ L)             = s ◅ V-Λ L ρ
step (s ; ρ ▻ (L ·⋆ A))        = (s , -·⋆ A) ; ρ ▻ L
step (s ; ρ ▻ wrap A B L) = (s , wrap-) ; ρ ▻ L
step (s ; ρ ▻ unwrap L) = (s , unwrap-) ; ρ ▻ L
step (s ; ρ ▻ con c) = s ◅ V-con c
step (s ; ρ ▻ builtin bn σ ts) with proj₁ (proj₂ (SIG bn)) | inspect (proj₁ ∘ proj₂ ∘ SIG) bn
step (s ; ρ ▻ builtin bn σ [])       | L.[]     | [[ p ]]
  with BUILTIN bn σ (substEq (VTel (proj₁ (SIG bn)) σ ) (sym p) _)
... | inj₁ V = s ◅ V
... | inj₂ A = ◆ A
step (s ; ρ ▻ builtin bn σ (t ∷ ts)) | A L.∷ As | [[ p ]] =
  (s , builtin- bn σ L.[] _ A As p ts ρ) ; ρ ▻ t
step (s ; ρ ▻ error A) = ◆ A
step (ε ◅ V) = □ V
step ((s , -· M ρ') ◅ V) = (s , V ·-) ; ρ' ▻ M
step ((s , (V-ƛ M ρ ·-)) ◅ V) = s ; ρ ∷ V ▻ M
step ((s , -·⋆ A) ◅ V-Λ M ρ) = s ; ρ ▻ (M [ A ]⋆)
step ((s , wrap- {A = A}{B = B}) ◅ V) = s ◅ V-wrap V
step ((s , unwrap-) ◅ V-wrap V) = s ◅ V
step ((s , builtin- b σ As vs A L.[] p ts' ρ) ◅ V)
  with BUILTIN b σ (extendVTel As σ vs V (sym p))
... | inj₁ V' = s ◅ V'
... | inj₂ A' = ◆ A'
step ((s , builtin- b σ As vs A (A' L.∷ As') p (t' ∷ ts') ρ) ◅ V) =
  (s , builtin-
         b
         σ
         (As L.++ L.[ A ])
         (extendVTel As σ vs V refl)
         A'
         As'
         (trans p (sym (++-assoc As L.[ A ] (A' L.∷ As'))))
         ts'
         ρ)
   ; ρ ▻ t'
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
