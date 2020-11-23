# CEK machine that discharges builtin args

```
module Algorithmic.CEKC where

open import Agda.Builtin.String using (primStringFromList; primStringAppend)
open import Data.Bool using (Bool;true;false)
open import Data.Product using (Σ;_×_;proj₁;proj₂) renaming (_,_ to _,,_)
open import Function using (_∘_;id)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;sym;trans;inspect) renaming ([_] to [[_]];subst to substEq)
import Data.List as L
open import Data.List.Properties
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Data.Unit using (⊤;tt)
import Debug.Trace as Debug
open import Utils

open import Type
open import Type.BetaNormal
open import Type.BetaNBE hiding (Env)
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Algorithmic.Reduction using (VERIFYSIG)
open import Algorithmic.RenamingSubstitution
open import Builtin
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Utils using (decIf)

-- this could still be imported from Alg/Reduction
-- but BUILTIN is going to have to change
data Value :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}
    → (M : Γ , A ⊢ B)
      ---------------------------
    → Value (ƛ M)

  V-Λ : ∀ {Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}
    → (M : Γ ,⋆ K ⊢ B)
      ----------------
    → Value (Λ M)

  V-wrap : ∀{Φ Γ K}
   → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : Φ ⊢Nf⋆ K}
   → {term : Γ ⊢  _}
   → Value term
   → Value (wrap A B term)

  V-con : ∀{Φ Γ}{tcn : TyCon}
    → (cn : TermCon (con tcn))
    → Value {Γ = Γ} (con {Φ} cn)

Clos : ∅ ⊢Nf⋆ * → Set

data Env : Ctx ∅ → Set where
  []   : Env ∅
  _∷_ : ∀{Γ A} → Env Γ → Clos A → Env (Γ , A)

Clos A = Σ (Ctx ∅) λ Γ → Σ (Γ ⊢ A) λ M → Value M × Env Γ

lookup : ∀{Γ A} → Γ ∋ A → Env Γ → Clos A
lookup Z     (ρ ∷ c) = c
lookup (S x) (ρ ∷ c) = lookup x ρ

CTel : ∀ Δ → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)(As : L.List (Δ ⊢Nf⋆ *)) → Set
CTel Δ σ L.[]       = ⊤
CTel Δ σ (A L.∷ As) = Clos (substNf σ A) × CTel Δ σ As

BUILTIN : (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (ctel : CTel Δ σ As)
      -----------------------------
    → Σ (Ctx ∅) λ Γ → Γ ⊢ substNf σ C × Env Γ

BUILTIN addInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, con (integer (i + i')) ,, []
BUILTIN subtractInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, con (integer (i - i')) ,, []
BUILTIN multiplyInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, con (integer (i ** i')) ,, []
BUILTIN divideInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, decIf (i' ≟ ℤ.pos 0) (error _) (con (integer (div i i'))) ,, []
BUILTIN quotientInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, decIf (i' ≟ ℤ.pos 0) (error _) (con (integer (quot i i'))) ,, []
BUILTIN remainderInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, decIf (i' ≟ ℤ.pos 0) (error _) (con (integer (rem i i'))) ,, []
BUILTIN modInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, decIf (i' ≟ ℤ.pos 0) (error _) (con (integer (mod i i'))) ,, []
BUILTIN lessThanInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, decIf (i <? i') (con (bool true)) (con (bool false)) ,, []
BUILTIN lessThanEqualsInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, decIf (i ≤? i') (con (bool true)) (con (bool false)) ,, []
BUILTIN greaterThanInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, decIf (i Builtin.Constant.Type.>? i') (con (bool true)) (con (bool false)) ,, []
BUILTIN greaterThanEqualsInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, decIf (i ≥? i') (con (bool true)) (con (bool false)) ,, []
BUILTIN equalsInteger σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (integer i') ,, _) ,, tt) = _ ,, decIf (i ≟ i') (con (bool true)) (con (bool false)) ,, []
BUILTIN concatenate σ ((_ ,, _ ,, V-con (bytestring b) ,, _) ,, (_ ,, _ ,, V-con (bytestring b') ,, _) ,, tt) = _ ,, con (bytestring (concat b b')) ,, []
BUILTIN takeByteString σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (bytestring b) ,, _) ,, tt) = _ ,, con (bytestring (take i b)) ,, []
BUILTIN dropByteString σ ((_ ,, _ ,, V-con (integer i) ,, _) ,, (_ ,, _ ,, V-con (bytestring b) ,, _) ,, tt) = _ ,, con (bytestring (drop i b)) ,, []
BUILTIN sha2-256 σ ((_ ,, _ ,, V-con (bytestring b) ,, _) ,, tt) = _ ,, (con (bytestring (SHA2-256 b))) ,, []
BUILTIN sha3-256 σ ((_ ,, _ ,, V-con (bytestring b) ,, _) ,, tt) = _ ,, (con (bytestring (SHA3-256 b))) ,, []
BUILTIN verifySignature σ ((_ ,, _ ,, V-con (bytestring k) ,, _) ,, (_ ,, _ ,, V-con (bytestring d) ,, _) ,, (_ ,, _ ,, V-con (bytestring c) ,, _) ,, tt) = _ ,, VERIFYSIG (verifySig k d c) ,, []
BUILTIN equalsByteString σ ((_ ,, _ ,, V-con (bytestring b) ,, _) ,, (_ ,, _ ,, V-con (bytestring b') ,, _) ,, tt) = _ ,, con (bool (equals b b')) ,, []
BUILTIN ifThenElse σ ((_ ,, _ ,, V-con (bool true) ,, _) ,, (_ ,, t ,, _ ,, ρ) ,, _ ,, tt) = _ ,, t ,, ρ
BUILTIN ifThenElse σ ((_ ,, _ ,, V-con (bool false) ,, _) ,, _ ,, (_ ,, u ,, _ ,, ρ) ,, tt) = _ ,, u ,, ρ
BUILTIN charToString _ ((_ ,, _ ,, V-con (char c) ,, _) ,, tt) = _ ,, con (string (primStringFromList L.[ c ])) ,, []
BUILTIN append _ ((_ ,, _ ,, V-con (string s) ,, _) ,, (_ ,, _ ,, V-con (string t) ,, _) ,, tt) =
  _ ,, con (string (primStringAppend s t)) ,, []
BUILTIN trace _ ((_ ,, _ ,, V-con (string s) ,, _) ,, tt) = _ ,, con (Debug.trace s unit) ,, []

data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·     : ∀{Γ}{A B : ∅ ⊢Nf⋆ *} → Γ ⊢ A → Env Γ → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *} → Clos (A ⇒ B) → Frame B A

  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K)
    → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (μ A B) (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  unwrap- : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) (μ A B)

  builtin- : ∀{Γ}(b : Builtin)
    → (σ : ∀ {K} → proj₁ (SIG b) ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (As : L.List (proj₁ (SIG b) ⊢Nf⋆ *))
    → (cs : CTel (proj₁ (SIG b)) σ As)
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
  _;_◅_ : ∀{Γ}{H : ∅ ⊢Nf⋆ *} → Stack T H → Env Γ → {M : Γ ⊢ H} → Value M → State T
  □     : Clos T → State T
  ◆     : ∅ ⊢Nf⋆ * → State T

discharge : ∀{Γ A}{M : Γ ⊢ A} → Value M → Env Γ → Σ (∅ ⊢ A) Value

env2ren : ∀{Γ} → Env Γ → Sub (ne ∘ `) Γ ∅
env2ren (ρ ∷ (_ ,, M ,, V ,, ρ')) Z     =
 conv⊢ refl (sym (substNf-id _)) (proj₁ (discharge V ρ'))
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

discharge (V-ƛ M)    ρ = _ ,, V-ƛ (dischargeBody M ρ)
discharge (V-Λ M)    ρ = _ ,, V-Λ (dischargeBody⋆ M ρ)
discharge (V-wrap V) ρ = _ ,, V-wrap (proj₂ (discharge V ρ))
discharge (V-con c)  ρ = _ ,, V-con c


-- telescope rangling

-- recontructing the telescope after an element has been evaluated

reconstTel : ∀{Φ Γ Δ As} Bs Ds
    → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (telB : Tel Γ Δ σ Bs)
    → ∀{C}(t' : Γ ⊢ substNf σ C)
    → (p : Bs L.++ (C L.∷ Ds) ≡ As)
    → (tel' : Tel Γ Δ σ Ds)
    → Tel Γ Δ σ As
reconstTel L.[] Ds σ telB t' refl telD = t' ∷ telD
reconstTel (B L.∷ Bs) Ds σ (X ∷ telB) t' refl tel' =
  X ∷ reconstTel Bs Ds σ telB t' refl tel'

extendCTel : ∀{Δ As} Bs
    → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (cs : CTel Δ σ Bs)
    → ∀{C}(c : Clos (substNf σ C))
    → (p : Bs L.++ (C L.∷ L.[]) ≡ As)
    → CTel Δ σ As
extendCTel L.[] σ cs c refl = c ,, _
extendCTel (B L.∷ Bs) σ (c ,, cs) c' refl = c ,, extendCTel Bs σ cs c' refl

dischargeTel : ∀{Γ Δ As}
    → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (ts : Tel Γ Δ σ As)
    → Env Γ
    → Tel ∅ Δ σ As

dischargeTel σ [] ρ = []
dischargeTel {As = A L.∷ As} σ (t ∷ ts) ρ = conv⊢ refl (substNf-id (substNf σ A)) (subst (ne ∘ `) (env2ren ρ) t) Tel.∷ dischargeTel σ ts ρ

step : ∀{T} → State T → State T
step (s ; ρ ▻ ` x)      = let Γ ,, M ,, V ,, ρ' = lookup x ρ in s ; ρ' ◅ V
step (s ; ρ ▻ ƛ M)      = s ; ρ ◅ V-ƛ M
step (s ; ρ ▻ (L · M))  = (s , -· M ρ) ; ρ ▻ L
step (s ; ρ ▻ Λ M)      = s ; ρ ◅ V-Λ M
step (s ; ρ ▻ (M ·⋆ A)) = (s , -·⋆ A) ; ρ ▻ M
step (s ; ρ ▻ wrap A B M) = (s , wrap-) ; ρ ▻ M
step (s ; ρ ▻ unwrap M) = (s , unwrap-) ; ρ ▻ M
step (s ; ρ ▻ con c) = s ; ρ ◅ V-con c
step (s ; ρ ▻ builtin bn σ ts) with proj₁ (proj₂ (SIG bn)) | inspect (proj₁ ∘ proj₂ ∘ SIG) bn
... | L.[]     | [[ p ]] =
  let _ ,, M ,, ρ' = BUILTIN bn σ (substEq (CTel (proj₁ (SIG bn)) σ ) (sym p) _)  in  s ; ρ' ▻ M
step (s ; ρ ▻ builtin bn σ (t ∷ ts)) | A L.∷ As | [[ p ]] =
  (s , builtin- bn σ L.[] _ A As p ts ρ) ; ρ ▻ t
step (s ; ρ ▻ error A) = ◆ A
step (ε ; ρ ◅ V) = □ (_ ,, _ ,, V ,, ρ)
step ((s , -· M ρ') ; ρ ◅ V) = (s , ((_ ,, _ ,, V ,, ρ) ·-)) ; ρ' ▻ M
step ((s , ((_ ,, ƛ M ,, V-ƛ .M ,, ρ') ·-)) ; ρ ◅ V) =
  s ; ρ' ∷ (_ ,, _ ,, V ,, ρ) ▻ M
step ((s , -·⋆ A) ; ρ ◅ V-Λ M) = s ; ρ ▻ (M [ A ]⋆)
step ((s , wrap-) ; ρ ◅ V) = s ; ρ ◅ V-wrap V
step ((s , unwrap-) ; ρ ◅ V-wrap V) = s ; ρ ◅ V
step ((s , builtin- b σ As cs A .L.[] p [] ρ') ; ρ ◅ V) =
  let _ ,, M ,, ρ' = BUILTIN b σ (extendCTel As σ cs (_ ,, _ ,, V ,, ρ) (sym p)) in s ; ρ' ▻ M
step ((s , builtin- b σ As cs A (A' L.∷ As') p (t' ∷ ts') ρ') ; ρ ◅ V) =
   (s , builtin-
        b
        σ
        (As L.++ L.[ A ])
        (extendCTel As σ cs (_ ,, _ ,, V ,, ρ) refl)
        A'
        As'
        (trans p (sym (++-assoc As L.[ A ] (A' L.∷ As'))))
        ts'
        ρ')

  ; ρ' ▻ t'
step (□ C)       = □ C
step (◆ A)       = ◆ A

open import Data.Nat

stepper : ℕ → ∀{T} → State T → Either RuntimeError (State T)
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ; ρ ▻ M) = stepper n (s ; ρ ▻ M)
stepper (suc n) st | (s ; ρ ◅ V) = stepper n (s ; ρ ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)
