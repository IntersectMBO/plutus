# CK machine

```
module Algorithmic.CK where
```

```
open import Function
open import Data.Bool using (Bool;true;false)
open import Data.List as L using (List;[];_∷_)
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality using (inspect;sym;trans;_≡_;refl;cong)
  renaming ([_] to [[_]];subst to substEq)
open import Data.Unit using (tt)
open import Data.Product renaming (_,_ to _,,_)
import Data.Sum as Sum
open import Data.Empty
open import Utils
open import Type
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Algorithmic
open import Algorithmic.Reduction hiding (step;Error)
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNBE
open import Algorithmic.RenamingSubstitution
```

```
-- this could also be presented as a relation and then there would be
-- more function rather like progress

vtel-lem : ∀{Δ}{As As' : List (Δ ⊢Nf⋆ *)} (σ : ∀{K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
  → (p : As' ≡ As)
  → (ts : Tel ∅ Δ σ As')
  → VTel Δ σ As' ts
  → VTel Δ σ As (substEq (Tel ∅ Δ σ) p ts)
vtel-lem σ refl ts vs = vs

-- recontructing the telescope after an element has been evaluated

reconstTel : ∀{Φ Γ Δ As} Bs Ds
    → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (telB : Tel Γ Δ σ Bs)
    → ∀{C}(t' : Γ ⊢ substNf σ C)
    → (p : Bs L.++ (C ∷ Ds) ≡ As)
    → (tel' : Tel Γ Δ σ Ds)
    → Tel Γ Δ σ As
reconstTel [] Ds σ telB t' refl telD = t' ∷ telD
reconstTel (B ∷ Bs) Ds σ (X ∷ telB) t' refl tel' =
  X ∷ reconstTel Bs Ds σ telB t' refl tel'

extendVTel : ∀{Δ As} Bs
    → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (ts : Tel ∅ Δ σ Bs)
    → VTel Δ σ Bs ts 
    → ∀{C}(t' : ∅ ⊢ substNf σ C)
    → Value t'
    → (p : Bs L.++ (C ∷ []) ≡ As)
    → VTel Δ σ As (reconstTel Bs [] σ ts t' p [])

extendVTel [] σ [] _ t' vt' refl = vt' ,, _
extendVTel (B ∷ Bs) σ (t ∷ ts) (v ,, vs) t' v' refl =
  v ,, extendVTel Bs σ ts vs t' v' refl

data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·_     : {A B : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → Frame B A
  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K) → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (μ A B) (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  unwrap- : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) (μ A B)

  builtin- : ∀(b : Builtin)
    → (σ : SubNf (proj₁ (SIG b)) ∅)
    → (As : List (proj₁ (SIG b) ⊢Nf⋆ *))
    → (ts : Tel ∅ (proj₁ (SIG b)) σ As)
    → VTel (proj₁ (SIG b)) σ As ts
    → (A : (proj₁ (SIG b) ⊢Nf⋆ *))
    → (As' : List (proj₁ (SIG b) ⊢Nf⋆ *))
    → proj₁ (proj₂ (SIG b)) ≡ As L.++ A ∷ As'
    → Tel ∅ (proj₁ (SIG b)) σ As'
    → Frame (substNf σ (proj₂ (proj₂ (SIG b)))) (substNf σ A)

data Stack : (T : ∅ ⊢Nf⋆ *)(H : ∅ ⊢Nf⋆ *) → Set where
  ε   : {T : ∅ ⊢Nf⋆ *} → Stack T T
  _,_ : {T : ∅ ⊢Nf⋆ *}{H1 : ∅ ⊢Nf⋆ *}{H2 : ∅ ⊢Nf⋆ *}
    → Stack T H1 → Frame H1 H2 → Stack T H2

data State (T : ∅ ⊢Nf⋆ *) : Set where
  _▻_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → ∅ ⊢ H → State T
  _◅_ : {H : ∅ ⊢Nf⋆ *} → Stack T H → {t : ∅ ⊢ H} → Value t → State T
  □  : {t : ∅ ⊢ T} →  Value t → State T
  ◆   : (A : ∅ ⊢Nf⋆ *)  →  State T

-- Plugging a term of suitable type into a frame yields a term again
closeFrame : ∀{T H} → Frame T H → ∅ ⊢ H → ∅ ⊢ T
closeFrame (-· u)          t = t · u
closeFrame (_·- {t = t} v) u = t · u
closeFrame (-·⋆ A)         t = _·⋆_ t A
closeFrame wrap-           t = wrap _ _ t
closeFrame unwrap-         t = unwrap t
closeFrame (builtin- b σ As ts vts A As' p ts') t =
  builtin b σ (reconstTel As As' σ ts t (sym p) ts' )
-- Plugging a term into a stack yields a term again

closeStack : ∀{T H} → Stack T H → ∅ ⊢ H → ∅ ⊢ T
closeStack ε       t = t
closeStack (s , f) t = closeStack s (closeFrame f t)

-- a state can be closed to yield a term again

closeState : ∀{T} → State T → ∅ ⊢ T
closeState (s ▻ t)           = closeStack s t
closeState (_◅_ s {t = t} v) = closeStack s t
closeState (□ {t = t} v)     = t
closeState (◆ A)             = error _

discharge : ∀{A : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A} → Value t → ∅ ⊢ A
discharge {t = t} _ = t

step : ∀{A} → State A → State A
step (s ▻ ƛ L)                    = s ◅ V-ƛ L
step (s ▻ (L · M))                = (s , -· M) ▻ L
step (s ▻ Λ L)                    = s ◅ V-Λ L
step (s ▻ (L ·⋆ A))               = (s , -·⋆ A) ▻ L
step (s ▻ wrap A B L)             = (s , wrap-) ▻ L
step (s ▻ unwrap L)               = (s , unwrap-) ▻ L
step (s ▻ con cn)                 = s ◅ V-con cn
step (s ▻ error A)                = ◆ A
step (ε ◅ V)                      = □ V
step ((s , (-· M)) ◅ V)           = ((s , V ·-) ▻ M)
step ((s , (V-ƛ t ·-)) ◅ V)       = s ▻ (t [ discharge V ])
step ((s , (-·⋆ A)) ◅ V-Λ t)      = s ▻ (t [ A ]⋆)
step ((s , wrap-) ◅ V)            = s ◅ (V-wrap V)
step ((s , unwrap-) ◅ V-wrap V)   = s ◅ V
step (s ▻ builtin bn σ tel)
  with proj₁ (proj₂ (SIG bn)) | inspect (proj₁ ∘ (proj₂ ∘ SIG)) bn
step (s ▻ builtin bn σ []) | [] | [[ p ]] = 
  s ▻ BUILTIN bn σ (substEq (Tel ∅ _ σ) (sym p) []) (vtel-lem σ (sym p) [] tt)
step (s ▻ builtin bn σ (t ∷ ts)) | A ∷ As | [[ p ]] =
  (s , builtin- bn σ [] [] _ A As p ts) ▻ t
step ( _◅_ (s , (builtin- b σ As ts vts A .[] p [])) {t = t} V) =
  s ▻ BUILTIN b
              σ
              (reconstTel As [] σ ts t (sym p) [])
              (extendVTel As σ ts vts t V (sym p))
step (_◅_ (s , builtin- b σ As ts vts A (A' ∷ As') p (t' ∷ ts')) {t = t} V) =
  (s , builtin-
        b
        σ
        (As L.++ L.[ A ])
        (reconstTel As [] σ ts t refl [])
        (extendVTel As σ ts vts t V refl)
        A'
        As'
        (trans p (sym (++-assoc As L.[ A ] (A' ∷ As')))) ts')
  ▻ t'

step (s ▻ ibuiltin b) = s ◅ ival b
step ((s , (V-I⇒ b p q r σ base vs f ·-)) ◅ v) =
  s ▻ IBUILTIN' b p q σ (vs ,, deval v ,, v) _ r
step ((s , (V-I⇒ b p q r σ (skip⋆ p') vs f ·-)) ◅ v) =
  s ◅ (V-IΠ b p q r σ p' (vs ,, deval v ,, v) (f · deval v))
step ((s , (V-I⇒ b p q r σ (skip p') vs f ·-)) ◅ v) =
  s ◅ V-I⇒ b p q r σ p' (vs ,, deval v ,, v) (f · deval v)
step ((s , -·⋆ A) ◅ V-IΠ b p q r σ p' vs f)  = ◆ (itype b)

step (□ V)                        = □ V
step (◆ A)                        = ◆ A

open import Data.Nat

stepper : ℕ → ∀{T}
  → State T
  → Either RuntimeError (State T)
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ▻ M) = stepper n (s ▻ M)
stepper (suc n) st | (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)

