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

vtel-lem : ∀{Φ}{Γ Δ}{As As' : List (Δ ⊢Nf⋆ *)} (σ : ∀{K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  → (p : As' ≡ As)
  → (ts : Tel Γ Δ σ As')
  → VTel Γ Δ σ As' ts
  → VTel Γ Δ σ As (substEq (Tel Γ Δ σ) p ts)
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

extendVTel : ∀{Φ Γ Δ As} Bs
    → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (ts : Tel Γ Δ σ Bs)
    → VTel Γ Δ σ Bs ts 
    → ∀{C}(t' : Γ ⊢ substNf σ C)
    → Value t'
    → (p : Bs L.++ (C ∷ []) ≡ As)
    → VTel Γ Δ σ As (reconstTel Bs [] σ ts t' p [])

extendVTel [] σ [] _ t' vt' refl = vt' ,, _
extendVTel (B ∷ Bs) σ (t ∷ ts) (v ,, vs) t' v' refl =
  v ,, extendVTel Bs σ ts vs t' v' refl

data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·_     : {A B : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → Frame B A
  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K)
    → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{pat : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : ∅ ⊢Nf⋆ K}
    → Frame (ne (μ1 · pat · arg))
            (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
  unwrap- : ∀{K}{pat : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{arg : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf pat · (μ1 · embNf pat) · embNf arg))
            (ne (μ1 · pat · arg))

  builtin- : ∀(b : Builtin)
    → (σ : ∀ {K} → proj₁ (SIG b) ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (As : List (proj₁ (SIG b) ⊢Nf⋆ *))
    → (ts : Tel ∅ (proj₁ (SIG b)) σ As)
    → VTel ∅ (proj₁ (SIG b)) σ As ts
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
closeFrame wrap-           t = wrap1 _ _ t
closeFrame unwrap-         t = unwrap1 t
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

-- this function, apart from making a step, also determines the
-- contexts and provides a proof.  These things could be done
-- seperately.

deval : ∀{A : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A} → Value t → ∅ ⊢ A
deval {t = t} _ = t

step : ∀{A} → State A → State A
step (s ▻ ƛ L)                    = s ◅ V-ƛ L
step (s ▻ (L · M))                = (s , -· M) ▻ L
step (s ▻ Λ L)                    = s ◅ V-Λ L
step (s ▻ (L ·⋆ A))               = (s , -·⋆ A) ▻ L
step (s ▻ wrap1 pat arg L)        = (s , wrap-) ▻ L
step (s ▻ unwrap1 L)              = (s , unwrap-) ▻ L
step (s ▻ con cn)                 = s ◅ V-con cn
step (s ▻ error A)                = ◆ A
step (ε ◅ V)                      = □ V
step ((s , (-· M)) ◅ V)           = ((s , V ·-) ▻ M)
step ((s , (V-ƛ t ·-)) ◅ V)       = s ▻ (t [ deval V ])
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
step (□ V)                        = □ V
step (◆ A)                        = ◆ A

open import Data.Nat

stepper : ℕ → ∀{T}
  → State T
  → Either Error (State T)
stepper zero st = inj₁ gasError
stepper (suc n) st with step st
stepper (suc n) st | (s ▻ M) = stepper n (s ▻ M)
stepper (suc n) st | (s ◅ V) = stepper n (s ◅ V)
stepper (suc n) st | (□ V)   = return (□ V)
stepper (suc n) st | ◆ A     = return (◆ A)
```

This is the property I would like to have, but it cannot be proved directly like this:

```
open import Relation.Binary.PropositionalEquality

{-
preservation : ∀ n {Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(p : NoVar Γ)(t : Γ ⊢ A)
  → Σ (Φ ⊢Nf⋆ *) λ A' → Σ (Γ ⊢ A') λ t' → Σ (Value t') λ v → stepper n p (ε ▻ t) ≡ (Φ ,, Γ ,, p ,, just (□ v)) → A ≡ A'
-}
```
