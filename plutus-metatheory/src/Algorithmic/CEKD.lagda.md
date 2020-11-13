# CEK machine that discharges builtin args

```
module Algorithmic.CEKD where

open import Data.Bool using (Bool;true;false)
open import Data.Product using (Σ;_×_;proj₁;proj₂) renaming (_,_ to _,,_)
open import Function using (_∘_;id)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;sym;trans;inspect) renaming ([_] to [[_]];subst to substEq)
import Data.List as L
open import Data.List.Properties
import Data.Sum as Sum

open import Type
open import Type.BetaNormal
open import Type.BetaNBE hiding (Env)
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Algorithmic.Reduction hiding (step)
open import Builtin
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con

Clos : ∅ ⊢Nf⋆ * → Set

data Env : Ctx ∅ → Set where
  []   : Env ∅
  _∷_ : ∀{Γ A} → Env Γ → Clos A → Env (Γ , A)

Clos A = Σ (Ctx ∅) λ Γ → Σ (Γ ⊢ A) λ M → Value M × Env Γ

lookup : ∀{Γ A} → Γ ∋ A → Env Γ → Clos A
lookup Z     (ρ ∷ c) = c
lookup (S x) (ρ ∷ c) = lookup x ρ

data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·     : ∀{Γ}{A B : ∅ ⊢Nf⋆ *} → Γ ⊢ A → Env Γ → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *} → Clos (A ⇒ B) → Frame B A
  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K) → Frame (B [ A ]Nf) (Π B)
  wrap-   : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (μ A B) (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  unwrap- : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) (μ A B)

  builtin- : (b : Builtin)
    → (σ : ∀ {K} → proj₁ (SIG b) ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (As : L.List (proj₁ (SIG b) ⊢Nf⋆ *))
    → (ts : Tel ∅ (proj₁ (SIG b)) σ As)
    → VTel ∅ (proj₁ (SIG b)) σ As ts
    → (A : (proj₁ (SIG b) ⊢Nf⋆ *))
    → (As' : L.List (proj₁ (SIG b) ⊢Nf⋆ *))
    → proj₁ (proj₂ (SIG b)) ≡ As L.++ A L.∷ As'
    → Tel ∅ (proj₁ (SIG b)) σ As'
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

dischargeTel : ∀{Γ Δ As}
    → (σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K)
    → (ts : Tel Γ Δ σ As)
    → Env Γ
    → Tel ∅ Δ σ As

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
discharge (V-pbuiltin⋆ b Φ σ p) ρ = _ ,, V-pbuiltin⋆ b Φ σ p
discharge (V-pbuiltin b σ A As' p ts) ρ =
  _ ,, V-pbuiltin b σ A As' p (dischargeTel σ ts ρ)

-- telescope rangling
vtel-lem : ∀{Φ}{Γ Δ}{As As' : L.List (Δ ⊢Nf⋆ *)} (σ : ∀{K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
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
    → (p : Bs L.++ (C L.∷ Ds) ≡ As)
    → (tel' : Tel Γ Δ σ Ds)
    → Tel Γ Δ σ As
reconstTel L.[] Ds σ telB t' refl telD = t' ∷ telD
reconstTel (B L.∷ Bs) Ds σ (X ∷ telB) t' refl tel' =
  X ∷ reconstTel Bs Ds σ telB t' refl tel'

extendVTel : ∀{Φ Γ Δ As} Bs
    → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (ts : Tel Γ Δ σ Bs)
    → VTel Γ Δ σ Bs ts 
    → ∀{C}(t' : Γ ⊢ substNf σ C)
    → Value t'
    → (p : Bs L.++ (C L.∷ L.[]) ≡ As)
    → VTel Γ Δ σ As (reconstTel Bs L.[] σ ts t' p [])

extendVTel L.[] σ [] _ t' vt' refl = vt' ,, _
extendVTel (B L.∷ Bs) σ (t ∷ ts) (v ,, vs) t' v' refl =
  v ,, extendVTel Bs σ ts vs t' v' refl
    
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
  s ; ρ ▻ BUILTIN bn σ (substEq (Tel _ _ σ) (sym p) []) (vtel-lem σ (sym p) [] _)
step (s ; ρ ▻ builtin bn σ (t ∷ ts)) | A L.∷ As | [[ p ]] =
  (s , builtin- bn σ L.[] [] _ A As p (dischargeTel σ ts ρ)) ; ρ ▻ t
step (x ; x₁ ▻ pbuiltin b Ψ' σ As' p x₂) =
  ◆ (abstractArg _ As' p (proj₂ (proj₂ (SIG b))) σ)
step (s ; ρ ▻ error A) = ◆ A
step (ε ; ρ ◅ V) = □ (_ ,, _ ,, V ,, ρ)
step ((s , -· M ρ') ; ρ ◅ V) = (s , ((_ ,, _ ,, V ,, ρ) ·-)) ; ρ' ▻ M
step ((s , ((_ ,, ƛ M ,, V-ƛ .M ,, ρ') ·-)) ; ρ ◅ V) =
  s ; ρ' ∷ (_ ,, _ ,, V ,, ρ) ▻ M
step ((s , -·⋆ A) ; ρ ◅ V-Λ M) = s ; ρ ▻ (M [ A ]⋆) 
step ((s , wrap-) ; ρ ◅ V) = s ; ρ ◅ V-wrap V
step ((s , unwrap-) ; ρ ◅ V-wrap V) = s ; ρ ◅ V
step ((s , builtin- b σ As ts vs A .L.[] p []) ; ρ ◅ V) = s ; [] ▻
  BUILTIN b
          σ
          (reconstTel As L.[] σ ts (proj₁ (discharge V ρ)) (sym p) [])
          (extendVTel As σ ts vs (proj₁ (discharge V ρ)) (proj₂ (discharge V ρ)) (sym p))
step ((s , builtin- b σ As ts vs A (A' L.∷ As') p (t' ∷ ts')) ; ρ ◅ V) =
  (s , builtin-
        b
        σ
        (As L.++ L.[ A ])
        (reconstTel As L.[] σ ts (proj₁ (discharge V ρ)) refl [])
        (extendVTel As σ ts vs (proj₁ (discharge V ρ)) (proj₂ (discharge V ρ)) refl)
        A'
        As'
        (trans p (sym (++-assoc As L.[ A ] (A' L.∷ As')))) ts')
  ; [] ▻ t'
step ((s , -·⋆ A) ; ρ ◅ V-pbuiltin⋆ b Φ σ p) =
  ◆ (abstractArg (proj₁ (proj₂ (SIG b))) _ (Sum.inj₁ (p ,, refl)) (proj₂ (proj₂ (SIG b))) (substNf-cons σ A))
step ((s , ((_ ,, _ ,, V-pbuiltin b σ A As' p ts ,, _) ·-)) ; ρ ◅ V) =
  ◆ (abstractArg (proj₁ (proj₂ (SIG b))) (A L.∷ As') (Sum.inj₂ (refl ,, p)) (proj₂ (proj₂ (SIG b))) σ)
step (□ C)       = □ C
step (◆ A)       = ◆ A

