---
title: CC machine for types
layout: page
---

```
module Type.CCI where
```

## Imports

```
open import Type
open import Type.RenamingSubstitution
open import Type.ReductionCI hiding (step)

open import Data.Product
```

```
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum

-- expose the bottom inner layer of the evalctx
dissect : (E : EvalCtx K J) → K ≡ J ⊎ Σ Kind λ I → EvalCtx K I × Frame I J
dissect [] = inj₁ refl
dissect (V ·r E) with dissect E 
... | inj₁ refl = inj₂ (-, [] , V ·-)
... | inj₂ (_ , E' , f) = inj₂ (-, V ·r E' , f)
dissect (E l· B) with dissect E 
... | inj₁ refl = inj₂ (-, [] , -· B)
... | inj₂ (_ , E' , f) = inj₂ (-, E' l· B , f)
dissect (V ⇒r E) with dissect E
... | inj₁ refl = inj₂ (-, [] , V ⇒-)
... | inj₂ (_ , E' , f) = inj₂ (-, V ⇒r E' , f)
dissect (E l⇒ B) with dissect E
... | inj₁ refl = inj₂ (-, [] , -⇒ B)
... | inj₂ (_ , E' , f) = inj₂ (-, E' l⇒ B , f)
dissect (μr V E) with dissect E
... | inj₁ refl         = inj₂ (-, [] , μ V -)
... | inj₂ (_ , E' , f) = inj₂ (-, μr V E' , f)
dissect (μl E B) with dissect E
... | inj₁ refl = inj₂ (-, [] , μ- B)
... | inj₂ (_ , E' , f) = inj₂ (-, μl E' B , f)


lemma : (E : EvalCtx K J)(F : Frame J I)
      → dissect (extendEvalCtx E F) ≡ inj₂ (-, E , F)
lemma [] (-· x) = refl
lemma [] (x ·-) = refl
lemma [] (-⇒ x) = refl
lemma [] (x ⇒-) = refl
lemma [] (μ- B) = refl
lemma [] μ x - = refl
lemma (x ·r E) F rewrite lemma E F = refl
lemma (E l· x) F rewrite lemma E F = refl
lemma (x ⇒r E) F rewrite lemma E F = refl
lemma (E l⇒ x) F rewrite lemma E F = refl
lemma (μr x E) F rewrite lemma E F = refl
lemma (μl E B) F rewrite lemma E F = refl
-- this reaches down inside the evaluation context and changes the
-- scope of the hole
```

```
data State (K : Kind) : Kind → Set where
  _▻_ : EvalCtx K J → ∅ ⊢⋆ J → State K J
  _◅_ : EvalCtx K J  → {A : ∅ ⊢⋆ J} → Value⋆ A → State K J
  □   : {A : ∅ ⊢⋆ K} →  Value⋆ A → State K K
```

```
closeState : State K J → ∅ ⊢⋆ K
closeState (E ▻ A) = closeEvalCtx E A
closeState (E ◅ V) = closeEvalCtx E (discharge V)
closeState (□ A)   = discharge A
```


## The machine

The `step` function performs one step of computation. It takes a state
and return a new state. The kind index `K` refers to the kind of the
outer type which is preserved. The second index `J/J'` refers to the
kind of the subtype in focus which may change.

```
helper : {A : ∅ ⊢⋆ J}(V : Value⋆ A)
       → K ≡ J ⊎ Σ Kind (λ I → EvalCtx K I × Frame I J)
       → ∃ (State K)
helper V (inj₁ refl) = -, □ V
helper V (inj₂ (_ , E' , -· B)) = -, extendEvalCtx E' (V ·-)  ▻ B
helper V (inj₂ (_ , E' , (V-ƛ N ·-))) = -, E' ▻ (N [ discharge V ])
helper V (inj₂ (_ , E' , -⇒ B)) = -, extendEvalCtx E' (V ⇒-)  ▻ B
helper V (inj₂ (_ , E' , W ⇒-)) = -, E' ◅ (W V-⇒ V)
helper V (inj₂ (_ , E' , μ- B)) = -, extendEvalCtx E' (μ V -) ▻ B
helper V (inj₂ (_ , E' , μ W -)) = -, E' ◅ V-μ W V

step : State K J → ∃ λ J' → State K J'
step (E ▻ Π A)                      = -, E ◅ V-Π A
step (E ▻ (A ⇒ B))                  = -, compEvalCtx' E ([] l⇒ B)  ▻ A
step (E ▻ ƛ A)                      = -, E ◅ V-ƛ A
step (E ▻ (A · B))                  = -, compEvalCtx' E ([] l· B) ▻ A
step (E ▻ μ A B)                    = -, compEvalCtx' E (μl [] B) ▻ A
step (E ▻ con c)                    = -, E ◅ V-con c
step (□ V)                          = -, □ V
-- v we look at the E to decide what to do...
step (E ◅ V) = helper V (dissect E)
```

```
variable I' J' K' : Kind

data _-→s_ : State K J → State K I → Set where
  base  : {s : State K J}
        → s -→s s
  step* : {s : State K J}{s' : State K I}{s'' : State K I'}
        → step s ≡ (I , s')
        → s' -→s s''
        → s -→s s''

step** : {s : State K J}{s' : State K I}{s'' : State K I'}
        → s -→s s'
        → s' -→s s''
        → s -→s s''
step** base q = q
step** (step* x p) q = step* x (step** p q)

subst-step* : {s : State K J}{s' : State K J'}{s'' : State K I}
        → _≡_ {A = Σ Kind (State K)} (J , s) (J' , s')
        → s' -→s s''
        → s -→s s''
subst-step* refl q = q

helper·-lem : ∀(E : EvalCtx K J)(E' : EvalCtx K' I) B {A' : ∅ ⊢⋆ K' ⇒ J}(V : Value⋆ A') → 
   helper V (dissect (extendEvalCtx E (-· B))) ≡ (K' , extendEvalCtx E (V ·-) ▻ B)
helper·-lem E E' B V rewrite lemma E (-· B) = refl

helper⇒r-lem : ∀(E : EvalCtx K *){B}(W : Value⋆ B){A'}(V : Value⋆ A') →
   helper W (dissect (extendEvalCtx E (V ⇒-))) ≡ (* , E ◅ (V V-⇒ W))
helper⇒r-lem E W V rewrite lemma E (V ⇒-) = refl

helper⇒l-lem : ∀(E : EvalCtx K *) B {A'}(V : Value⋆ A') →
   helper V (dissect (extendEvalCtx E (-⇒ B))) ≡ (* , extendEvalCtx E (V ⇒-) ▻ B)
helper⇒l-lem E B V rewrite lemma E (-⇒ B) = refl

helperμl-lem : ∀(E : EvalCtx K _)(B : ∅ ⊢⋆ J){A'}(V : Value⋆ A')
  → helper V (dissect (extendEvalCtx E (μ- B))) ≡ (_ , extendEvalCtx E (μ V -) ▻ B)
helperμl-lem E B V rewrite lemma E (μ- B) = refl

helperμr-lem : ∀(E : EvalCtx K _){B : ∅ ⊢⋆ J}(W : Value⋆ B){A'}(V : Value⋆ A')
  → helper W (dissect (extendEvalCtx E (μ V -))) ≡ (* , E ◅ V-μ V W)
helperμr-lem E W V rewrite lemma E (μ V -) = refl

-- some high level structure of the reduction to CC machine below
lemV : (A : ∅ ⊢⋆ J)(V : Value⋆ A)(E : EvalCtx K J) → (E ▻ A) -→s (E ◅ V)
lemV .(Π N) (V-Π N) E = step* refl base
lemV .(_ ⇒ _) (V V-⇒ W) E = step*
  refl
  (step** (lemV (discharge V) V (extendEvalCtx E (-⇒ discharge W)))
          (step* refl
                 (subst-step* (helper⇒l-lem E (discharge W) V)
                              (step** (lemV (discharge W) W (extendEvalCtx E (V ⇒-)))
                                      (step* refl (subst-step* ( helper⇒r-lem E W V) base))))))
lemV .(ƛ N) (V-ƛ N) E = step* refl base
lemV .(con tcn) (V-con tcn) E = step* refl base
lemV .(μ _ _) (V-μ V W) E = step*
  refl
  (step** (lemV _ V (extendEvalCtx E (μ- discharge W)))
          (step* refl
                 (subst-step* (helperμl-lem E (discharge W) V)
                              (step** (lemV _ W (extendEvalCtx E (μ V -)))
                                      (step* refl (subst-step* ( helperμr-lem E W V) base))))))

lem62 : (A : ∅ ⊢⋆ I)(B : ∅ ⊢⋆ J)(E : EvalCtx K J)(E' : EvalCtx J I)
      → B ~  E' ⟦ A ⟧
      → (E ▻ B) -→s (compEvalCtx' E E' ▻ A)
lem62 A .A E [] (~[] .A) = base
lem62 A .(_ · B) E (V ·r E') (~·r .A .V B .E' x) = step*
  refl
  (step** (lemV _ V (extendEvalCtx E (-· B)))
          (step* refl
                 (subst-step* (helper·-lem E E' B V)
                              (lem62 A B (extendEvalCtx E (V ·-)) E' x))))
lem62 A .(A₁ · x₁) E (E' l· x₁) (~l· .A A₁ .x₁ .E' x) = step*
  refl
  (lem62 A A₁ (extendEvalCtx E (-· x₁)) E' x)
lem62 A .(_ ⇒ B) E (V ⇒r E') (~⇒r .A _ .V .E' B x) = step*
  refl
  (step** (lemV _ V (extendEvalCtx E (-⇒ B)))
          (step* refl
                 (subst-step* (helper⇒l-lem E B V)
                              (lem62 A B (extendEvalCtx E (V ⇒-)) E' x))))
lem62 A .(A₁ ⇒ x₁) E (E' l⇒ x₁) (~l⇒ .A A₁ .x₁ .E' x) = step*
  refl
  (lem62 A _ (extendEvalCtx E (-⇒ x₁)) E' x)
lem62 A .(μ _ B) E (μr x₁ E') (~μr .A _ .x₁ .E' B x) = step*
  refl
  (step** (lemV _ x₁ (extendEvalCtx E (μ- B)))
          (step* refl
                 (subst-step* (helperμl-lem E B x₁)
                              (lem62 A B (extendEvalCtx E (μ x₁ -)) E' x))))
lem62 A .(μ A₁ B₁) E (μl E' B₁) (~μl .A A₁ .B₁ .E' x) = step*
  refl
  (lem62 A _ (extendEvalCtx E (μ- B₁)) E' x)

{-
lem1 : (M : ∅ ⊢⋆ J)(B B' : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → B ~ E ⟦ M ⟧ → B —→⋆ B'
  → Σ Kind λ J' → Σ (∅ ⊢⋆ J') λ N → Σ (EvalCtx K J') λ E'
  → B' ~ E' ⟦ N ⟧ × (E ▻ M) -→s (E' ▻ N)
  × Σ (∅ ⊢⋆ J') λ L →  (B ~ E' ⟦ L ⟧) × (L —→⋆ N)
lem1 M B B' p = {!!}

unwind : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J) → A' ≡ closeEvalCtx E A → (V : Value⋆ A') → (E ▻ A) -→s ([] ◅ V)
unwind = {!!}

-- thm2 follows from this stronger theorem
thm1 : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → A' ≡ closeEvalCtx E A → (B : ∅ ⊢⋆ K)(V : Value⋆ B) → A' —↠⋆ B -> (E ▻ A) -→s ([] ◅ V)
thm1 A A' E p .A' V refl—↠⋆ = unwind A A' E p V
thm1 A A' E p B V (trans—↠⋆ {B = B'} q r) with lemma51 B'
... | inj₂ (J , E' , I , L , N , VL , VN , X) = step** {!!} (thm1 (L · N) B' E' X B V r)

... | inj₁ V' with v-refl B' B V' r
... | refl , refl = step** {!!} (unwind {!!} {!!} {!!} {!!} V)

-- this is the result we want
thm2 : (A B : ∅ ⊢⋆ K)(V : Value⋆ B) → A —↠⋆ B -> ([] ▻ A) -→s ([] ◅ V)
thm2 A B V p = thm1 A A [] refl B V p
-}
```
