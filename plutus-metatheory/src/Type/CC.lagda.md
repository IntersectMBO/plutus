---
title: CC machine for types
layout: page
---

```
module Type.CC where
```

## Imports

```
open import Type
open import Type.RenamingSubstitution
open import Type.ReductionC hiding (step)

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
variable I' : Kind

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

variable K' : Kind

helper⇒ : ∀(E : EvalCtx K *){B}(W : Value⋆ B){A'}(V : Value⋆ A')
  → (extendEvalCtx E (V ⇒-) ▻ B) -→s (E ◅ (V V-⇒ W))
  → proj₂ (helper V (dissect (extendEvalCtx E (-⇒ B)))) -→s
         (E ◅ (V V-⇒ W))
helper⇒ E W V x rewrite (lemma E (-⇒ discharge W)) = x

helper⇒' : ∀(E : EvalCtx K *){B}(W : Value⋆ B){A'}(V : Value⋆ A')
  → proj₂ (helper W (dissect (extendEvalCtx E (V ⇒-)))) -→s
         (E ◅ (V V-⇒ W))
helper⇒' E W V rewrite (lemma E (V ⇒-)) = base

helper⇒'' : ∀(E : EvalCtx K *) E' B{A'}(V : Value⋆ A') → 
 (extendEvalCtx E (V ⇒-) ▻ B) -→s
 (compEvalCtx' (extendEvalCtx E (V ⇒-)) E' ▻ A)
 →
 proj₂ (helper V (dissect (extendEvalCtx E (-⇒ B)))) -→s
      (compEvalCtx' (extendEvalCtx E (V ⇒-)) E' ▻ A)
helper⇒'' E E' B V x rewrite (lemma E (-⇒ B)) = x

helperμ : ∀(E : EvalCtx K _){B : ∅ ⊢⋆ J}(W : Value⋆ B){A'}(V : Value⋆ A')
  → (extendEvalCtx E (μ V -) ▻ B) -→s (E ◅ (V-μ V W))
  → proj₂ (helper V (dissect (extendEvalCtx E (μ- B)))) -→s
         (E ◅ (V-μ V W))
helperμ E W V x rewrite lemma E (μ- discharge W) = x

helperμ' : ∀(E : EvalCtx K _){B : ∅ ⊢⋆ J}(W : Value⋆ B){A'}(V : Value⋆ A')
  → proj₂ (helper W (dissect (extendEvalCtx E (μ V -)))) -→s
         (E ◅ (V-μ V W))
helperμ' E W V rewrite lemma E (μ V -) = base

helperμ'' : ∀(E : EvalCtx K _) E' (B : ∅ ⊢⋆ J){A'}(V : Value⋆ A')
  → (extendEvalCtx E (μ V -) ▻ B) -→s (compEvalCtx' (extendEvalCtx E μ V -) E' ▻ A)
  → proj₂ (helper V (dissect (extendEvalCtx E (μ- B)))) -→s
    (compEvalCtx' (extendEvalCtx E μ V -) E' ▻ A)
helperμ'' E E' B V x rewrite lemma E (μ- B) = x


-- some high level structure of the reduction to CC machine below
lemV : (A : ∅ ⊢⋆ J)(V : Value⋆ A)(E : EvalCtx K J) → (E ▻ A) -→s (E ◅ V)
lemV .(Π N) (V-Π N) E = step* refl base
lemV .(_ ⇒ _) (V V-⇒ W) E = step* refl (step** (lemV (discharge V) V (extendEvalCtx E (-⇒ discharge W))) (step* refl (helper⇒ E W V (step** (lemV (discharge W) W (extendEvalCtx E (V ⇒-))) (step* refl (helper⇒' E W V))))))
lemV .(ƛ N) (V-ƛ N) E = step* refl base
lemV .(con tcn) (V-con tcn) E = step* refl base
lemV .(μ _ _) (V-μ V W) E = step* refl (step** (lemV _ V (extendEvalCtx E (μ- discharge W))) (step* refl (helperμ E W V (step** (lemV _ W (extendEvalCtx E (μ V -))) (step* refl (helperμ' E W V))))))

helper· : ∀(E : EvalCtx K J)(E' : EvalCtx K' I) B {A' : ∅ ⊢⋆ K' ⇒ J}(V : Value⋆ A') → 
  (extendEvalCtx E (V ·-) ▻ B) -→s
  (compEvalCtx' (extendEvalCtx E (V ·-)) E' ▻ A)
   → 
  proj₂ (helper V (dissect (extendEvalCtx E (-· B)))) -→s
        (compEvalCtx' (extendEvalCtx E (V ·-)) E' ▻ A)
helper· E E' B V x rewrite lemma E (-· B) = x

lem62 : (A : ∅ ⊢⋆ I)(B : ∅ ⊢⋆ J)(E : EvalCtx K J)(E' : EvalCtx J I)
      → B ~ E' ⟦ A ⟧
      → (E ▻ B) -→s (compEvalCtx' E E' ▻ A)
lem62 A .A E [] (~[] .A) = base
lem62 A .(_ · B) E (V ·r E') (~·r .A .V B .E' x) =
  step* refl (step** (lemV _ V (extendEvalCtx E (-· B))) (step* refl (helper· E E' B V (lem62 A B (extendEvalCtx E (V ·-)) E' x) )))
lem62 A .(A₁ · x₁) E (E' l· x₁) (~l· .A A₁ .x₁ .E' x) = step* refl (lem62 A A₁ (extendEvalCtx E (-· x₁)) E' x)
lem62 A .(_ ⇒ B) E (V ⇒r E') (~⇒r .A _ .V .E' B x) = step* refl (step** (lemV _ V (extendEvalCtx E (-⇒ B))) (step* refl (helper⇒'' E E' B V (lem62 A B (extendEvalCtx E (V ⇒-)) E' x))))
lem62 A .(A₁ ⇒ x₁) E (E' l⇒ x₁) (~l⇒ .A A₁ .x₁ .E' x) = step* refl (lem62 A _ (extendEvalCtx E (-⇒ x₁)) E' x)
lem62 A .(μ _ B) E (μr x₁ E') (~μr .A _ .x₁ .E' B x) = step* refl (step** (lemV _ x₁ (extendEvalCtx E (μ- B))) (step* refl (helperμ'' E E' B x₁ (lem62 A B (extendEvalCtx E (μ x₁ -)) E' x))))
lem62 A .(μ A₁ B₁) E (μl E' B₁) (~μl .A A₁ .B₁ .E' x) = step* refl (lem62 A _ (extendEvalCtx E (μ- B₁)) E' x)

{-
lem1 : (A : ∅ ⊢⋆ J)(B : ∅ ⊢⋆ K)(E : EvalCtx K J)
       (A' : ∅ ⊢⋆ J)(B' : ∅ ⊢⋆ K)(E' : EvalCtx K J)
  → B ~ E ⟦ A ⟧ → B' ~ E' ⟦ A' ⟧ → B —→⋆ B' -> (E ▻ A) -→s (E' ▻ A')
lem1 A B E A' B' E' p q r = {!!}

unwind : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J) → A' ~ E ⟦ A ⟧ → (V : Value⋆ A') → (E ▻ A) -→s ([] ◅ V)
unwind = {!!}


-- thm2 follows from this stronger theorem
thm1 : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → A' ~ E ⟦ A ⟧ → (B : ∅ ⊢⋆ K)(V : Value⋆ B) → A' —↠⋆ B -> (E ▻ A) -→s ([] ◅ V)
thm1 A A' E p B V q = {!!}

-- this is the result we want
thm2 : (A B : ∅ ⊢⋆ K)(V : Value⋆ B) → A —↠⋆ B -> ([] ▻ A) -→s ([] ◅ V)
thm2 A B V p = thm1 A A [] (~[] A) B V p
-}
```
