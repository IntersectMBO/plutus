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
open import Relation.Binary.PropositionalEquality renaming ([_] to I[_])
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


helper·r-lem : ∀(E : EvalCtx K J) B {A : ∅ ,⋆ K' ⊢⋆ J}(V : Value⋆ B) → 
  helper V (dissect (extendEvalCtx E (V-ƛ A ·-))) ≡ (J , E ▻ (A [ B ]))
helper·r-lem E B {A} V rewrite lemma E (V-ƛ A ·-) = refl


helper·l-lem : ∀(E : EvalCtx K J) B {A' : ∅ ⊢⋆ K' ⇒ J}(V : Value⋆ A') → 
   helper V (dissect (extendEvalCtx E (-· B))) ≡ (K' , extendEvalCtx E (V ·-) ▻ B)
helper·l-lem E B V rewrite lemma E (-· B) = refl

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
      → B ≡ closeEvalCtx E' A
      → (E ▻ B) -→s (compEvalCtx' E E' ▻ A)
lem62 A .A E [] refl = base
lem62 A .(_ · closeEvalCtx E' A) E (V ·r E') refl = step*
  refl
  (step**
    (lemV _ V (extendEvalCtx E (-· closeEvalCtx E' A)))
    (step*
      refl
      (subst-step*
        (helper·l-lem E (closeEvalCtx E' A) V)
        (lem62 A (closeEvalCtx E' A) (extendEvalCtx E (V ·-)) E' refl))))
lem62 A .(closeEvalCtx E' A · C) E (E' l· C) refl = step*
  refl
  (lem62 A (closeEvalCtx E' A) (extendEvalCtx E (-· C)) E' refl)
lem62 A .(_ ⇒ closeEvalCtx E' A) E (V ⇒r E') refl = step*
  refl
  (step**
    (lemV _ V (extendEvalCtx E (-⇒ closeEvalCtx E' A)))
    (step*
      refl
      (subst-step* (helper⇒l-lem E _ V)
                   (lem62 A _ (extendEvalCtx E (V ⇒-)) E' refl))))
lem62 A B E (E' l⇒ C) refl = step*
  refl
  (lem62 A _ (extendEvalCtx E (-⇒ C)) E' refl)
lem62 A B E (μr V E') refl = step*
  refl
  (step**
    (lemV _ V (extendEvalCtx E (μ- _)))
    (step*
      refl
      (subst-step*
        (helperμl-lem E _ V)
        (lem62 A _ (extendEvalCtx E (μ V -)) E' refl))))
lem62 A B E (μl E' C) refl = step*
  refl
  (lem62 A _ (extendEvalCtx E (μ- C)) E' refl)

lem1 : (M : ∅ ⊢⋆ J)(B B' : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → B ≡ closeEvalCtx E M
  → B —→E B'
  → Σ Kind λ J'
  → Σ (∅ ⊢⋆ J') λ N
  → Σ (EvalCtx K J') λ E'
  → B' ≡ closeEvalCtx E' N
  × (E ▻ M) -→s (E' ▻ N)
  × Σ (∅ ⊢⋆ J') λ L
  → (B ≡ closeEvalCtx E' L)
  × (L —→E N)
lem1 M B B' p = {!!}

-- this is a really a view or case analysis principle
-- "there are only 4 possibilities"
lem2 : (M : ∅ ⊢⋆ J)(B : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → (N : ∅ ⊢⋆ J')(B' : ∅ ⊢⋆ K)(E' : EvalCtx K J')
  → B ≡ closeEvalCtx E M
  → B' ≡ closeEvalCtx E' N
  → B —→E B'
  → Σ (∅ ⊢⋆ J') λ L → (B ≡ closeEvalCtx E' L)
  × (L —→⋆ N) × 
  ((Σ (EvalCtx J J') λ E'' → M ≡ closeEvalCtx E'' L)
  ⊎ Value⋆ M × Σ (Frame J' J) λ F → E ≡ extendEvalCtx E' F)
lem2 M B E N B' E' p q r = {!!}

lem-→⋆ : (A B : ∅ ⊢⋆ J)(E : EvalCtx K J) → A —→⋆ B → (E ▻ A) -→s (E ▻ B)
lem-→⋆ (ƛ A · B) ._ E (β-ƛ V) = step* refl (step* refl (step* (helper·l-lem E B (V-ƛ A) ) (step** (lemV B V (extendEvalCtx E (V-ƛ A ·-))) (step* (helper·r-lem E B V) base))))

unwind : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J) → A' ≡ closeEvalCtx E A → (V : Value⋆ A') → (E ▻ A) -→s ([] ◅ V)
unwind = {!!}

β-lem : A ≡ ƛ A' · B' → A —→⋆ B → B ≡ A' [ B' ]
β-lem refl (β-ƛ x) = refl

-- thm2 follows from this stronger theorem
thm1 : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → A' ≡ closeEvalCtx E A → (B : ∅ ⊢⋆ K)(V : Value⋆ B) → A' —↠E B -> (E ▻ A) -→s ([] ◅ V)
thm1 A A' E p .A' V refl—↠E = unwind A A' E p V
thm1 A A' E p B V (trans—↠E {B = B'} q r) with lemma51 B'
... | inj₁ V' with v-refl B' B V' r
... | refl = {!V!}
thm1 A A' E p B V (trans—↠E {B = B'} q r)
  | inj₂ (J , E' , I , L , N , VL , VN , X)
  with lem2 A A' E (L · N) B' E' p X q
... | L' , p' , XX , inj₁ (E'' , p'') = step**
  (step** (lem62 L' A E E'' p'')
          (subst-step* (cong (λ E → J , E ▻ L')
                       (sym (uniquenessE
                         A'
                         (λ V → notboth A' (V , _ , q))
                         L'
                         E'
                         (compEvalCtx' E E'')
                         p'
                         (trans
                           p
                           (trans (cong (closeEvalCtx E) p'')
                                  (trans (sym (close-comp E E'' L'))
                                         (cong (λ E → closeEvalCtx E L')
                                               (compEvalCtx-eq E E''))))))))
                       (lem-→⋆ _ _ E' XX)))
  (thm1 (L · N) B' E' X B V r)
... | L' , p' , XX , inj₂ (VA , (-· x) , snd) = {!!}
... | L' , p' , XX , inj₂ (VA , (V-ƛ N₁ ·-) , refl) = step**
  (step** (lemV A VA _)
          (step* (cong (helper VA) (lemma E' (V-ƛ N₁ ·-)))
                 (subst-step* (cong (λ A → J , E' ▻ A) (sym (β-lem ZZ XX)))
                              base)))
  (thm1 (L · N) B' E' X B V r)
  where
  YY : A' ≡ closeEvalCtx E' (ƛ N₁ · A)
  YY = trans p (closeEF E' (V-ƛ N₁ ·-) A)
  ZZ : L' ≡ ƛ N₁ · A
  ZZ = uniqueness⋆ L' (ƛ N₁ · A) E' (trans (sym p') YY)
... | L' , p' , XX , inj₂ (VA , (-⇒ x) , snd) = {!!}
... | L' , p' , XX , inj₂ (VA , (x ⇒-) , snd) = {!!}
... | L' , p' , XX , inj₂ (VA , (μ- B₁) , snd) = {!!}
... | L' , p' , XX , inj₂ (VA , μ x - , snd) = {!!}

-- step** (lemV A VA E)
--  = step** {!lem2 A A' E (L · N) B' E' p X q!} (thm1 (L · N) B' E' X B V r)
-- we have E [ A ] -> E [ L . N ]
-- then r is reflexivity but we still have one step which goes to a value
-- this is the result we want
thm2 : (A B : ∅ ⊢⋆ K)(V : Value⋆ B) → A —↠E B -> ([] ▻ A) -→s ([] ◅ V)
thm2 A B V p = thm1 A A [] refl B V p
```
