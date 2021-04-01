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

lemma' : (E : EvalCtx K J)(F : Frame J I)
      → dissect' (extendEvalCtx E F) ≡ inj₂ (-, E , F)
lemma' [] (-· x) = refl
lemma' [] (x ·-) = refl
lemma' [] (-⇒ x) = refl
lemma' [] (x ⇒-) = refl
lemma' [] (μ- B) = refl
lemma' [] μ x - = refl
lemma' (x ·r E) F rewrite lemma' E F = refl
lemma' (E l· x) F rewrite lemma' E F = refl
lemma' (x ⇒r E) F rewrite lemma' E F = refl
lemma' (E l⇒ x) F rewrite lemma' E F = refl
lemma' (μr x E) F rewrite lemma' E F = refl
lemma' (μl E B) F rewrite lemma' E F = refl

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
stepV : {A : ∅ ⊢⋆ J}(V : Value⋆ A)
       → K ≡ J ⊎ Σ Kind (λ I → EvalCtx K I × Frame I J)
       → ∃ (State K)
stepV V (inj₁ refl) = -, □ V
stepV V (inj₂ (_ , E' , -· B)) = -, extendEvalCtx E' (V ·-)  ▻ B
stepV V (inj₂ (_ , E' , (V-ƛ N ·-))) = -, E' ▻ (N [ discharge V ])
stepV V (inj₂ (_ , E' , -⇒ B)) = -, extendEvalCtx E' (V ⇒-)  ▻ B
stepV V (inj₂ (_ , E' , W ⇒-)) = -, E' ◅ (W V-⇒ V)
stepV V (inj₂ (_ , E' , μ- B)) = -, extendEvalCtx E' (μ V -) ▻ B
stepV V (inj₂ (_ , E' , μ W -)) = -, E' ◅ V-μ W V

step : State K J → ∃ λ J' → State K J'
step (E ▻ Π A)                      = -, E ◅ V-Π A
step (E ▻ (A ⇒ B))                  = -, compEvalCtx' E ([] l⇒ B)  ▻ A
step (E ▻ ƛ A)                      = -, E ◅ V-ƛ A
step (E ▻ (A · B))                  = -, compEvalCtx' E ([] l· B) ▻ A
step (E ▻ μ A B)                    = -, compEvalCtx' E (μl [] B) ▻ A
step (E ▻ con c)                    = -, E ◅ V-con c
step (□ V)                          = -, □ V
-- v we look at the E to decide what to do...
step (E ◅ V) = stepV V (dissect E)
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


stepV·r-lem : ∀(E : EvalCtx K J) B {A : ∅ ,⋆ K' ⊢⋆ J}(V : Value⋆ B) → 
  stepV V (dissect (extendEvalCtx E (V-ƛ A ·-))) ≡ (J , E ▻ (A [ B ]))
stepV·r-lem E B {A} V rewrite lemma E (V-ƛ A ·-) = refl


stepV·l-lem : ∀(E : EvalCtx K J) B {A' : ∅ ⊢⋆ K' ⇒ J}(V : Value⋆ A') → 
   stepV V (dissect (extendEvalCtx E (-· B))) ≡ (K' , extendEvalCtx E (V ·-) ▻ B)
stepV·l-lem E B V rewrite lemma E (-· B) = refl

stepV⇒r-lem : ∀(E : EvalCtx K *){B}(W : Value⋆ B){A'}(V : Value⋆ A') →
   stepV W (dissect (extendEvalCtx E (V ⇒-))) ≡ (* , E ◅ (V V-⇒ W))
stepV⇒r-lem E W V rewrite lemma E (V ⇒-) = refl

stepV⇒l-lem : ∀(E : EvalCtx K *) B {A'}(V : Value⋆ A') →
   stepV V (dissect (extendEvalCtx E (-⇒ B))) ≡ (* , extendEvalCtx E (V ⇒-) ▻ B)
stepV⇒l-lem E B V rewrite lemma E (-⇒ B) = refl

stepVμl-lem : ∀(E : EvalCtx K _)(B : ∅ ⊢⋆ J){A'}(V : Value⋆ A')
  → stepV V (dissect (extendEvalCtx E (μ- B))) ≡ (_ , extendEvalCtx E (μ V -) ▻ B)
stepVμl-lem E B V rewrite lemma E (μ- B) = refl

stepVμr-lem : ∀(E : EvalCtx K _){B : ∅ ⊢⋆ J}(W : Value⋆ B){A'}(V : Value⋆ A')
  → stepV W (dissect (extendEvalCtx E (μ V -))) ≡ (* , E ◅ V-μ V W)
stepVμr-lem E W V rewrite lemma E (μ V -) = refl

-- some high level structure of the reduction to CC machine below
lemV : (A : ∅ ⊢⋆ J)(V : Value⋆ A)(E : EvalCtx K J) → (E ▻ A) -→s (E ◅ V)
lemV .(Π N) (V-Π N) E = step* refl base
lemV .(_ ⇒ _) (V V-⇒ W) E = step*
  refl
  (step** (lemV (discharge V) V (extendEvalCtx E (-⇒ discharge W)))
          (step* refl
                 (subst-step* (stepV⇒l-lem E (discharge W) V)
                              (step** (lemV (discharge W) W (extendEvalCtx E (V ⇒-)))
                                      (step* refl (subst-step* ( stepV⇒r-lem E W V) base))))))
lemV .(ƛ N) (V-ƛ N) E = step* refl base
lemV .(con tcn) (V-con tcn) E = step* refl base
lemV .(μ _ _) (V-μ V W) E = step*
  refl
  (step** (lemV _ V (extendEvalCtx E (μ- discharge W)))
          (step* refl
                 (subst-step* (stepVμl-lem E (discharge W) V)
                              (step** (lemV _ W (extendEvalCtx E (μ V -)))
                                      (step* refl (subst-step* ( stepVμr-lem E W V) base))))))

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
        (stepV·l-lem E (closeEvalCtx E' A) V)
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
      (subst-step* (stepV⇒l-lem E _ V)
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
        (stepVμl-lem E _ V)
        (lem62 A _ (extendEvalCtx E (μ V -)) E' refl))))
lem62 A B E (μl E' C) refl = step*
  refl
  (lem62 A _ (extendEvalCtx E (μ- C)) E' refl)


-- this is like a weakening of the environment
lem-→⋆ : (A B : ∅ ⊢⋆ J)(E : EvalCtx K J) → A —→⋆ B → (E ▻ A) -→s (E ▻ B)
lem-→⋆ (ƛ A · B) ._ E (β-ƛ V) = step* refl (step* refl (step* (stepV·l-lem E B (V-ƛ A) ) (step** (lemV B V (extendEvalCtx E (V-ƛ A ·-))) (step* (stepV·r-lem E B V) base))))

open import Data.Empty

-- I think this would be structurally recurisve on the depth of the
-- EvalCtx. dissect (which rips out the inner frame) reduces this by
-- one every time. The termination checker cannot see that the call to
-- dissect returns an E' that is smaller than E.

{-# TERMINATING #-}
unwindV : (A : ∅ ⊢⋆ J)(VA : Value⋆ A)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → A' ≡ closeEvalCtx E A → (V : Value⋆ A') → (E ◅ VA) -→s ([] ◅ V)
unwindV A VA A' E p V with dissect' E | inspect dissect' E
unwindV A VA A' E refl V | inj₁ (refl , refl) | I[ eq ]
  rewrite val-unique VA V
  = base 
unwindV A VA A' E p V | inj₂ (I , E'  , (-· B)) | I[ eq ]
  rewrite dissect-lemma E E' (-· B) eq
  = ⊥-elim (lemV· (lem0 _ E' (subst Value⋆ (trans p (closeEF E' (-· B) A)) V)))
... | inj₂ (I , E'  , (W ·-)) | I[ eq ]
  rewrite dissect-lemma E E' (W ·-) eq
  = ⊥-elim (lemV· (lem0 _ E' (subst Value⋆ (trans p (closeEF E' (W ·-) A)) V)))
... | inj₂ (.* , E' , (-⇒ B)) | I[ eq ]
  rewrite dissect-lemma E E' (-⇒ B) eq with decVal B
... | inj₁ VB  = step*
  (cong (stepV VA) (lemma E' (-⇒ B)))
  (step**
    (lemV B VB (extendEvalCtx E' (VA ⇒-)))
    (step*
      (cong (stepV VB) (lemma E' (VA ⇒-)))
      (unwindV _ (VA V-⇒ VB) A' E' (trans p (closeEF E' (-⇒ B) A)) V)))
... | inj₂ ¬VB = ⊥-elim (¬VB VB)
  where X : A' ≡ closeEvalCtx (extendEvalCtx E' (VA ⇒-)) B
        X = trans (trans p (closeEF E' (-⇒ B) A)) (sym (closeEF E' (VA ⇒-) B))
        VB : Value⋆ B
        VB = lem0 B (extendEvalCtx E' (VA ⇒-)) (subst Value⋆ X V)
unwindV A VA A' E p V | inj₂ (.* , E' , (W ⇒-)) | I[ eq ]
  rewrite dissect-lemma E E' (W ⇒-) eq = step*
  (cong (stepV VA) (lemma E' (W ⇒-)))
  (unwindV _ (W V-⇒ VA) A' E' (trans p (closeEF E' (W ⇒-) A)) V)
unwindV A VA A' E p V | inj₂ (.* , E' , (μ- B)) | I[ eq ]
  rewrite dissect-lemma E E' (μ- B) eq with decVal B
... | inj₁ VB  = step*
  (cong (stepV VA) (lemma E' (μ- B)))
  (step**
    (lemV B VB _)
    (step* (cong (stepV VB) (lemma E' (μ VA -)))
    (unwindV _ (V-μ VA VB) A' E' (trans p (closeEF E' (μ- B) A)) V)))
... | inj₂ ¬VB = ⊥-elim (¬VB VB)
  where X : A' ≡ closeEvalCtx (extendEvalCtx E' (μ VA -)) B
        X = trans (trans p (closeEF E' (μ- B) A)) (sym (closeEF E' (μ VA -) B))
        VB : Value⋆ B
        VB = lem0 B (extendEvalCtx E' (μ VA -)) (subst Value⋆ X V)

unwindV A VA A' E p V | inj₂ (.* , E' , μ W -) | I[ eq ]
  rewrite dissect-lemma E E' (μ W -) eq
  = step* (cong (stepV VA) (lemma E' (μ W -)))
          (unwindV _ (V-μ W VA) A' E' (trans p (closeEF E' (μ W -) A)) V)

unwind : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J) → A' ≡ closeEvalCtx E A → (V : Value⋆ A') → (E ▻ A) -→s ([] ◅ V)
unwind A A' E p VA' = step** (lemV A VA E) (unwindV A VA A' E p VA')
  where VA = lem0 A E (subst Value⋆ p VA')

-- this is a counterpart to lem62 and a stronger version of unwind
-- I expect the proof would be similar to that of unwind
postulate
  unwindE : (A : ∅ ⊢⋆ I)(B : ∅ ⊢⋆ J)(E : EvalCtx K J)(E' : EvalCtx J I)
      → B ≡ closeEvalCtx E' A
      → Value⋆ B
      → (compEvalCtx' E E' ▻ A) -→s (E ▻ B) 

β-lem : A ≡ ƛ A' · B' → A —→⋆ B → B ≡ A' [ B' ]
β-lem refl (β-ƛ x) = refl

-- this case doesn't arise in STLC it only arises in types due to the composite values of => and mu.
-- it is currently not proven, it is just postulated (assumed)
postulate
 missing-case : ∀ (M : ∅ ⊢⋆ J)(E : EvalCtx K J)(E' : EvalCtx K J')
  (L : ∅ ⊢⋆ I ⇒ J') N
  → (VM : Value⋆ M) → (VL : Value⋆ L) → Value⋆ N
  → closeEvalCtx E M ≡ closeEvalCtx E' (L · N)
  → ∀{J''}(E'' : EvalCtx K J'') F
  → extendEvalCtx E'' F ≡ E
  → Value⋆ (closeFrame F M)
  → (E ▻ M) -→s (E' ▻ (L · N))

-- thm2 follows from this stronger theorem

thm1 : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → A' ≡ closeEvalCtx E A → (B : ∅ ⊢⋆ K)(V : Value⋆ B) → A' —↠E B -> (E ▻ A) -→s ([] ◅ V)
thm1 M A E p .A V refl—↠E = unwind M A E p V
thm1 M A E refl B V (trans—↠E {B = B'} q q') with lemmaE' M E B' q
... | J' , E' , L , N , r , r' , r'' , inj₁ (E'' , refl) =
  step**
   ((step** (lem62 L M E E'' refl)
          (subst-step* (cong (λ E → J' , E ▻ L)
                       ((sym (uniquenessE
                         (closeEvalCtx E M)
                         (λ V → notboth (closeEvalCtx E M) (V , _ , q))
                         L
                         N
                         r
                         E'
                         (compEvalCtx' E E'')
                         r'
                         (trans
                           refl
                           (trans (cong (closeEvalCtx E) refl)
                                  (trans (sym (close-comp E E'' L))
                                         (cong (λ E → closeEvalCtx E L)
                                               (compEvalCtx-eq E E'')))))))))
                       (lem-→⋆ _ _ E' r))))
   (thm1 N B' E' (sym r'') B V q')
... | J' , E' , L , N , r , r' , r'' , inj₂ VM with lemmaE-51 L N r
... | I , _ , N' , V-ƛ L' , VN' , refl with lemmaX M E E' _ N' VM (V-ƛ L') VN' r'
... | inj₁ (refl , refl) = step**
  (step** (lemV M VM E) (step* (cong (stepV VM) (lemma E' (V-ƛ L' ·-)))
          (subst-step* (cong (λ A → J' , E' ▻ A)
                             (sym (β-lem (uniqueness⋆ (ƛ L' · N')
                                                      (ƛ L' · M)
                                                      E'
                                                      (trans (sym r')
                                                             (closeEF E' _ M)))
                                         r)))
                       base)))
  (thm1 N B' E' (sym r'') B V q')
thm1 M A E refl B V (trans—↠E {B = B'} q q') | J' , E' , L , N , r , r' , r'' , inj₂ VM | I , _ , N' , V-ƛ L' , VN' , refl | inj₂ (inj₁ (refl , refl)) with uniqueness⋆ _ _ E' (trans (sym (closeEF E' (-· N') M)) r')
... | refl = step**
  (step*
    refl
    (step*
      (cong (stepV (V-ƛ L')) (lemma E' (-· N')))
      (step**
        (lemV N' VN' (extendEvalCtx E' (V-ƛ L' ·-)))
        (step*
          (cong (stepV VN') (lemma E' (V-ƛ L' ·-)))
          (subst-step* (cong (λ A → J' , E' ▻ A) (sym (β-lem refl r))) base)))))
  (thm1 N B' E' (sym r'') B V q')
thm1 M .(closeEvalCtx E M) E refl B V (trans—↠E {B = B'} q q') | J' , E' , .(ƛ _ · N') , N , r , r' , r'' , inj₂ VM | I , ƛ L' , N' , V-ƛ L' , VN' , refl | inj₂ (inj₂ (inj₁ (I' , I'' , refl , E'' , E''' , p , refl))) = step**
  (step**
    (lemV M VM _)
    (step*
      (cong (stepV VM) (lemma E'' _))
      (step**
        (lem62 (ƛ L' · N') _ (extendEvalCtx E'' (VM ·-)) E''' refl)
        (step*
          refl
          (step*
            refl
            (step*
              (cong
                (stepV (V-ƛ L'))
                (lemma (compEvalCtx' (extendEvalCtx E'' (VM ·-)) E''') (-· N')))
              (step**
                (lemV N' VN' _)
                (step*
                  (cong
                    (stepV VN')
                    (lemma
                      (compEvalCtx' (extendEvalCtx E'' (VM ·-)) E''')
                      (V-ƛ L' ·-)))
                  (subst-step*
                    (cong₂ (λ E A → J' , (E ▻ A)) (trans (sym (compEvalCtx-eq _ E''')) (sym p)) (sym (β-lem refl r)))
                    base)))))))))
  (thm1 N B' E' (sym r'') B V q')
thm1 M .(closeEvalCtx E M) E refl B V (trans—↠E {B = B'} q q') | J' , E' , .(ƛ _ · N') , N , r , r' , r'' , inj₂ VM | I , ƛ L' , N' , V-ƛ L' , VN' , refl | inj₂ (inj₂ (inj₂ (inj₁ (refl , E'' , E''' , p , refl)))) = step**
  (lemV M VM E)
  (step*
    (cong (stepV VM) (lemma E'' _))
    (step**
      (lem62 (ƛ L' · N') _ (extendEvalCtx E'' (VM ⇒-)) E''' refl)
      (subst-step*
        (cong (λ E → _ , (E ▻ _))
              (trans (sym (compEvalCtx-eq _ E''')) (compEF E'' (VM ⇒-) E''')))
        (step*
          refl
          (step*
            refl
            (step*
              (cong (stepV (V-ƛ L'))
                    (lemma (compEvalCtx E'' (VM ⇒r E''')) (-· N')))
              (step**
                (lemV N' VN' _)
                (step*
                  (cong
                    (stepV VN')
                    (lemma (compEvalCtx E'' (VM ⇒r E''')) (V-ƛ L' ·-)))
                  (subst-step*
                    (cong₂ (λ E A → J' , E ▻ A)
                           (trans (sym (compEF E'' (VM ⇒-) E''')) (sym p))
                                  (sym (β-lem refl r)))
                    (thm1 N B' E' (sym r'') B V q'))))))))))
thm1 M .(closeEvalCtx E M) E refl B V (trans—↠E {B = B'} q q') | J' , E' , .(ƛ _ · N') , N , r , r' , r'' , inj₂ VM | I , ƛ _ , N' , V-ƛ L' , VN' , refl | inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (I' , refl , E'' , E''' , p , refl))))) = step**
  (step**
    (lemV M VM _)
    (step*
      (cong (stepV VM) (lemma E'' (μ- closeEvalCtx E''' (ƛ L' · N'))))
      (step**
        (lem62 (ƛ L' · N') _ (extendEvalCtx E'' (μ VM -)) E''' refl)
        (step*
          refl
          (step*
            refl
            (step*
              (cong
                (stepV (V-ƛ L'))
                (lemma (compEvalCtx' (extendEvalCtx E'' (μ VM -)) E''')
                       (-· N')))
              (step**
                (lemV N' VN' _)
                (step*
                  (cong
                    (stepV VN')
                    (lemma (compEvalCtx' (extendEvalCtx E'' (μ VM -)) E''')
                           (V-ƛ L' ·-)))
                  (subst-step*
                    (cong₂ (λ E A → J' , (E ▻ A))
                           (trans
                             (sym (compEvalCtx-eq _ E''')) (sym p))
                             (sym (β-lem refl r)))
                    base)))))))))
  (thm1 N B' E' (sym r'') B V q')
thm1 M A E refl B V (trans—↠E {B = B'} q q') | J' , E' , L , N , r , r' , r'' , inj₂ VM | I , _ , N' , V-ƛ L' , VN' , refl | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (I' , F , E'' , p' , VF))))) = step**
  (step**
    (missing-case M E E' (ƛ L') N' VM (V-ƛ L') VN' r' E'' F (sym p') VF)
    (step*
      refl
      (step*
        refl
        (step*
          (cong (stepV (V-ƛ L')) (lemma E' (-· N')))
          (step**
            (lemV N' VN' _)
            (step*
              (cong (stepV VN') (lemma E' (V-ƛ L' ·-)))
              (subst-step* (cong (λ N → J' , E' ▻ N) (sym (β-lem refl r))) base)))))))
  (thm1 N B' E' (sym r'') B V q')
  
thm2 : (A B : ∅ ⊢⋆ K)(V : Value⋆ B) → A —↠E B -> ([] ▻ A) -→s ([] ◅ V)
thm2 A B V p = thm1 A A [] refl B V p
```
