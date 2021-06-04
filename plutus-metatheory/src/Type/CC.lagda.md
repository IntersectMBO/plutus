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
```

```
open import Data.Product
open import Data.Empty
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
       → (K ≡ J) ⊎ Σ Kind (λ I → EvalCtx K I × Frame I J)
       → ∃ (State K)
stepV V (inj₁ refl) = -, [] ◅ V
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

-- I think this would be structurally recurisve on the depth of the
-- EvalCtx. dissect (which rips out the inner frame) reduces this by
-- one every time. The termination checker cannot see that the call to
-- dissect returns an E' that is smaller than E.

dissect-lemma2 : ∀ (E : EvalCtx K K) → dissect E ≡ inj₁ refl -> E ≡ []
dissect-lemma2 [] p = refl
dissect-lemma2 (V ·r E) p with dissect E
dissect-lemma2 (V ·r E) () | inj₁ refl
dissect-lemma2 (E l· B) p with dissect E
dissect-lemma2 (E l· B) p | inj₁ ()
dissect-lemma2 (V ⇒r E) p with dissect E
dissect-lemma2 (V ⇒r E) () | inj₁ refl
dissect-lemma2 (E l⇒ B) p with dissect E
dissect-lemma2 (E l⇒ B) () | inj₁ refl
dissect-lemma2 (μr V E) p with dissect E
dissect-lemma2 (μr V E) () | inj₁ refl
dissect-lemma2 (μl E B) p with dissect E
dissect-lemma2 (μl E B) p | inj₁ ()


dissect-lemma : ∀ (E : EvalCtx K J)(E' : EvalCtx K J') F → dissect E ≡ inj₂ (_ , E' , F) -> E ≡ extendEvalCtx E' F
dissect-lemma (x ·r E) E' F p with dissect E | inspect dissect E
dissect-lemma (x ·r E) E' .(x ·-) refl | inj₁ refl | I[ eq ]
  rewrite dissect-lemma2 E eq = refl
dissect-lemma (x ·r E) .(x ·r E'') .F' refl | inj₂ (I , E'' , F') | I[_] eq = cong (_ ·r_) (dissect-lemma E E'' F' eq)
dissect-lemma (E l· x) E' F p with dissect E | inspect dissect E
dissect-lemma (E l· x) E' .(-· x) refl | inj₁ refl | I[ eq ] rewrite dissect-lemma2 E eq = refl
dissect-lemma (E l· x) .(E'' l· x) .F' refl | inj₂ (I , E'' , F') | I[_] eq = cong (_l· _) (dissect-lemma E E'' F' eq)
dissect-lemma (x ⇒r E) E' F p with dissect E | inspect dissect E
dissect-lemma (x ⇒r E) E' .(x ⇒-) refl | inj₁ refl | I[ eq ] rewrite dissect-lemma2 E eq = refl
dissect-lemma (x ⇒r E) .(x ⇒r E'') .F' refl | inj₂ (I , E'' , F') | I[_] eq = cong (_ ⇒r_) (dissect-lemma E E'' F' eq)
dissect-lemma (E l⇒ x) E' F p with dissect E | inspect dissect E
dissect-lemma (E l⇒ x) E' .(-⇒ x) refl | inj₁ refl | I[ eq ] rewrite dissect-lemma2 E eq = refl
dissect-lemma (E l⇒ x) .(E'' l⇒ x) .F' refl | inj₂ (I , E'' , F') | I[_] eq = cong (_l⇒ _) (dissect-lemma E E'' F' eq)
dissect-lemma (μr x E) E' F p with dissect E | inspect dissect E
dissect-lemma (μr x E) E' .(μ x -) refl | inj₁ refl | I[ eq ] rewrite dissect-lemma2 E eq = refl
dissect-lemma (μr x E) .(μr x E'') .F' refl | inj₂ (I , E'' , F') | I[_] eq = cong (μr _) (dissect-lemma E E'' F' eq)
dissect-lemma (μl E B) E' F p with dissect E | inspect dissect E
dissect-lemma (μl E B) E' .(μ- B) refl | inj₁ refl | I[ eq ] rewrite dissect-lemma2 E eq = refl
dissect-lemma (μl E B) .(μl E'' B) .F' refl | inj₂ (I , E'' , F') | I[_] eq = cong (λ E → μl E B) (dissect-lemma E E'' F' eq)

{-# TERMINATING #-}
unwindVE : (A : ∅ ⊢⋆ I)(B : ∅ ⊢⋆ J)(E : EvalCtx K J)(E' : EvalCtx J I)
      → B ≡ closeEvalCtx E' A
      → (VA : Value⋆ A)
      → (VB : Value⋆ B)
      → (compEvalCtx E E' ◅ VA) -→s (E ◅ VB) 
unwindVE A B E E' p VA VB with dissect' E' | inspect dissect' E'
unwindVE A B E E' refl VA VB | inj₁ (refl , refl) | I[ eq ] rewrite compEvalCtx-eq E [] rewrite val-unique VA VB = base
... | inj₂ (I , E'' , (-· C)) | I[ eq ] rewrite dissect'-lemma E' E'' (-· C) eq =
  ⊥-elim (lemV· (lem0 _ E'' (subst Value⋆ (trans p (closeEF E'' (-· C) A)) VB)))
... | inj₂ (I , E'' , (V ·-)) | I[ eq ] rewrite dissect'-lemma E' E'' (V ·-) eq =
  ⊥-elim (lemV· (lem0 _ E'' (subst Value⋆ (trans p (closeEF E'' (V ·-) A)) VB)))
unwindVE A B E E' refl VA VB | inj₂ (.* , E'' , (-⇒ C)) | I[ eq ] rewrite dissect'-lemma E' E'' (-⇒ C) eq with decVal C
... | inj₁ VC  = step*
  (cong (stepV VA) (trans (cong dissect (compEF' E E'' (-⇒ C))) (lemma (compEvalCtx E E'') (-⇒ C))))
  (step** (lemV C VC (extendEvalCtx (compEvalCtx E E'') (VA ⇒-)))
          (step* (cong (stepV VC) (lemma (compEvalCtx E E'') (VA ⇒-))) (unwindVE _ _ E E'' (closeEF E'' (-⇒ C) A) (VA V-⇒ VC) VB)))
... | inj₂ ¬VC = ⊥-elim (¬VC (lem0 C (extendEvalCtx E'' (VA ⇒-)) (subst Value⋆ (trans (closeEF E'' (-⇒ C) A) (sym (closeEF E'' (VA ⇒-) C))) VB)))
unwindVE A B E E' refl VA VB | inj₂ (.* , E'' , (V ⇒-)) | I[ eq ] rewrite dissect'-lemma E' E'' (V ⇒-) eq = step* (cong (stepV VA) (trans (cong dissect (compEF' E E'' (V ⇒-))) (lemma (compEvalCtx E E'') (V ⇒-)))) (unwindVE _ _ E E'' (closeEF E'' (V ⇒-) A) (V V-⇒ VA) VB)
unwindVE A B E E' refl VA VB | inj₂ (.* , E'' , (μ- C)) | I[ eq ] rewrite dissect'-lemma E' E'' (μ- C) eq with decVal C
... | inj₁ VC  = step* (cong (stepV VA) (trans (cong dissect (compEF' E E'' (μ- C))) (lemma (compEvalCtx E E'') (μ- C)))) (step** (lemV C VC (extendEvalCtx (compEvalCtx E E'') (μ VA -))) (step* (cong (stepV VC) (lemma (compEvalCtx E E'') (μ VA -))) (unwindVE _ _ E E'' (closeEF E'' (μ- C) A) (V-μ VA VC) VB)))
... | inj₂ ¬VC = ⊥-elim (¬VC (lem0 C (extendEvalCtx E'' (μ VA -)) (subst Value⋆ (trans (closeEF E'' (μ- C) A) (sym (closeEF E'' (μ VA -) C))) VB)))
unwindVE A B E E' refl VA VB | inj₂ (.* , E'' , μ V -) | I[ eq ] rewrite dissect'-lemma E' E'' (μ V -) eq = step* (cong (stepV VA) (trans (cong dissect (compEF' E E'' (μ V -))) (lemma (compEvalCtx E E'') (μ V -)))) (unwindVE _ _ E E'' (closeEF E'' (μ V -) A) (V-μ V VA) VB)

unwindE : (A : ∅ ⊢⋆ I)(B : ∅ ⊢⋆ J)(E : EvalCtx K J)(E' : EvalCtx J I)
      → B ≡ closeEvalCtx E' A
      → (VB : Value⋆ B)
      → (compEvalCtx' E E' ▻ A) -→s (E ◅ VB) 
unwindE A B E E' refl VB = step**
  (subst-step* (cong (λ E → _ , (E ▻ A)) (sym (compEvalCtx-eq E E')))
               (lemV A (lem0 A E' VB) (compEvalCtx E E')))
               (unwindVE A B E E' refl (lem0 A E' VB) VB)

unwind : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J) → A' ≡ closeEvalCtx E A → (V : Value⋆ A') → (E ▻ A) -→s ([] ◅ V)
unwind A A' E p VA' = subst-step*
  (cong (λ E → _ , E ▻ A) (compEvalCtx-eq [] E))
  (unwindE A A' [] E p VA')

β-lem : A ≡ ƛ A' · B' → A —→⋆ B → B ≡ A' [ B' ]
β-lem refl (β-ƛ x) = refl

-- thm2 follows from this stronger theorem
open import Data.Empty
open import Relation.Nullary

lemmaF : ∀ (M : ∅ ⊢⋆ J)(F : Frame K J)(E : EvalCtx K' K)
      → ∀ (E' : EvalCtx K J')(L : ∅ ⊢⋆ I ⇒ J') N (V : Value⋆ M)
      → (VL : Value⋆ L) → (VN : Value⋆ N)
      → ¬ (Value⋆ (closeFrame F M))
      → closeEvalCtx (extendEvalCtx E F) M
        ≡ closeEvalCtx (compEvalCtx E E') (L · N)
      → (extendEvalCtx E F ◅ V) -→s (extendEvalCtx (compEvalCtx E E') (VL ·-) ◅  VN)
lemmaF M (-· B) E E' L N VM VL VN ¬VFM p with lemma51 B
lemmaF M (-· B) E E' L N VM VL VN ¬VFM p | inj₂ (I , E'' , I' , L' , N' , VL' , VN' , refl) with lemma51-good _ (compEvalCtx E E') L N refl VL VN (compEvalCtx E (VM ·r E'')) L' N' (trans (sym p) (trans (closeEF E (-· closeEvalCtx E'' (L' · N')) M) (sym (close-comp E (VM ·r E'') (L' · N'))))) VL' VN'
... | refl , refl , X , refl , refl rewrite val-unique VL VL' = step* (cong (stepV VM) (lemma E (-· closeEvalCtx E'' (L' · N')))) (step** (lem62 (L' · N') _ (extendEvalCtx E (VM ·-)) E'' refl) (step* refl (step** (lemV L' VL' _) (step* (cong (stepV VL') (lemma (compEvalCtx' (extendEvalCtx E (VM ·-)) E'') (-· N'))) (subst-step* (cong (λ E → _ , (E ▻ N')) (cong (λ E → extendEvalCtx E (VL' ·-)) (trans (trans (sym (compEvalCtx-eq (extendEvalCtx E (VM ·-)) E'')) (compEF E (VM ·-) E'')) (sym X)))) (lemV N' VN _))))))
lemmaF M (-· B) E E' L N VM VL VN ¬VFM p | inj₁ VB with lemma51-good _ (compEvalCtx E E') L N refl VL VN E M B (trans (sym p) (closeEF E (-· B) M)) VM VB
... | refl , refl , X , refl , refl rewrite val-unique VL VM = step* (cong (stepV VM) (lemma E (-· B)))
  (subst-step* (cong (λ E → _ , (E ▻ B)) (cong₂ extendEvalCtx (sym X) refl)) (lemV B VN _))
lemmaF M (VA ·-) E E' L N VM VL VN ¬VFM p with lemma51-good _ (compEvalCtx E E') L N refl VL VN E (discharge VA) M (trans (sym p) (closeEF E (VA ·-) M)) VA VM
... | refl , refl , X , refl , refl rewrite val-unique VM VN | val-unique VA VL = subst-step* (cong (λ E → _ , extendEvalCtx E (VL ·-) ◅ VN) (sym X)) base
lemmaF M (-⇒ B) E E' L N VM VL VN ¬VFM p with lemma51 B
... | inj₁ VB = ⊥-elim (¬VFM (VM V-⇒ VB))
... | inj₂ (I , E'' , I' , L' , N' , VL' , VN' , refl) with lemma51-good _ (compEvalCtx E E') L N refl VL VN (compEvalCtx E (VM ⇒r E'')) L' N' (trans (sym p) (trans (closeEF E (-⇒ closeEvalCtx E'' (L' · N')) M) (sym (close-comp E (VM ⇒r E'') (L' · N'))))) VL' VN'
... | refl , refl , X , refl , refl rewrite val-unique VL VL' = step* (cong (stepV VM) (lemma E (-⇒ B))) (step** (lem62 (L' · N') _ (extendEvalCtx E (VM ⇒-)) E'' refl) (subst-step* (cong (λ E → _ , E ▻ (L' · N')) (trans (trans (sym (compEvalCtx-eq (extendEvalCtx E (VM ⇒-)) E'')) (compEF E (VM ⇒-) E'')) (sym X))) (step* refl (step** (lemV L' VL' (extendEvalCtx (compEvalCtx E E') (-· N'))) (step* (cong (stepV VL') (lemma (compEvalCtx E E') (-· N'))) (lemV N' VN _))))))
lemmaF M (VA ⇒-) E E' L N VM VL VN ¬VFM p = ⊥-elim (¬VFM (VA V-⇒ VM))
lemmaF M (μ- B) E E' L N VM VL VN ¬VFM p with lemma51 B
... | inj₁ VB = ⊥-elim (¬VFM (V-μ VM VB))
... | inj₂ (I , E'' , I' , L' , N' , VL' , VN' , refl)  with lemma51-good _ (compEvalCtx E E') L N refl VL VN (compEvalCtx E (μr VM E'')) L' N' (trans (sym p) (trans (closeEF E (μ- closeEvalCtx E'' (L' · N')) M) (sym (close-comp E (μr VM E'') (L' · N'))))) VL' VN'
... | refl , refl , X , refl , refl rewrite val-unique VL VL' = step* (cong (stepV VM) (lemma E (μ- B))) (step** (lem62 (L' · N') _ (extendEvalCtx E (μ VM -)) E'' refl) (subst-step* (cong (λ E → _ , E ▻ (L' · N')) (trans (trans (sym (compEvalCtx-eq (extendEvalCtx E (μ VM -)) E'')) (compEF E (μ VM -) E'')) (sym X))) (step* refl (step** (lemV L' VL' (extendEvalCtx (compEvalCtx E E') (-· N'))) (step* (cong (stepV VL') (lemma (compEvalCtx E E') (-· N'))) (lemV N' VN _))))))
lemmaF M μ VA - E E' L N VM VL VN ¬VFM p = ⊥-elim (¬VFM (V-μ VA VM))

thm1 : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → A' ≡ closeEvalCtx E A → (B : ∅ ⊢⋆ K)(V : Value⋆ B)
  → A' —↠E B -> (E ▻ A) -→s ([] ◅ V)
thm1 A A' E p .A' V refl—↠E = unwind A A' E p V
  -- it's already a value, so there's only some unwinding to do
thm1 A A' E refl C V (trans—↠E {B = B} q q') with lemmaE' A E B q
... | J , E' , L , N , p , p' , p'' , inj₁ (E'' , p''') = step** (lem62 L A E E'' p''') (step** (subst-step* (cong (λ E → _ , E ▻ L) (uniquenessE _ (λ V → notboth (closeEvalCtx (compEvalCtx' E E'') L) (V , _ , contextRule (compEvalCtx' E E'') p refl refl)) L N p (compEvalCtx' E E'') E' refl (trans (trans (trans (cong (λ E → closeEvalCtx E L) (sym (compEvalCtx-eq E E''))) (close-comp E E'' L)) (cong (closeEvalCtx E) (sym p'''))) p'))) (lem-→⋆ L N E' p)) (thm1 N B E' (sym p'') C V q'))
... | J , E' , (ƛ L · N) , .(sub (sub-cons ` N) L) , β-ƛ VN , p' , p'' , inj₂ VA with case2 A E VA E' (ƛ L) N (V-ƛ L) VN p'
... | I , I' , E'' , F , E''' , refl , VE'''A , ¬VFE'''A , E'''' , r' = step**
  (step** (subst-step* (cong (λ E → _ , E ▻ A) (trans (sym (compEF E'' F E''')) (compEvalCtx-eq (extendEvalCtx E'' F) E'''))) (unwindE A _ (extendEvalCtx E'' F) E''' refl VE'''A)) (step** (lemmaF (closeEvalCtx E''' A) F E'' E'''' (ƛ L) N VE'''A (V-ƛ L) VN ¬VFE'''A (trans (trans (closeEF E'' F (closeEvalCtx E''' A)) (trans (cong (closeEvalCtx E'') (evalEF' F E''' A)) (sym  (close-comp E'' (evalFrame F E''') A)))) (trans (sym r') (sym (close-comp E'' E'''' (ƛ L · N)))) )) (step* (cong (stepV VN) (lemma (compEvalCtx E'' E'''') (V-ƛ L ·-))) (subst-step* (cong (λ E → _ , E ▻ (L [ N ])) (uniquenessE _ (lemE· (compEvalCtx E'' E'''')) (ƛ L · N) (L [ N ]) (β-ƛ VN) (compEvalCtx E'' E'''') E' refl (trans (trans (close-comp E'' E'''' (ƛ L · N)) r') p'))) base))))
  (thm1 (L [ N ]) B E' (sym p'') C V q')

{-# TERMINATING #-}
thm1b : (A : ∅ ⊢⋆ J)(A' : ∅ ⊢⋆ K)(E : EvalCtx K J)
  → A' ≡ closeEvalCtx E A → (B : ∅ ⊢⋆ K)(V : Value⋆ B)
  → (E ▻ A) -→s ([] ◅ V) ⊎ (∃ λ (W : Value⋆ A) → (E ◅ W) -→s ([] ◅ V)) → A' —↠E B
thm1b (Π A) A' E p B V (inj₁ (step* refl q')) =
 thm1b (Π A) A' E p B V (inj₂ ((V-Π A) , q'))
thm1b (A ⇒ C) A' E p B V (inj₁ (step* refl q')) = thm1b A A' (extendEvalCtx E (-⇒ C)) (trans p (sym (closeEF E (-⇒ C) A))) B V (inj₁ q') 
thm1b (ƛ A) A' E p B V (inj₁ (step* refl q')) =
  thm1b (ƛ A) A' E p B V (inj₂ ((V-ƛ A) , q'))
thm1b (A · C) A' E p B V (inj₁ (step* refl q')) = thm1b A A' (extendEvalCtx E (-· C)) (trans p (sym (closeEF E (-· C) A))) B V (inj₁ q')
thm1b (μ A C) A' E p B V (inj₁ (step* refl q')) = thm1b A A' (extendEvalCtx E (μ- C)) (trans p (sym (closeEF E (μ- C) A))) B V (inj₁ q')
thm1b (con c) A' E p B V (inj₁ (step* refl q')) = thm1b (con c) A' E p B V (inj₂ (V-con c , q'))
thm1b A A' E p B V (inj₂ (W , q)) with dissect E | inspect dissect E
thm1b A .A .[] refl A V (inj₂ (V , base)) | inj₁ refl | I[ eq ] = refl—↠E
thm1b A A' E p B V (inj₂ (W , step* refl q)) | inj₁ refl | I[ eq ] rewrite dissect-lemma2 E eq = thm1b A A' [] p B V (inj₂ (W , q))
... | inj₂ (I , E' , F) | I[ eq ] rewrite dissect-lemma E E' F eq = thm1b A A' (extendEvalCtx E' F) p B V (inj₂ (W , q))

thm2 : (A B : ∅ ⊢⋆ K)(V : Value⋆ B) → A —↠E B → ([] ▻ A) -→s ([] ◅ V)
thm2 A B V p = thm1 A A [] refl B V p

thm2b : (A B : ∅ ⊢⋆ K)(V : Value⋆ B) → ([] ▻ A) -→s ([] ◅ V) → A —↠E B
thm2b A B V p = thm1b A A [] refl B V (inj₁ p)
```
