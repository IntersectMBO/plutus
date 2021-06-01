---
title: CC machine for terms
layout: page
---


```
module Algorithmic.CC where

open import Type
open import Type.BetaNormal
open import Algorithmic.ReductionEC

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)

dissect : ∀{A B}(E : EC A B) → A ≡ B ⊎ Σ (∅ ⊢Nf⋆ *) λ C → EC A C × Frame C B
dissect []        = inj₁ refl
dissect (E l· M') with dissect E
... | inj₁ refl         = inj₂ (_ ,, [] ,, -· M')
... | inj₂ (C ,, E' ,, F) = inj₂ (C ,, E' l· M' ,, F)
dissect (VM ·r E) with dissect E
... | inj₁ refl         = inj₂ (_ ,, [] ,, VM ·-)
... | inj₂ (C ,, E' ,, F) = inj₂ (C ,, VM ·r E' ,, F)
dissect (E ·⋆ A) with dissect E
... | inj₁ refl         = inj₂ (_ ,, [] ,,  -·⋆ A)
... | inj₂ (C ,, E' ,, F) = inj₂ (C ,, E' ·⋆ A ,, F)
dissect (wrap E) with dissect E
... | inj₁ refl         = inj₂ (_ ,, [] ,, wrap-)
... | inj₂ (C ,, E' ,, F) = inj₂ (C ,, wrap E' ,, F)
dissect (unwrap E) with dissect E
... | inj₁ refl         = inj₂ (_ ,, [] ,, unwrap-)
... | inj₂ (C ,, E' ,, F) = inj₂ (C ,, unwrap E' ,, F)

compEC : ∀{A B C} → EC A B → EC B C → EC A C
compEC []         E' = E'
compEC (E  l· M') E' = compEC E E' l· M'
compEC (VM ·r E)  E' = VM ·r compEC E E'
compEC (E ·⋆ A)   E' = compEC E E' ·⋆ A
compEC (wrap E)   E' = wrap (compEC E E') 
compEC (unwrap E) E' = unwrap (compEC E E')

extEC : ∀{A B C}(E : EC A B)(F : Frame B C) → EC A C
extEC []         (-· M') = [] l· M'
extEC []         (VM ·-) = VM ·r []
extEC []         (-·⋆ A) = [] ·⋆ A
extEC []         wrap-   = wrap []
extEC []         unwrap- = unwrap []
extEC (E l· M')  F       = extEC E F l· M'
extEC (VM ·r E)  F       = VM ·r extEC E F
extEC (E ·⋆ A)   F       = extEC E F ·⋆ A
extEC (wrap E)   F       = wrap (extEC E F)
extEC (unwrap E) F       = unwrap (extEC E F)

compEC' : ∀{A B C} → EC A B → EC B C → EC A C
compEC' E []          = E
compEC' E (E' l· M')  = compEC' (extEC E (-· M')) E'
compEC' E (VM ·r E')  = compEC' (extEC E (VM ·-)) E'
compEC' E (E' ·⋆ A)   = compEC' (extEC E (-·⋆ A)) E'
compEC' E (wrap E')   = compEC' (extEC E wrap-) E'
compEC' E (unwrap E') = compEC' (extEC E unwrap-) E'

```

# the machine

```
open import Data.List hiding ([_])

open import Algorithmic
open import Algorithmic.RenamingSubstitution

data State (T : ∅ ⊢Nf⋆ *) : Set where
  _▻_ : {H : ∅ ⊢Nf⋆ *} → EC T H → ∅ ⊢ H → State T
  _◅_ : {H : ∅ ⊢Nf⋆ *} → EC T H → {t : ∅ ⊢ H} → Value t → State T
  □  : {t : ∅ ⊢ T} →  Value t → State T
  ◆   : (A : ∅ ⊢Nf⋆ *)  →  State T

stepV : ∀{A B }{M : ∅ ⊢ A}(V : Value M)
       → (B ≡ A) ⊎ ∃ (λ C → EC B C × Frame C A)
       → State B
stepV V (inj₁ refl)                 = [] ◅ V
stepV V (inj₂ (_ ,, E ,, (-· N)))  = extEC E (V ·-) ▻ N
stepV V (inj₂ (_ ,, E ,, (V-ƛ M ·-))) = E ▻ (M [ deval V ])
stepV V (inj₂ (_ ,, E ,, (V-I⇒ b {as' = []} p q ·-))) =
  E ▻ BUILTIN' b (bubble p) (step p q V)
stepV V (inj₂ (_ ,, E ,, (V-I⇒ b {as' = Term ∷ as'} p q ·-)))
  with bappTermLem b _ (bubble p) (BApp2BAPP (step p q V))
... | _ ,, _ ,, refl = E ◅ V-I⇒ b (bubble p) (step p q V) 
stepV V (inj₂ (_ ,, E ,, (V-I⇒ b {as' = Type ∷ as'} p q ·-)))
  with bappTypeLem b _ (bubble p) (BApp2BAPP (step p q V))
... | _ ,, _ ,, refl = E ◅ V-IΠ b (bubble p) (step p q V) 
stepV V (inj₂ (_ ,, E ,, wrap-))   = E ◅ V-wrap V
stepV (V-Λ M) (inj₂ (_ ,, E ,, -·⋆ A)) = E ▻ (M [ A ]⋆)
stepV (V-IΠ b {as' = []} p q) (inj₂ (_ ,, E ,, -·⋆ A)) =
  E ▻ BUILTIN' b (bubble p) (step⋆ p q) 
stepV (V-IΠ b {as' = Term ∷ as'} p q) (inj₂ (_ ,, E ,, -·⋆ A))
  with bappTermLem b _ (bubble p) (BApp2BAPP (step⋆ p q {A}))
... | _ ,, _ ,, X =
  E ◅ convVal' X (V-I⇒ b (bubble p) (convBApp1 b X (step⋆ p q)))
stepV (V-IΠ b {as' = Type ∷ as'} p q) (inj₂ (_ ,, E ,, -·⋆ A))
  with bappTypeLem b _ (bubble p) (BApp2BAPP (step⋆ p q))
... | _ ,, _ ,, X =
  E ◅ convVal' X (V-IΠ b (bubble p) (convBApp1 b X (step⋆ p q)))
stepV (V-wrap V) (inj₂ (_ ,, E ,, unwrap-)) = E ◅ V 

stepT : ∀{A} → State A → State A
stepT (E ▻ ƛ M)        = E ◅ V-ƛ M 
stepT (E ▻ (M · M'))   = extEC E (-· M') ▻ M
stepT (E ▻ Λ M)        = E ◅ V-Λ M 
stepT (E ▻ (M ·⋆ A))   = extEC E (-·⋆ A) ▻ M
stepT (E ▻ wrap A B M) = extEC E wrap- ▻ M
stepT (E ▻ unwrap M)   = extEC E unwrap- ▻ M
stepT (E ▻ con c)      = E ◅ V-con c 
stepT (E ▻ ibuiltin b) = E ◅ ival b 
stepT (E ▻ error A)    = ◆ A
stepT (E ◅ V)          = stepV V (dissect E)
stepT (□ V)            = □ V
stepT (◆ A)            = ◆ A
```

```
data _-→s_ {A : ∅ ⊢Nf⋆ *} : State A → State A → Set where
  base  : {s : State A} → s -→s s
  step* : {s s' s'' : State A}
        → stepT s ≡ s'
        → s' -→s s''
        → s -→s s''

step** : ∀{A}{s : State A}{s' : State A}{s'' : State A}
        → s -→s s'
        → s' -→s s''
        → s -→s s''
step** base q = q
step** (step* x p) q = step* x (step** p q)

dissect-lemma : ∀{A B C}(E : EC A B)(F : Frame B C)
  → dissect (extEC E F) ≡ inj₂ (_ ,, E ,, F)
dissect-lemma []         (-· M') = refl
dissect-lemma []         (VM ·-) = refl
dissect-lemma []         (-·⋆ A) = refl
dissect-lemma []         wrap-   = refl
dissect-lemma []         unwrap- = refl
dissect-lemma (E l· M')  F
  rewrite dissect-lemma E F = refl
dissect-lemma (VM ·r E)  F
  rewrite dissect-lemma E F = refl
dissect-lemma (E ·⋆ A)   F
  rewrite dissect-lemma E F = refl
dissect-lemma (wrap E)   F
  rewrite dissect-lemma E F = refl
dissect-lemma (unwrap E) F
  rewrite dissect-lemma E F = refl

open import Builtin

lemV : ∀{A B}(M : ∅ ⊢ B)(V : Value M)(E : EC A B) → (E ▻ M) -→s (E ◅ V)
lemV .(ƛ M)        (V-ƛ M)      E = step* refl base
lemV .(Λ M)        (V-Λ M)      E = step* refl base
lemV .(wrap _ _ _) (V-wrap V)   E = step*
  refl
  (step**
    (lemV _ V (extEC E wrap-))
    (step* (cong (stepV V) (dissect-lemma E wrap-))
           base))
lemV .(con cn)     (V-con cn)   E = step* refl base
-- v a brute force proof by pattern matching on builtins
lemV .(ibuiltin addInteger)
     (V-I⇒ addInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin addInteger · _)
     (V-I⇒ addInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ addInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin subtractInteger)
     (V-I⇒ subtractInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin subtractInteger · _)
     (V-I⇒ subtractInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ subtractInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'

lemV .(ibuiltin multiplyInteger)
     (V-I⇒ multiplyInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin multiplyInteger · _)
     (V-I⇒ multiplyInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ multiplyInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'

lemV .(ibuiltin divideInteger)
     (V-I⇒ divideInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin divideInteger · _)
     (V-I⇒ divideInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ divideInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin quotientInteger)
     (V-I⇒ quotientInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin quotientInteger · _)
     (V-I⇒ quotientInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ quotientInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'

lemV .(ibuiltin remainderInteger)
     (V-I⇒ remainderInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin remainderInteger · _)
     (V-I⇒ remainderInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ remainderInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin modInteger)
     (V-I⇒ modInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin modInteger · _)
     (V-I⇒ modInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ modInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin lessThanInteger)
     (V-I⇒ lessThanInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin lessThanInteger · _)
     (V-I⇒ lessThanInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ lessThanInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin lessThanEqualsInteger)
     (V-I⇒ lessThanEqualsInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin lessThanEqualsInteger · _)
     (V-I⇒ lessThanEqualsInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ lessThanEqualsInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin greaterThanInteger)
     (V-I⇒ greaterThanInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin greaterThanInteger · _)
     (V-I⇒ greaterThanInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ greaterThanInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'

lemV .(ibuiltin greaterThanEqualsInteger)
     (V-I⇒ greaterThanEqualsInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin greaterThanEqualsInteger · _)
     (V-I⇒ greaterThanEqualsInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ greaterThanEqualsInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin equalsInteger)
     (V-I⇒ equalsInteger (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin equalsInteger · _)
     (V-I⇒ equalsInteger (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ equalsInteger {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin concatenate)
     (V-I⇒ concatenate (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin concatenate · _)
     (V-I⇒ concatenate (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ concatenate {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin takeByteString)
     (V-I⇒ takeByteString (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin takeByteString · _)
     (V-I⇒ takeByteString (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ takeByteString {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin dropByteString)
     (V-I⇒ dropByteString (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin dropByteString · _)
     (V-I⇒ dropByteString (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ dropByteString {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin lessThanByteString)
     (V-I⇒ lessThanByteString (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin lessThanByteString · _)
     (V-I⇒ lessThanByteString (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ lessThanByteString {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin greaterThanByteString)
     (V-I⇒ greaterThanByteString (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin greaterThanByteString · _)
     (V-I⇒ greaterThanByteString (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ greaterThanByteString {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin sha2-256) (V-I⇒ sha2-256 (start .(Term ∷ [])) base) E =
  step* refl base
lemV M (V-I⇒ sha2-256 {as' = as'} (bubble {as = as} p) q) E with
  <>>-cancel-both' as _ ([] ∷ Term) _ p refl
... | _ ,, () ,, _
lemV .(ibuiltin sha3-256) (V-I⇒ sha3-256 (start .(Term ∷ [])) base) E =
  step* refl base
lemV M (V-I⇒ sha3-256 {as' = as'} (bubble {as = as} p) q) E with
  <>>-cancel-both' as _ ([] ∷ Term) _ p refl
... | _ ,, () ,, _
lemV .(ibuiltin verifySignature) (V-I⇒ verifySignature (start .(Term ∷ Term ∷ Term ∷ [])) base) E = step* refl base
lemV (ibuiltin verifySignature · t) (V-I⇒ verifySignature (bubble (start .(Term ∷ Term ∷ Term ∷ []))) (step .(start (Term ∷ Term ∷ Term ∷ [])) base vt)) E = step* refl (step* refl (step* (cong (stepV _) (dissect-lemma E (-· t))) (step** (lemV t vt (extEC E (_ ·-))) (step* (cong (stepV vt) (dissect-lemma E (_ ·-))) base))))
lemV ((ibuiltin verifySignature · t) · u) (V-I⇒ verifySignature (bubble (bubble (start .(Term ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Term ∷ Term ∷ Term ∷ []))) (step .(start (Term ∷ Term ∷ Term ∷ [])) base vt) vu)) E = step* refl (step* refl (step* refl (step* (cong (stepV _) (dissect-lemma (extEC E (-· u)) (-· t))) (step** (lemV t vt (extEC (extEC E (-· u)) (_ ·-))) (step* (cong (stepV vt) (dissect-lemma (extEC E (-· u)) (_ ·-)) ) (step* (cong (stepV _) (dissect-lemma E (-· u))) (step** (lemV u vu (extEC E (_ ·-))) (step* (cong (stepV vu) (dissect-lemma E (_ ·-))) base))))))))
lemV M (V-I⇒ verifySignature {as' = as'} (bubble (bubble (bubble {as = as} p))) q) E with <>>-cancel-both' as _ ((([] ∷ Term) ∷ Term) ∷ Term) _ p refl
... | _ ,, () ,, _
lemV .(ibuiltin equalsByteString)
     (V-I⇒ equalsByteString (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin equalsByteString · _)
     (V-I⇒ equalsByteString (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ equalsByteString {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV M (V-I⇒ ifThenElse (bubble (start .(Type ∷ Term ∷ Term ∷ Term ∷ []))) q) E with BApp2BAPP q
lemV (ibuiltin ifThenElse ·⋆ A) (V-I⇒ ifThenElse (bubble (start .(arity ifThenElse))) (step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base)) E | step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl refl = step* refl (step** (lemV (ibuiltin ifThenElse) (ival ifThenElse) (extEC E (-·⋆ A))) (step* (cong (stepV _) (dissect-lemma E (-·⋆ A))) base))
lemV .(_ · _) (V-I⇒ ifThenElse (bubble (bubble (start .(Type ∷ Term ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) q vu)) E with BApp2BAPP q
lemV ((ibuiltin ifThenElse ·⋆ A) · b) (V-I⇒ ifThenElse (bubble (bubble (start .(arity ifThenElse)))) (step .(bubble (start (arity ifThenElse))) (step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base) vb)) E | step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl refl = step* refl (step* refl (step** (lemV (ibuiltin ifThenElse) (ival ifThenElse) (extEC (extEC E (-· _)) (-·⋆ A))) (step* (cong (stepV _) (dissect-lemma (extEC E (-· _)) (-·⋆ A))) (step* (cong (stepV _) (dissect-lemma E (-· _))) (step** (lemV _ vb (extEC E (_ ·-))) (step* (cong (stepV vb) (dissect-lemma E _)) base))))))
lemV .((_ · _) · _) (V-I⇒ ifThenElse (bubble (bubble (bubble (start .(Type ∷ Term ∷ Term ∷ Term ∷ []))))) (step .(bubble (bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ [])))) (step .(bubble (start (Type ∷ Term ∷ Term ∷ Term ∷ []))) q x₁) x)) E with BApp2BAPP q
lemV (((ibuiltin ifThenElse ·⋆ A) · b) · t) (V-I⇒ ifThenElse (bubble (bubble (bubble (start .(arity ifThenElse))))) (step .(bubble (bubble (start (arity ifThenElse)))) (step .(bubble (start (arity ifThenElse))) (step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base) vb) vt)) E | step⋆ .(start (Type ∷ Term ∷ Term ∷ Term ∷ [])) base refl refl = step* refl (step* refl (step* refl (step** (lemV (ibuiltin ifThenElse) (ival ifThenElse) (extEC (extEC (extEC E (-· t)) (-· b)) (-·⋆ A))) (step* (cong (stepV _) (dissect-lemma (extEC (extEC E (-· t)) (-· b)) (-·⋆ A))) (step* (cong (stepV _) (dissect-lemma (extEC E (-· t)) (-· b))) (step** (lemV b vb (extEC (extEC E (-· t)) (_ ·-))) (step* (cong (stepV vb) (dissect-lemma (extEC E (-· t)) (_ ·-))) (step* (cong (stepV _) (dissect-lemma E (-· t))) (step** (lemV t vt (extEC E _)) (step* (cong (stepV vt) (dissect-lemma E _)) base))))))))))
lemV M (V-I⇒ ifThenElse {as' = as'} (bubble (bubble (bubble (bubble {as = as} p)))) q) E with <>>-cancel-both' as _ ([] <>< arity ifThenElse) _ p refl
... | X ,, () ,, Y'
lemV .(ibuiltin charToString) (V-I⇒ charToString (start .(Term ∷ [])) base) E =
  step* refl base
lemV M (V-I⇒ charToString {as' = as'} (bubble {as = as} p) q) E with
  <>>-cancel-both' as _ ([] ∷ Term) _ p refl
... | _ ,, () ,, _
lemV .(ibuiltin append)
     (V-I⇒ append (start .(Term ∷ Term ∷ [])) base)
     E = step* refl base
lemV .(ibuiltin append · _)
     (V-I⇒ append (bubble (start .(Term ∷ Term ∷ [])))
     (step .(start (Term ∷ Term ∷ [])) base v))
     E = step*
  refl
  (step*
    refl
    (step* (cong (stepV _) (dissect-lemma E (-· deval v)))
           (step**
             (lemV (deval v) v (extEC E (_ ·-)))
             (step* (cong (stepV v) (dissect-lemma E (_ ·-))) base))))
lemV M (V-I⇒ append {as' = as'} (bubble (bubble {as = as} p)) q) E
  with <>>-cancel-both' as _ (([] ∷ Term) ∷ Term) (Term ∷ as') p refl
... | X ,, () ,, Y'
lemV .(ibuiltin trace) (V-I⇒ trace (start .(Term ∷ [])) base) E =
  step* refl base
lemV M (V-I⇒ trace {as' = as'} (bubble {as = as} p) q) E with
  <>>-cancel-both' as _ ([] ∷ Term) _ p refl
... | _ ,, () ,, _
lemV M (V-IΠ b p q) E = {!!}

lem62 : ∀{A B C}(L : ∅ ⊢ C)(E : EC A B)(E' : EC B C)
      → (E ▻ (E' [ L ]ᴱ)) -→s (compEC' E E' ▻ L)
lem62 L E []          = base
lem62 L E (E' l· M')  = step* refl (lem62 L (extEC E (-· M')) E')
lem62 L E (VM ·r E')  = step* refl (step**
  (lemV _ VM (extEC E (-· (E' [ L ]ᴱ))))
  (step* (cong (stepV VM) (dissect-lemma E (-· (E' [ L ]ᴱ))))
         (lem62 L (extEC E (VM ·-)) E')))
lem62 L E (E' ·⋆ A)   = step* refl (lem62 L (extEC E (-·⋆ A)) E')
lem62 L E (wrap E')   = step* refl (lem62 L (extEC E wrap-) E')
lem62 L E (unwrap E') = step* refl (lem62 L (extEC E unwrap-) E')

