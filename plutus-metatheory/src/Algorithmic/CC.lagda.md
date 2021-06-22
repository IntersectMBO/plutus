---
title: CC machine for terms
layout: page
---


```
module Algorithmic.CC where

open import Type
open import Type.BetaNormal
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Algorithmic.ReductionEC

open import Relation.Binary.PropositionalEquality renaming ([_] to I[_])
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

dissect-inj₁ : ∀{A B}(E : EC A B)(p : A ≡ B) → dissect E ≡ inj₁ p
  → subst (λ A → EC A B) p E ≡ []
dissect-inj₁ [] refl refl = refl
dissect-inj₁ (E l· N) p q with dissect E
dissect-inj₁ (E l· N) refl q | inj₁ ()
dissect-inj₁ (VM ·r E) p q with dissect E
dissect-inj₁ (VM ·r E) refl () | inj₁ refl
dissect-inj₁ (E ·⋆ A) p q with dissect E
dissect-inj₁ (E ·⋆ A) p () | inj₁ refl
dissect-inj₁ (wrap E) p q with dissect E
dissect-inj₁ (wrap E) p () | inj₁ refl
dissect-inj₁ (unwrap E) p q with dissect E
dissect-inj₁ (unwrap E) p () | inj₁ refl

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

dissect-inj₂ : ∀{A B C}(E : EC A C)(E' : EC A B)(F : Frame B C)
  → dissect E ≡ inj₂ (_ ,, E' ,, F) → E ≡ extEC E' F
dissect-inj₂ (E l· N) E' F p with dissect E | inspect dissect E
dissect-inj₂ (E l· N) .[] .(-· N) refl | inj₁ refl | I[ eq ]
  rewrite dissect-inj₁ E refl eq = refl
dissect-inj₂ (E l· N) .(E'' l· N) .F' refl | inj₂ (_ ,, E'' ,, F') | I[ eq ] =
  cong (_l· N) (dissect-inj₂ E E'' F' eq)
dissect-inj₂ (VM ·r E) E' F p with dissect E | inspect dissect E
dissect-inj₂ (VM ·r E) .[] .(VM ·-) refl | inj₁ refl | I[ eq ] =
  cong (VM ·r_) ( dissect-inj₁ E refl eq)
dissect-inj₂ (VM ·r E) .(VM ·r E') .F refl | inj₂ (_ ,, E' ,, F) | I[ eq ] =
  cong (VM ·r_) (dissect-inj₂ E E' F eq) 
dissect-inj₂ (E ·⋆ A) E' F p with dissect E | inspect dissect E
dissect-inj₂ (E ·⋆ A) .[] .(-·⋆ A) refl | inj₁ refl | I[ eq ] =
  cong (_·⋆ A) (dissect-inj₁ E refl eq)
dissect-inj₂ (E ·⋆ A) .(E'' ·⋆ A) .F' refl | inj₂ (_ ,, E'' ,, F') | I[ eq ] =
  cong (_·⋆ A) (dissect-inj₂ E E'' F' eq)
dissect-inj₂ (wrap E) E' F p with dissect E | inspect dissect E
dissect-inj₂ (wrap E) .[] .wrap- refl | inj₁ refl | I[ eq ] =
  cong wrap (dissect-inj₁ E refl eq)
dissect-inj₂ (wrap E) .(wrap E'') .F' refl | inj₂ (_ ,, E'' ,, F') | I[ eq ] =
  cong wrap (dissect-inj₂ E E'' F' eq)

dissect-inj₂ (unwrap E) E' F p with dissect E | inspect dissect E
dissect-inj₂ (unwrap E) .[] .unwrap- refl | inj₁ refl | I[ eq ] =
  cong unwrap (dissect-inj₁ E refl eq)
dissect-inj₂ (unwrap E) .(unwrap E'') .F' refl | inj₂ (_ ,, E'' ,, F') | I[ eq ]
  = cong unwrap (dissect-inj₂ E E'' F' eq)


compEC' : ∀{A B C} → EC A B → EC B C → EC A C
compEC' E []          = E
compEC' E (E' l· M')  = compEC' (extEC E (-· M')) E'
compEC' E (VM ·r E')  = compEC' (extEC E (VM ·-)) E'
compEC' E (E' ·⋆ A)   = compEC' (extEC E (-·⋆ A)) E'
compEC' E (wrap E')   = compEC' (extEC E wrap-) E'
compEC' E (unwrap E') = compEC' (extEC E unwrap-) E'

postulate
  compEC-eq : ∀{A B C}(E : EC C B)(E' : EC B A) → compEC E E' ≡ compEC' E E'

compEC'-[] : ∀{B C}(E : EC B C) → compEC' [] E ≡ E
compEC'-[] E = sym (compEC-eq [] E)

compEC'-extEC : ∀{A B C D}(E : EC A B)(E' : EC B C)(F : Frame C D)
  → compEC' E (extEC E' F) ≡ extEC (compEC' E E') F
compEC'-extEC E [] (-· N) = refl
compEC'-extEC E [] (VM ·-) = refl
compEC'-extEC E [] (-·⋆ A) = refl
compEC'-extEC E [] wrap- = refl
compEC'-extEC E [] unwrap- = refl
compEC'-extEC E (E' l· N) F = compEC'-extEC (extEC E (-· N)) E' F
compEC'-extEC E (VM ·r E') F = compEC'-extEC (extEC E (VM ·-)) E' F
compEC'-extEC E (E' ·⋆ A) F = compEC'-extEC (extEC E (-·⋆ A)) E' F
compEC'-extEC E (wrap E') F = compEC'-extEC (extEC E wrap-) E' F
compEC'-extEC E (unwrap E') F = compEC'-extEC (extEC E unwrap-) E' F

extEC-[]ᴱ : ∀{A B C}(E : EC A B)(F : Frame B C)(M : ∅ ⊢ C) →
  extEC E F [ M ]ᴱ ≡ E [ F [ M ]ᶠ ]ᴱ
extEC-[]ᴱ [] (-· N) M = refl
extEC-[]ᴱ [] (VL ·-) M = refl
extEC-[]ᴱ [] (-·⋆ A) M = refl
extEC-[]ᴱ [] wrap- M = refl
extEC-[]ᴱ [] unwrap- M = refl
extEC-[]ᴱ (E l· N) F M = cong (_· N) (extEC-[]ᴱ E F M)
extEC-[]ᴱ (VL ·r E) F M = cong (deval VL ·_) (extEC-[]ᴱ E F M)
extEC-[]ᴱ (E ·⋆ A) F M = cong (_·⋆ A) (extEC-[]ᴱ E F M)
extEC-[]ᴱ (wrap E) F M = cong (wrap _ _) (extEC-[]ᴱ E F M)
extEC-[]ᴱ (unwrap E) F M = cong unwrap (extEC-[]ᴱ E F M)
```

# the machine

```
open import Data.List hiding ([_])

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
stepV V (inj₂ (_ ,, E ,, (V-I⇒ b {as' = a ∷ as'} p q ·-))) =
  E ◅ V-I b (bubble p) (step p q V)
stepV V (inj₂ (_ ,, E ,, wrap-))   = E ◅ V-wrap V
stepV (V-Λ M) (inj₂ (_ ,, E ,, -·⋆ A)) = E ▻ (M [ A ]⋆)
stepV (V-IΠ b {as' = []} p q) (inj₂ (_ ,, E ,, -·⋆ A)) =
  E ▻ BUILTIN' b (bubble p) (step⋆ p q) 
stepV (V-IΠ b {as' = a ∷ as'} p q) (inj₂ (_ ,, E ,, -·⋆ A)) =
  E ◅ V-I b (bubble p) (step⋆ p q)
stepV (V-wrap V) (inj₂ (_ ,, E ,, unwrap-)) = E ▻ deval V -- E ◅ V 

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
lemV M (V-IΠ addInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) ([] <>< arity addInteger) as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ subtractInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ multiplyInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ divideInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ quotientInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ remainderInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ modInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ lessThanInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ lessThanEqualsInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ greaterThanInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ greaterThanEqualsInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ equalsInteger {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ concatenate {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ takeByteString {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ dropByteString {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ lessThanByteString {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ greaterThanByteString {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ sha2-256 {as' = as'} p q) E with <>>-cancel-both' _ ([] ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ sha3-256 {as' = as'} p q) E with <>>-cancel-both' _ ([] ∷ Type) _ as' p refl
... | X ,, Y ,, () 
lemV M (V-IΠ verifySignature {as' = as'} (bubble (bubble p)) q) E with <>>-cancel-both' _ ((([] ∷ _) ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ equalsByteString {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV .(ibuiltin ifThenElse) (V-IΠ ifThenElse (start .(Type ∷ Term ∷ Term ∷ Term ∷ [])) base) E = step* refl base
lemV M (V-IΠ ifThenElse {as' = as'} (bubble (bubble (bubble p))) q) E with <>>-cancel-both' _ (((([] ∷ _) ∷ _) ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ charToString {as' = as'} p q) E with <>>-cancel-both' _ ([] ∷ Type) _ as' p refl
... | X ,, Y ,, () 
lemV M (V-IΠ append {as' = as'} (bubble p) q) E with <>>-cancel-both' _ (([] ∷ _) ∷ Type) _ as' p refl
... | X ,, Y ,, ()
lemV M (V-IΠ trace {as' = as'} p q) E with <>>-cancel-both' _ ([] ∷ Type) _ as' p refl
... | X ,, Y ,, ()

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

open import Data.Empty

{-# TERMINATING #-}
unwindVE : ∀{A B C}(M : ∅ ⊢ A)(N : ∅ ⊢ B)(E : EC C B)(E' : EC B A)
      → N ≡ E' [ M ]ᴱ
      → (VM : Value M)
      → (VN : Value N)
      → (compEC' E E' ◅ VM) -→s (E ◅ VN) 
unwindVE A B E E' refl VM VN with dissect E' | inspect dissect E'
... | inj₁ refl | I[ eq ] rewrite dissect-inj₁ E' refl eq rewrite uniqueVal A VM VN = base
... | inj₂ (_ ,, E'' ,, (V-ƛ M ·-)) | I[ eq ] rewrite dissect-inj₂ E' E'' (V-ƛ M ·-) eq = ⊥-elim (lemVβ (lemVE _ E'' (Value2VALUE (subst Value (extEC-[]ᴱ E'' (V-ƛ M ·-) A) VN))))
unwindVE A .(E' [ A ]ᴱ) E E' refl VM VN | inj₂ (_ ,, E'' ,, (V-I⇒ b {as' = []} p x ·-)) | I[ eq ] rewrite dissect-inj₂ E' E'' (V-I⇒ b p x ·-) eq = ⊥-elim (valred (lemVE _ E'' (Value2VALUE (subst Value (extEC-[]ᴱ E'' (V-I⇒ b p x ·-) A) VN))) (β-sbuiltin b (deval (V-I⇒ b p x)) p x A VM))
unwindVE A .(E' [ A ]ᴱ) E E' refl VM VN | inj₂ (_ ,, E'' ,, (V-I⇒ b {as' = x₁ ∷ as'} p x ·-)) | I[ eq ] rewrite dissect-inj₂ E' E'' (V-I⇒ b p x ·-) eq =
  step* (trans (cong (λ E → stepV VM (dissect E)) (compEC'-extEC E E'' (V-I⇒ b p x ·-))) (cong (stepV VM) (dissect-lemma (compEC' E E'') (V-I⇒ b p x ·-)))) (unwindVE _ _ E E'' (extEC-[]ᴱ E'' (V-I⇒ b p x ·-) A) (V-I b (bubble p) (step p x VM)) VN)
unwindVE .(Λ M) .(E' [ Λ M ]ᴱ) E E' refl (V-Λ M) VN | inj₂ (_ ,, E'' ,, -·⋆ C) | I[ eq ] rewrite dissect-inj₂ E' E'' (-·⋆ C) eq = ⊥-elim (lemVβ⋆ (lemVE _ E'' (Value2VALUE (subst Value (extEC-[]ᴱ E'' (-·⋆ C) (Λ M)) VN))))
unwindVE A .(E' [ A ]ᴱ) E E' refl (V-IΠ b {as' = []} p x) VN | inj₂ (_ ,, E'' ,, -·⋆ C) | I[ eq ] rewrite dissect-inj₂ E' E'' (-·⋆ C) eq = ⊥-elim (valred (lemVE _ E'' (Value2VALUE (subst Value (extEC-[]ᴱ E'' (-·⋆ C) A) VN))) (β-sbuiltin⋆ b A p x C))
unwindVE A .(E' [ A ]ᴱ) E E' refl (V-IΠ b {as' = a ∷ as'} p x) VN | inj₂ (_ ,, E'' ,, -·⋆ C) | I[ eq ] rewrite dissect-inj₂ E' E'' (-·⋆ C) eq =
  step* (trans (cong (λ E → stepV _ (dissect E)) (compEC'-extEC E E'' (-·⋆ C))) (cong (stepV (V-IΠ b p x)) (dissect-lemma (compEC' E E'') (-·⋆ C)))) (unwindVE _ _ E E'' (extEC-[]ᴱ E'' (-·⋆ C) A) (V-I b (bubble p) (step⋆ p x)) VN)
... | inj₂ (_ ,, E'' ,, wrap-) | I[ eq ] rewrite dissect-inj₂ E' E'' wrap- eq = step* (trans (cong (λ E → stepV VM (dissect E)) (compEC'-extEC E E'' wrap-)) (cong (stepV VM) (dissect-lemma (compEC' E E'') wrap-))) (unwindVE _ _ E E'' (extEC-[]ᴱ E'' wrap- A) (V-wrap VM) VN)
unwindVE .(wrap _ _ _) .(E' [ wrap _ _ _ ]ᴱ) E E' refl (V-wrap VM) VN | inj₂ (_ ,, E'' ,, unwrap-) | I[ eq ] rewrite dissect-inj₂ E' E'' unwrap- eq = ⊥-elim (valred (lemVE _ E'' (Value2VALUE (subst Value (extEC-[]ᴱ E'' unwrap- (deval (V-wrap VM))) VN))) (β-wrap VM))
unwindVE .(ƛ M) .(E' [ ƛ M ]ᴱ) E E' refl (V-ƛ M) VN | inj₂ (_ ,, E'' ,, (-· M')) | I[ eq ] rewrite dissect-inj₂ E' E'' (-· M') eq = ⊥-elim (lemVβ (lemVE (ƛ M · M') E'' (Value2VALUE (subst Value (extEC-[]ᴱ E'' (-· M') (ƛ M)) VN))))
unwindVE A .(E' [ A ]ᴱ) E E' refl V@(V-I⇒ b {as' = []} p x) VN | inj₂ (_ ,, E'' ,, (-· M')) | I[ eq ] rewrite dissect-inj₂ E' E'' (-· M') eq = ⊥-elim (valred (lemVE _ E'' (Value2VALUE (subst Value (extEC-[]ᴱ E'' (-· M') A) VN))) (β-sbuiltin b A p x M' (VALUE2Value (lemVE _ (extEC E'' (V ·-)) (Value2VALUE (subst Value (trans (extEC-[]ᴱ E'' (-· M') A) (sym (extEC-[]ᴱ E'' (V ·-) M'))) VN))))))
unwindVE A .(E' [ A ]ᴱ) E E' refl V@(V-I⇒ b {as' = a ∷ as'} p x) VN | inj₂ (_ ,, E'' ,, (-· M')) | I[ eq ] rewrite dissect-inj₂ E' E'' (-· M') eq = step* (trans (cong (λ E → stepV (V-I⇒ b p x) (dissect E)) (compEC'-extEC E E'' (-· M'))) (cong (stepV (V-I⇒ b p x)) (dissect-lemma (compEC' E E'') (-· M')))) (step** (lemV M' (VALUE2Value (lemVE M' (extEC E'' (V-I⇒ b p x ·-)) (Value2VALUE (subst Value (trans (extEC-[]ᴱ E'' (-· M') A) (sym (extEC-[]ᴱ E'' (V-I⇒ b p x ·-) M'))) VN)))) (extEC (compEC' E E'') (V-I⇒ b p x ·-))) (step* (cong (stepV _) (dissect-lemma (compEC' E E'') (V-I⇒ b p x ·-))) ((unwindVE (A · M') _ E E'' (extEC-[]ᴱ E'' (-· M') A) (V-I b (bubble p)
  (step p x
   (VALUE2Value
    (lemVE M' (extEC E'' (V-I⇒ b p x ·-))
     (Value2VALUE
      (subst Value
       (trans (extEC-[]ᴱ E'' (-· M') A)
        (sym (extEC-[]ᴱ E'' (V-I⇒ b p x ·-) M')))
       VN)))))) VN))))

unwindE : ∀{A B C}(M : ∅ ⊢ A)(N : ∅ ⊢ B)(E : EC C B)(E' : EC B A)
      → N ≡ E' [ M ]ᴱ
      → (VN : Value N)
      → (compEC' E E' ▻ M) -→s (E ◅ VN) 
unwindE M N E E' refl VN = step**
  (lemV M _ (compEC' E E'))
  (unwindVE M N E E' refl (VALUE2Value (lemVE M E' (Value2VALUE VN))) VN)

open import Relation.Nullary

data CaseP {A B}(M : ∅ ⊢ B)(M' : ∅ ⊢ A)(E : EC A B) : Set where
  redex : ∀ {C}
    → ¬ (Value M) 
    → (E' : EC A C)
    → (N : ∅ ⊢ C)
    → M' ≡ E' [ N ]ᴱ
    → (L : ∅ ⊢ C)
    → E [ M ]ᴱ ≡ E' [ L ]ᴱ
    → L —→⋆ N
    -- different stuff
    → (E'' : EC B C)
    → M ≡ E'' [ L ]ᴱ
    → CaseP M M' E
  val : ∀ {C}
    → (E' : EC A C)
    → (N : ∅ ⊢ C)
    → M' ≡ E' [ N ]ᴱ
    → (L : ∅ ⊢ C)
    → E [ M ]ᴱ ≡ E' [ L ]ᴱ
    → L —→⋆ N
    -- different stuff
    → Value M
    → CaseP M M' E
  
caseP : ∀{A B}(M : ∅ ⊢ B)(M' : ∅ ⊢ A)(E : EC A B) → E [ M ]ᴱ —→ M'
  → CaseP M M' E
caseP M M' E (ruleEC E' x p p') with rlemma51! M
-- E'  goes all the way from the outside to the redex
-- E only goes as far as M
-- E'' is inside M
-- E''' goes all the way down to the redex

... | done VM = val E' _ p' _ p x VM
... | step ¬VM E'' q1 q2 X with rlemma51! (E [ M ]ᴱ)
... | done VEM = ⊥-elim (¬VM (VALUE2Value (lemVE M E (Value2VALUE VEM))))
... | step ¬VEM E''' q1' q2' X' with X' (compEC E E'') (trans (cong (λ M → E [ M ]ᴱ) q2) {!!}) q1
... | refl ,, refl ,, refl with X' E' p (β x)
... | refl ,, refl ,, refl = redex ¬VM (compEC E E'') _ p' _ p x E'' q2
caseP M .(error _) E (ruleErr E₁ x) = {!!}

lem-→s⋆ : ∀{A B}(E : EC A B){L N} →  L —→⋆ N -> (E ▻ L) -→s (E ▻ N)
lem-→s⋆ E (β-ƛ V) = step*
  refl
  (step** (lemV _ (V-ƛ _) (extEC E (-· _)))
          (step* (cong (stepV (V-ƛ _)) (dissect-lemma E (-· _)))
                 (step** (lemV _ V (extEC E (V-ƛ _ ·-)))
                         (step* (cong (stepV V) (dissect-lemma E (V-ƛ _ ·-)))
                                base))))
lem-→s⋆ E β-Λ = step*
  refl
  (step** (lemV _ (V-Λ _) (extEC E (-·⋆ _)))
          (step* (cong (stepV (V-Λ _)) (dissect-lemma E (-·⋆ _)))
                 base))
lem-→s⋆ E (β-wrap V) = step*
  refl
  (step** (lemV _ (V-wrap V) (extEC E unwrap-))
          (step* (cong (stepV (V-wrap V)) (dissect-lemma E unwrap-))
                 base))
lem-→s⋆ E (β-sbuiltin b t p bt u vu) with bappTermLem b t p (BApp2BAPP bt)
... | _ ,, _ ,, refl = step*
  refl
  (step** (lemV t (V-I⇒ b p bt) (extEC E (-· u)))
          (step* (cong (stepV (V-I⇒ b p bt)) (dissect-lemma E (-· u)))
                 (step** (lemV u vu (extEC E (V-I⇒ b p bt ·-)))
                         (step* (cong (stepV vu) (dissect-lemma E (V-I⇒ b p bt ·-)))
                                base))))
lem-→s⋆ E (β-sbuiltin⋆ b t p bt A) with bappTypeLem b t p (BApp2BAPP bt)
... | _ ,, _ ,, refl = step*
  refl
  (step** (lemV t (V-IΠ b p bt) (extEC E (-·⋆ A)))
          (step* (cong (stepV (V-IΠ b p bt)) (dissect-lemma E (-·⋆ A))) base))

thm1 : ∀{A B}(M : ∅ ⊢ A)(M' : ∅ ⊢ B)(E : EC B A)
  → M' ≡ E [ M ]ᴱ → (O : ∅ ⊢ B)(V : Value O)
  → M' —↠ O -> (E ▻ M) -→s ([] ◅ V)
thm1 M M' E p .M' V refl—↠ = subst
  (λ E → (E ▻ M) -→s ([] ◅ V))
  (compEC'-[] E)
  (unwindE M M' [] E p V)
thm1 M _ E refl O V (trans—↠ q q') with caseP M _ E q
... | redex ¬VM E' N x L x₁ x₂ E'' refl = step**
  (lem62 _ E E'')
  (step**
    (subst (λ E → (E ▻ L) -→s (E' ▻ N))
      {!!}
      (lem-→s⋆ E' x₂))
    (thm1 _ _  E' x _ V q'))
... | val E' N x L x₁ x₂ x₃ = {!!}
