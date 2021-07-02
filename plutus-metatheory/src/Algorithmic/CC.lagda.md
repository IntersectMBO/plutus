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

-- 2nd functor law for []ᴱ
compEC-[]ᴱ : ∀{A B C}(E : EC A B)(E' : EC B C)(L : ∅ ⊢ C)
  → E [ E' [ L ]ᴱ ]ᴱ ≡ compEC E E' [ L ]ᴱ
compEC-[]ᴱ []         E' L = refl
compEC-[]ᴱ (E l· M')  E' L = cong (_· M') (compEC-[]ᴱ E E' L)
compEC-[]ᴱ (VM ·r E)  E' L = cong (deval VM ·_) (compEC-[]ᴱ E E' L) 
compEC-[]ᴱ (E ·⋆ A)   E' L = cong (_·⋆ A) (compEC-[]ᴱ E E' L)
compEC-[]ᴱ (wrap E)   E' L = cong (wrap _ _) (compEC-[]ᴱ E E' L)
compEC-[]ᴱ (unwrap E) E' L = cong unwrap (compEC-[]ᴱ E E' L)
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
open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution

data Focussing {A B}(M : ∅ ⊢ A)(E : EC B A) M' (p : E [ M ]ᴱ —→ M') : Set
  where
  -- there is some duplication here
  -- I am not sure if it's worth adding another type though
  -- or, I could make it a record containing a sum
  local : ∀{A'}(E' : EC B A')(L : ∅ ⊢ A')
    → Redex L
    → E [ M ]ᴱ ≡ E' [ L ]ᴱ
    -- the redex is inside M
    → ∀{E'' : EC A A'}
    → M ≡ E'' [ L ]ᴱ
    → Focussing M E M' p
  nonlocal : ∀{A'}(E' : EC B A')(L : ∅ ⊢ A')
    → Redex L
    → E [ M ]ᴱ ≡ E' [ L ]ᴱ
    -- M is a value, so the redex must be somewhere else
    → Value M
    → Focussing M E M' p

focus : ∀{A B}(M : ∅ ⊢ A)(E : EC B A) M' (p : E [ M ]ᴱ —→ M')
  → Focussing M E M' p
focus M E M' p with rlemma51! (E [ M ]ᴱ)
focus M E M' p | done VEM = ⊥-elim (notVAL VEM p)
focus M E M' p | step ¬VEM E' r q U with rlemma51! M
focus M E M' p | step ¬VEM E' r q U | step ¬VM E'' r' q' U' with U _ (trans (cong (E [_]ᴱ) q') (compEC-[]ᴱ E E'' _)) r'
... | refl ,, refl ,, refl = local (compEC E E'') _ r q q'
focus M E M' p | step ¬VEM E' r q U | done VM = nonlocal E' _ r q VM

-- we can recover that M' == whatever I think
-- storing it in Focussing made things complicated

data ReFocussing {A B}(E : EC B A)(M : ∅ ⊢ A)(VM : Value M)
  {A'}(E₁ : EC B A')(L : ∅ ⊢ A')(r : Redex L)(p : E [ M ]ᴱ ≡ E₁ [ L ]ᴱ)
  : Set where
  locate : ∀{C C'}(E₂ : EC B C)(F : Frame C C')(E₃ : EC C' A)
    → compEC' (extEC E₂ F) E₃ ≡ E
    → Value (E₃ [ M ]ᴱ) -- the point at which we still have a value
    → ¬ (Value (F [ E₃ [ M ]ᴱ ]ᶠ)) -- the point at which we do not
    → (E₄ : EC C A') -- not sure if this is needed, it may always be []?
    → compEC' E₂ E₄ [ L ]ᴱ ≡ E [ M ]ᴱ
    → ReFocussing E M VM E₁ L r p

{-# TERMINATING #-}
-- it should be terminating on the depth of E
refocus : ∀{A B}(E : EC B A)(M : ∅ ⊢ A)(VM : Value M){A'}(E₁ : EC B A')
  (L : ∅ ⊢ A')(r : Redex L)(p : E [ M ]ᴱ ≡ E₁ [ L ]ᴱ)
  → ReFocussing E M VM E₁ L r p
refocus E M VM E₁ L r p with dissect E | inspect dissect E
refocus E M VM E₁ L r p | inj₁ refl | I[ eq ] rewrite dissect-inj₁ E refl eq =
  ⊥-elim (valredex (lemVE L E₁ (Value2VALUE (subst Value p VM))) r)
refocus E M VM E₁ L r p | inj₂ (_ ,, E₂ ,, (-· N)) | I[ eq ] with rlemma51! N
refocus E M VM E₁ L r p | inj₂ (C ,, E₂ ,, (-· N)) | I[ eq ] | step ¬VN E₃ r' p' U with rlemma51! (E [ M ]ᴱ)
... | done VEM = ⊥-elim (valredex (lemVE _ E₁ (Value2VALUE (subst Value p VEM))) r)
... | step ¬VEM E₄ r'' p'' U'  rewrite dissect-inj₂ E E₂ (-· N) eq with U' _ p r
... | refl ,, refl ,, refl with U' (compEC' (extEC E₂ (VM ·-)) E₃) (trans (extEC-[]ᴱ E₂ (-· N) M) (trans (trans (cong (λ N →  E₂ [ M · N ]ᴱ) p') (sym (extEC-[]ᴱ E₂ (VM ·-) _))) (trans (compEC-[]ᴱ (extEC E₂ (VM ·-)) E₃ _) (cong (λ E → E [ _ ]ᴱ) (compEC-eq (extEC E₂ (VM ·-)) E₃))))) r'
... | refl ,, refl ,, refl = locate E₂ (-· N) [] refl VM (lemV'· (λ VN → valredex (lemVE L _ (Value2VALUE (subst Value p' VN))) r')) ((VM EC.·r E₃)) (sym (trans (extEC-[]ᴱ E₂ (-· N) M) (trans (trans (cong (λ N →  E₂ [ M · N ]ᴱ) p') (sym (extEC-[]ᴱ E₂ (VM ·-) _))) (trans (compEC-[]ᴱ (extEC E₂ (VM ·-)) E₃ _) (cong (λ E → E [ _ ]ᴱ) (compEC-eq (extEC E₂ (VM ·-)) E₃))))))
-- same proof twice
refocus E .(ƛ M) (V-ƛ M) E₁ L r p | inj₂ (_ ,, E₂ ,, (-· N)) | I[ eq ] | done VN with rlemma51! (E [ ƛ M ]ᴱ)
... | done VEƛM = ⊥-elim (valredex (lemVE L E₁ (Value2VALUE (subst Value p VEƛM))) r) 
... | step ¬VEƛM E₃ x₁ x₂ U rewrite dissect-inj₂ E E₂ (-· N) eq with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (-· N) (ƛ M)) (β (β-ƛ VN))
... | refl ,, refl ,, refl = locate E₂ (-· N) [] refl (V-ƛ M) (λ V → lemVβ (Value2VALUE V)) [] (sym (extEC-[]ᴱ E₂ (-· N) (ƛ M)))
refocus E M V@(V-I⇒ b {as' = []} p₁ x) E₁ L r p | inj₂ (_ ,, E₂ ,, (-· N)) | I[ eq ] | done VN with rlemma51! (E [ M ]ᴱ)
... | done VEM =
  ⊥-elim (valredex (lemVE L E₁ (Value2VALUE (subst Value p VEM))) r) 
... | step ¬VEM E₃ x₂ x₃ U rewrite dissect-inj₂ E E₂ (-· N) eq with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (-· N) M) (β (β-sbuiltin b M p₁ x N VN))
... | refl ,, refl ,, refl = locate E₂ (-· N) [] refl V (λ V → valred (Value2VALUE V) (β-sbuiltin b M p₁ x N VN)) [] (sym (extEC-[]ᴱ E₂ (-· N) M))
refocus E M (V-I⇒ b {as' = x₁ ∷ as'} p₁ x) E₁ L r p | inj₂ (_ ,, E₂ ,, (-· N)) | I[ eq ] | done VN rewrite dissect-inj₂ E E₂ (-· N) eq with refocus E₂ (M · N) (V-I b (bubble p₁) (step p₁ x VN)) E₁ L r (trans (sym (extEC-[]ᴱ E₂ (-· N) M)) p)
... | locate E₃ F E₄ x₂ x₃ x₄ E₅ x₅ = locate
  E₃
  F
  (extEC E₄ (-· N))
  (trans (compEC'-extEC (extEC E₃ F) E₄ (-· N)) (cong (λ E → extEC E (-· N)) x₂))
  (subst Value (sym (extEC-[]ᴱ E₄ (-· N) M)) x₃)
  (subst (λ M → ¬ Value (F [ M ]ᶠ))
  (sym (extEC-[]ᴱ E₄ (-· N) M)) x₄)
  E₅
  (trans x₅ (sym (extEC-[]ᴱ E₂ (-· N) M)))
  -- unsat builtin case :)
refocus E M VM E₁ L r p | inj₂ (_ ,, E₂ ,, (V@(V-ƛ M₁) ·-))      | I[ eq ]
  with rlemma51! (E [ M ]ᴱ)
... | done VEM =
  ⊥-elim (valredex (lemVE L E₁ (Value2VALUE (subst Value p VEM))) r) 
... | step ¬VEM E₃ x₁ x₂ U  rewrite dissect-inj₂ E E₂ (V ·-) eq
  with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (V ·-) M) (β (β-ƛ VM))
... | refl ,, refl ,, refl = locate E₂ (V ·-) [] refl VM (λ V → lemVβ (Value2VALUE V)) [] (sym (extEC-[]ᴱ E₂ (V ·-) M)) 
refocus E M VM E₁ L r p | inj₂ (_ ,, E₂ ,, (V@(V-I⇒ b {as' = []} p₁ x) ·-)) | I[ eq ] with rlemma51! (E [ M ]ᴱ)
... | done VEM =
  ⊥-elim (valredex (lemVE L E₁ (Value2VALUE (subst Value p VEM))) r) 
... | step ¬VEM E₃ x₁ x₂ U rewrite dissect-inj₂ E E₂ (V ·-) eq
  with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (V ·-) M) (β (β-sbuiltin b _ p₁ x M VM))
... | refl ,, refl ,, refl = locate E₂ (V ·-) [] refl VM (λ V → valred (Value2VALUE V) (β-sbuiltin b _ p₁ x M VM)) [] (sym (extEC-[]ᴱ E₂ (V ·-) M))
refocus E M VM E₁ L r p | inj₂ (_ ,, E₂ ,, _·- {t = t} (V@(V-I⇒ b {as' = _ ∷ as'} p₁ x))) | I[ eq ] rewrite dissect-inj₂ E E₂ (V ·-) eq with refocus E₂ (t · M) (V-I b (bubble p₁) (step p₁ x VM)) E₁ L r (trans (sym (extEC-[]ᴱ E₂ (V ·-) M)) p)
... | locate E₃ F E₄ x₂ x₃ x₄ E₅ x₅ = locate
  E₃
  F
  (extEC E₄ (V ·-))
  (trans (compEC'-extEC (extEC E₃ F) E₄ (V ·-)) (cong (λ E → extEC E (V ·-)) x₂))
  (subst Value (sym (extEC-[]ᴱ E₄ (V ·-) M)) x₃)
  (subst (λ M → ¬ Value (F [ M ]ᶠ))
  (sym (extEC-[]ᴱ E₄ (V ·-) M)) x₄)
  E₅
  (trans x₅ (sym (extEC-[]ᴱ E₂ (V ·-) M)))
refocus E .(Λ M) (V-Λ M) E₁ L r p | inj₂ (_ ,, E₂ ,, -·⋆ A) | I[ eq ]  with rlemma51! (E [ Λ M ]ᴱ)
... | done VEƛM = ⊥-elim (valredex (lemVE L E₁ (Value2VALUE (subst Value p VEƛM))) r) 
... | step ¬VEƛM E₃ x₁ x₂ U rewrite dissect-inj₂ E E₂ (-·⋆ A) eq with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (-·⋆ A) (Λ M)) (β β-Λ)
... | refl ,, refl ,, refl = locate E₂ (-·⋆ A) [] refl (V-Λ M) (λ V → lemVβ⋆ (Value2VALUE V)) [] (sym (extEC-[]ᴱ E₂ (-·⋆ A) (Λ M)))
refocus E M V@(V-IΠ b {as' = []} p₁ x) E₁ L r p | inj₂ (_ ,, E₂ ,, -·⋆ A) | I[ eq ] with rlemma51! (E [ M ]ᴱ)
... | done VEM =
  ⊥-elim (valredex (lemVE L E₁ (Value2VALUE (subst Value p VEM))) r) 
... | step ¬VEM E₃ x₂ x₃ U rewrite dissect-inj₂ E E₂ (-·⋆ A) eq with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (-·⋆ A) M) (β (β-sbuiltin⋆ b M p₁ x A))
... | refl ,, refl ,, refl = locate E₂ (-·⋆ A) [] refl V (λ V → valred (Value2VALUE V) (β-sbuiltin⋆ b M p₁ x A)) [] (sym (extEC-[]ᴱ E₂ (-·⋆ A) M))
refocus E M (V-IΠ b {as' = _ ∷ as'} p₁ x) E₁ L r p | inj₂ (_ ,, E₂ ,, -·⋆ A) | I[ eq ] rewrite dissect-inj₂ E E₂ (-·⋆ A) eq with refocus E₂ (M ·⋆ A) (V-I b (bubble p₁) (step⋆ p₁ x)) E₁ L r (trans (sym (extEC-[]ᴱ E₂ (-·⋆ A) M)) p)
... | locate E₃ F E₄ x₂ x₃ x₄ E₅ x₅ = locate
  E₃
  F
  (extEC E₄ (-·⋆ A))
  (trans (compEC'-extEC (extEC E₃ F) E₄ (-·⋆ A)) (cong (λ E → extEC E (-·⋆ A)) x₂))
  (subst Value (sym (extEC-[]ᴱ E₄ (-·⋆ A) M)) x₃)
  (subst (λ M → ¬ Value (F [ M ]ᶠ))
  (sym (extEC-[]ᴱ E₄ (-·⋆ A) M)) x₄)
  E₅
  (trans x₅ (sym (extEC-[]ᴱ E₂ (-·⋆ A) M)))
refocus E M VM E₁ L r p | inj₂ (μ A B ,, E₂ ,, wrap-) | I[ eq ] rewrite dissect-inj₂ E E₂ wrap- eq with refocus E₂ (wrap _ _ M) (V-wrap VM) E₁ L r (trans (sym (extEC-[]ᴱ E₂ wrap- M)) p)
... | locate E₃ F E₄ x x₁ x₂ E₅ x₃ = locate E₃ F (extEC E₄ wrap-) ((trans (compEC'-extEC (extEC E₃ F) E₄ wrap-) (cong (λ E → extEC E wrap-) x))) (subst Value (sym (extEC-[]ᴱ E₄ wrap- M)) x₁) (λ V → x₂ (subst Value (cong (F [_]ᶠ) (extEC-[]ᴱ E₄ wrap- M)) V)) E₅ (trans x₃ (sym (extEC-[]ᴱ E₂ wrap- M)))
refocus E (wrap A B M) (V-wrap VM) E₁ L r p | inj₂ (_ ,, E₂ ,, unwrap-) | I[ eq ] with rlemma51! (E [ wrap A B M ]ᴱ)
... | done VEM =
  ⊥-elim (valredex (lemVE L E₁ (Value2VALUE (subst Value p VEM))) r) 
... | step ¬VEM E₃ x₁ x₂ U rewrite dissect-inj₂ E E₂ unwrap- eq
  with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ unwrap- (wrap A B M)) (β (β-wrap VM))
... | refl ,, refl ,, refl = locate E₂ unwrap- [] refl (V-wrap VM) (λ V → valred (Value2VALUE V) (β-wrap VM)) [] (sym (extEC-[]ᴱ E₂ unwrap- (wrap A B M)))


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

{-
lemmaF : ∀{A A' B B'}(M : ∅ ⊢ A)(F : Frame B A)(E : EC B' B)
      → ∀ (E' : EC B A')(L : ∅ ⊢ A')
      → (V : Value M)
      → Redex L
      → ¬ (Value (F [ M ]ᶠ))
      → extEC E F [ M ]ᴱ ≡ (compEC' E E') [ L ]ᴱ
      → (extEC E F ◅ V) -→s (compEC' E E' ▻ L)
      -- this would work for the textbook CC machine
      -- but not our CC machine which is technically the SCC machine
-}

-- here we do the change of direction in the CC machine but note, we
-- are already at the fork in the road, we don't have to look for it
lemmaF' : ∀{A A' B B'}(M : ∅ ⊢ A)(F : Frame B A)(E : EC B' B)
      → ∀ (E' : EC B A')(L L' : ∅ ⊢ A')
      → (V : Value M)
      → L —→⋆ L'
      → ¬ (Value (F [ M ]ᶠ))
      → extEC E F [ M ]ᴱ ≡ (compEC' E E') [ L ]ᴱ
      → (extEC E F ◅ V) -→s (compEC' E E' ▻ L')
lemmaF' M (-· N) E E' L L' V r ¬VFM x₁ with rlemma51! N
... | step ¬VN  E₁ x₃ refl U with rlemma51! (extEC E (-· N) [ M ]ᴱ)
... | done VMN = ⊥-elim (¬VFM (VALUE2Value (lemVE (M · E₁ [ _ ]ᴱ) E (Value2VALUE (subst Value (extEC-[]ᴱ E (-· (E₁ [ _ ]ᴱ)) M) VMN))) ))
... | step ¬VEMN E₂ x₆ x₇ U' with U' (compEC' E E') x₁ (β r)
... | refl ,, refl ,, refl with U' (compEC' (extEC E (V ·-)) E₁) (trans (extEC-[]ᴱ E (-· N) M) (trans (trans (sym (extEC-[]ᴱ E (V ·-) _)) (compEC-[]ᴱ (extEC E (V ·-)) E₁ _)) (cong (_[ _ ]ᴱ) (compEC-eq (extEC E (V ·-)) E₁)))) x₃
... | refl ,, x ,, refl rewrite x = step* (cong (stepV V) (dissect-lemma E (-· (E₁ [ L ]ᴱ)))) (step** (lem62 L (extEC E (V ·-)) E₁) (lem-→s⋆ _ r)) 
lemmaF' .(ƛ M) (-· N) E E' L L' (V-ƛ M) r ¬VFM x₁ | done VN with rlemma51! (extEC E (-· N) [ ƛ M ]ᴱ)
... | done VƛMN = ⊥-elim (lemVβ (lemVE _ E (Value2VALUE (subst Value (extEC-[]ᴱ E (-· N) (ƛ M)) VƛMN))))
... | step ¬VƛMN E₁ x₂ x₃ U with U E (extEC-[]ᴱ E (-· N) (ƛ M)) (β (β-ƛ VN))
... | refl ,, refl ,, refl with U (compEC' E E') x₁ (β r)
lemmaF' .(ƛ M) (-· N) E E' L _ (V-ƛ M) (β-ƛ _) ¬VFM x₁ | done VN | step ¬VƛMN E₁ x₂ x₃ U | refl ,, refl ,, refl | refl ,, x ,, refl = step*
  (cong (stepV (V-ƛ M)) (dissect-lemma E (-· N)))
  (step** (lemV N VN (extEC E (V-ƛ M ·-)))
          (step* (cong (stepV VN) (dissect-lemma E (V-ƛ M ·-))) (subst (λ E' →  (E ▻ (M [ N ])) -→s (E' ▻ (M [ N ]))) x base)))

lemmaF' M (-· N) E E' L L' V@(V-I⇒ b {as' = []} p x) r ¬VFM x₁ | done VN with rlemma51! (extEC E (-· N) [ M ]ᴱ)
... | done VMN = ⊥-elim (valred (lemVE _ E (Value2VALUE (subst Value (extEC-[]ᴱ E (-· N) M) VMN))) (β-sbuiltin b M p x N VN))
... | step ¬VMN E₁ x₃ x₄ U with U E (extEC-[]ᴱ E (-· N) M) (β (β-sbuiltin b M p x N VN))
... | refl ,, refl ,, refl with U (compEC' E E') x₁ (β r)
lemmaF' M (-· N) E E' .(M · N) _ V@(V-I⇒ b {as' = []} p x) (β-sbuiltin b₁ .M p₁ bt .N vu) ¬VFM x₁ | done VN | step ¬VMN E x₃ x₄ U | refl ,, refl ,, refl | refl ,, q ,, refl with uniqueVal N VN vu | uniqueVal M V (V-I⇒ b₁ p₁ bt)
... | refl | refl = step*
  (cong (stepV V) (dissect-lemma E (-· N)))
  (step** (lemV N VN (extEC E (V ·-)))
          (step* (cong (stepV VN) (dissect-lemma E (V ·-))) (subst (λ E' → (E ▻ _) -→s (E' ▻ _)) q base)))
lemmaF' M (-· N) E E' L L' (V-I⇒ b {as' = x₂ ∷ as'} p x) r ¬VFM x₁ | done VN =
  ⊥-elim (¬VFM (V-I b (bubble p) (step p x VN)))

lemmaF' M (VN ·-) E E' L L' V x x₁ x₂ with rlemma51! (extEC E (VN ·-) [ M ]ᴱ)
... | done VNM = ⊥-elim (x₁ (VALUE2Value (lemVE (deval VN · M) E (Value2VALUE (subst Value (extEC-[]ᴱ E (VN ·-) M) VNM)))))
lemmaF' M (V-ƛ M₁ ·-) E E' L L' V x x₁ x₂ | step ¬VƛM₁M E₁ x₃ x₄ U with U (compEC' E E') x₂ (β x)
... | refl ,, refl ,, refl with U E (extEC-[]ᴱ E (V-ƛ M₁ ·-) M) (β (β-ƛ V))
lemmaF' M (V-ƛ M₁ ·-) E E' L L' V (β-ƛ _) x₁ x₂ | step ¬VƛM₁M E₁ x₃ x₄ U | refl ,, refl ,, refl | refl ,, q ,, refl = step* (cong (stepV V) (dissect-lemma E (V-ƛ M₁ ·-))) ((subst (λ E' → (E ▻ _) -→s (E' ▻ _)) (sym q) base))
lemmaF' M (V-I⇒ b {as' = x₇ ∷ as'} p x₃ ·-) E E' L L' V x x₁ x₂ | step ¬VNM E₁ x₄ x₅ x₆ = ⊥-elim (x₁ (V-I b (bubble p) (step p x₃ V)))
lemmaF' M (VN@(V-I⇒ b {as' = []} p x₃) ·-) E E' L L' V x x₁ x₂ | step ¬VNM E₁ x₄ x₅ U with U E (extEC-[]ᴱ E (VN ·-) M) (β (β-sbuiltin b _ p x₃ M V))
... | refl ,, refl ,, refl with U (compEC' E E') x₂ (β x)
lemmaF' M (VN@(V-I⇒ b {as' = []} p x₃) ·-) E E' L L' V x x₁ x₂ | step ¬VNM E₁ x₄ x₅ U | refl ,, refl ,, refl | refl ,, q ,, refl rewrite determinism⋆ x (β-sbuiltin b _ p x₃ M V) = step*
  (cong (stepV V) (dissect-lemma E (VN ·-)))
  (subst (λ E' → (E ▻ _) -→s (E' ▻ _)) q base)
lemmaF' M (-·⋆ A) E E' L L' V x x₁ x₂ with rlemma51! (extEC E (-·⋆ A) [ M ]ᴱ)
... | done VM·⋆A = ⊥-elim (x₁ (VALUE2Value (lemVE (M ·⋆ A) E (Value2VALUE (subst Value (extEC-[]ᴱ E (-·⋆ A) M) VM·⋆A)))))
lemmaF' M (-·⋆ A) E E' L L' V x x₁ x₂ | step ¬VM·⋆A E₁ x₃ x₄ U with U (compEC' E E') x₂ (β x)
lemmaF' .(Λ M) (-·⋆ A) E E' L L' (V-Λ M) x x₁ x₂ | step ¬VM·⋆A .(compEC' E E') x₃ x₄ U | refl ,, refl ,, refl with U E (extEC-[]ᴱ E (-·⋆ A) (Λ M)) (β β-Λ)
lemmaF' .(Λ M) (-·⋆ A) E E' L L' (V-Λ M) x x₁ x₂ | step ¬VM·⋆A .(compEC' E E') x₃ x₄ U | refl ,, refl ,, refl | refl ,, q ,, refl rewrite determinism⋆ x (β-Λ) = step*
  (cong (stepV (V-Λ M)) (dissect-lemma E (-·⋆ A)))
  (subst (λ E' → (E ▻ _) -→s (E' ▻ _)) (sym q) base)
lemmaF' M (-·⋆ A) E E' L L' (V-IΠ b {as' = []} p x₅) x x₁ x₂ | step ¬VM·⋆A .(compEC' E E') x₃ x₄ U | refl ,, refl ,, refl with U E (extEC-[]ᴱ E (-·⋆ A) M) (β (β-sbuiltin⋆ b M p x₅ A))
lemmaF' M (-·⋆ A) E E' L L' VM@(V-IΠ b {as' = []} p x₅) x x₁ x₂ | step ¬VM·⋆A .(compEC' E E') x₃ x₄ U | refl ,, refl ,, refl | refl ,, q ,, refl rewrite determinism⋆ x (β-sbuiltin⋆ b M p x₅ A) = step*
  (cong (stepV VM) (dissect-lemma E (-·⋆ A)))
  (subst (λ E' → (E ▻ _) -→s (E' ▻ _)) (sym q) base)
lemmaF' M (-·⋆ A) E E' L L' (V-IΠ b {as' = x₆ ∷ as'} p x₅) x x₁ x₂ | step ¬VM·⋆A .(compEC' E E') x₃ x₄ U | refl ,, refl ,, refl = ⊥-elim (x₁ (V-I b (bubble p) (step⋆ p x₅)))

lemmaF' M wrap- E E' L L' V x x₁ x₂ = {!!}
lemmaF' M unwrap- E E' L L' V x x₁ x₂ = {!!}

err—→ : ∀{A}{M} → error A —→ M → M ≡ error A
err—→ (ruleEC [] () refl refl)
err—→ (ruleErr E x) = refl

err—↠ : ∀{A}{M} → error A —↠ M → M ≡ error A
err—↠ refl—↠        = refl
err—↠ (trans—↠ x p) rewrite err—→ x = err—↠ p

thm1 : ∀{A B}(M : ∅ ⊢ A)(M' : ∅ ⊢ B)(E : EC B A)
  → M' ≡ E [ M ]ᴱ → (O : ∅ ⊢ B)(V : Value O)
  → M' —↠ O -> (E ▻ M) -→s ([] ◅ V)
thm1 M M' E p .M' V refl—↠ = subst
  (λ E → (E ▻ M) -→s ([] ◅ V))
  (compEC'-[] E)
  (unwindE M M' [] E p V)
thm1 M _ E refl O V (trans—↠ q q') with focus M E _ q
... | local E' L (β r) x₁ {E'' = E''} refl = step** (lem62 L E E'') (step** (lem-→s⋆ (compEC' E E'') r) (thm1 _ _ (compEC' E E'') (determinism q (ruleEC (compEC' E E'') r (trans (compEC-[]ᴱ E E'' L) (cong (_[ L ]ᴱ) (compEC-eq E E'')) ) refl)) O V q'))
... | local E' L err x₁ refl rewrite determinism q (ruleErr E' x₁) = ⊥-elim (valerr E-error (subst Value (err—↠ q') V))
... | nonlocal E' L err p VM rewrite determinism q (ruleErr E' p) = ⊥-elim (valerr E-error (subst Value (err—↠ q') V))
... | nonlocal E' L (β r) p VM with refocus E M VM E' L (β r) p
... | locate E₂ F E₃ refl VE₃M x₂ E₄ x₃ = step** (unwindE M (E₃ [ M ]ᴱ) (extEC E₂ F) E₃ refl VE₃M) (step** (lemmaF' (E₃ [ M ]ᴱ) F E₂ E₄ L _ VE₃M r x₂ (trans (trans (compEC-[]ᴱ (extEC E₂ F) E₃ M) (cong (_[ M ]ᴱ) (compEC-eq (extEC E₂ F) E₃))) (sym x₃))) (thm1 _ _ (compEC' E₂ E₄) (determinism q (ruleEC (compEC' E₂ E₄) r (sym x₃) refl)) O V q'))
