---
title: CC machine for terms
layout: page
---


```
module Algorithmic.BehaviouralEquivalence.ReductionvsCC where
```

## Imports

```
open import Data.Nat using (suc;zero)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;subst;inspect;cong;sym;trans) 
                                                  renaming ([_] to I[_])
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Data.Product using (Σ;_×_;∃) 
                         renaming (_,_ to _,,_)
open import Data.List using (_∷_;[])
open import Data.Empty using (⊥;⊥-elim)
open import Relation.Nullary using (¬_)

open import Utils using (Kind;*;_⇒_;start;bubble)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_)
open _⊢⋆_
open import Type.BetaNormal using (_⊢Nf⋆_)
open _⊢Nf⋆_
open import Algorithmic using (Ctx;_⊢_)
open Ctx
open _⊢_
open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.ReductionEC
open import Algorithmic.ReductionEC.Determinism

open import Algorithmic.CC

dissect-inj₁ : ∀{A B}(E : EC A B)(p : A ≡ B) → dissect E ≡ inj₁ p
  → subst (λ A → EC A B) p E ≡ []
dissect-inj₁ []                refl refl = refl
dissect-inj₁ (E l· N)          p    q with dissect E
dissect-inj₁ (E l· N)          refl q | inj₁ ()
dissect-inj₁ (VM ·r E)         p    q with dissect E
dissect-inj₁ (VM ·r E)         refl () | inj₁ refl
dissect-inj₁ (E ·⋆ A / refl)   p    q with dissect E
dissect-inj₁ (E ·⋆ A / refl)   p    () | inj₁ refl
dissect-inj₁ (wrap E)          p    q with dissect E
dissect-inj₁ (wrap E)          p    () | inj₁ refl
dissect-inj₁ (unwrap E / refl) p    q with dissect E
dissect-inj₁ (unwrap E / refl) p    () | inj₁ refl

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
dissect-inj₂ (E ·⋆ A / refl) E' F p with dissect E | inspect dissect E
dissect-inj₂ (E ·⋆ A / refl) .[] .(-·⋆ A) refl | inj₁ refl | I[ eq ] =
  cong (_·⋆ A / refl) (dissect-inj₁ E refl eq)
dissect-inj₂ (E ·⋆ A / refl) .(E'' ·⋆ A / refl) .F' refl
  | inj₂ (_ ,, E'' ,, F') | I[ eq ]
  = cong (_·⋆ A / refl) (dissect-inj₂ E E'' F' eq)
dissect-inj₂ (wrap E) E' F p with dissect E | inspect dissect E
dissect-inj₂ (wrap E) .[] .wrap- refl | inj₁ refl | I[ eq ] =
  cong wrap (dissect-inj₁ E refl eq)
dissect-inj₂ (wrap E) .(wrap E'') .F' refl | inj₂ (_ ,, E'' ,, F') | I[ eq ] =
  cong wrap (dissect-inj₂ E E'' F' eq)
dissect-inj₂ (unwrap E / refl) E' F p with dissect E | inspect dissect E
dissect-inj₂ (unwrap E / refl) .[] .unwrap- refl | inj₁ refl | I[ eq ] =
  cong (λ E → unwrap E / refl) (dissect-inj₁ E refl eq)
dissect-inj₂ (unwrap E / refl) .(unwrap E'' / refl) .F' refl
  | inj₂ (_ ,, E'' ,, F') | I[ eq ]
  = cong (λ E → unwrap E / refl) (dissect-inj₂ E E'' F' eq)


compEC' : ∀{A B C} → EC A B → EC B C → EC A C
compEC' E []                 = E
compEC' E (E' l· M')         = compEC' (extEC E (-· M')) E'
compEC' E (VM ·r E')         = compEC' (extEC E (VM ·-)) E'
compEC' E (E' ·⋆ A / refl)   = compEC' (extEC E (-·⋆ A)) E'
compEC' E (wrap E')          = compEC' (extEC E wrap-) E'
compEC' E (unwrap E' / refl) = compEC' (extEC E unwrap-) E'

postulate
  compEC-eq : ∀{A B C}(E : EC C B)(E' : EC B A) → compEC E E' ≡ compEC' E E'

compEC'-[] : ∀{B C}(E : EC B C) → compEC' [] E ≡ E
compEC'-[] E = sym (compEC-eq [] E)

compEC'-extEC : ∀{A B C D}(E : EC A B)(E' : EC B C)(F : Frame C D)
  → compEC' E (extEC E' F) ≡ extEC (compEC' E E') F
compEC'-extEC E []                 (-· N)  = refl
compEC'-extEC E []                 (VM ·-) = refl
compEC'-extEC E []                 (-·⋆ A) = refl
compEC'-extEC E []                 wrap-   = refl
compEC'-extEC E []                 unwrap- = refl
compEC'-extEC E (E' l· N)          F       =
  compEC'-extEC (extEC E (-· N)) E' F
compEC'-extEC E (VM ·r E')         F       =
  compEC'-extEC (extEC E (VM ·-)) E' F
compEC'-extEC E (E' ·⋆ A / refl)   F       =
  compEC'-extEC (extEC E (-·⋆ A)) E' F
compEC'-extEC E (wrap E')          F       =
  compEC'-extEC (extEC E wrap-) E' F
compEC'-extEC E (unwrap E' / refl) F       =
  compEC'-extEC (extEC E unwrap-) E' F

extEC-[]ᴱ : ∀{A B C}(E : EC A B)(F : Frame B C)(M : ∅ ⊢ C) →
  extEC E F [ M ]ᴱ ≡ E [ F [ M ]ᶠ ]ᴱ
extEC-[]ᴱ []                (-· N)  M = refl
extEC-[]ᴱ []                (VL ·-) M = refl
extEC-[]ᴱ []                (-·⋆ A) M = refl
extEC-[]ᴱ []                wrap-   M = refl
extEC-[]ᴱ []                unwrap- M = refl
extEC-[]ᴱ (E l· N)          F       M = cong (_· N) (extEC-[]ᴱ E F M)
extEC-[]ᴱ (VL ·r E)         F       M = cong (deval VL ·_) (extEC-[]ᴱ E F M)
extEC-[]ᴱ (E ·⋆ A / refl)   F       M = cong (_·⋆ A / refl) (extEC-[]ᴱ E F M)
extEC-[]ᴱ (wrap E)          F       M = cong (wrap _ _) (extEC-[]ᴱ E F M)
extEC-[]ᴱ (unwrap E / refl) F       M =
  cong (λ M → unwrap M refl) (extEC-[]ᴱ E F M)

-- 2nd functor law for []ᴱ
compEC-[]ᴱ : ∀{A B C}(E : EC A B)(E' : EC B C)(L : ∅ ⊢ C)
  → E [ E' [ L ]ᴱ ]ᴱ ≡ compEC E E' [ L ]ᴱ
compEC-[]ᴱ []                E' L = refl
compEC-[]ᴱ (E l· M')         E' L = cong (_· M') (compEC-[]ᴱ E E' L)
compEC-[]ᴱ (VM ·r E)         E' L = cong (deval VM ·_) (compEC-[]ᴱ E E' L)
compEC-[]ᴱ (E ·⋆ A / refl)   E' L = cong (_·⋆ A / refl) (compEC-[]ᴱ E E' L)
compEC-[]ᴱ (wrap E)          E' L = cong (wrap _ _) (compEC-[]ᴱ E E' L)
compEC-[]ᴱ (unwrap E / refl) E' L =
  cong (λ M → unwrap M refl) (compEC-[]ᴱ E E' L)
```

```
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
dissect-lemma (E ·⋆ A / refl)   F
  rewrite dissect-lemma E F = refl
dissect-lemma (wrap E)   F
  rewrite dissect-lemma E F = refl
dissect-lemma (unwrap E / refl) F
  rewrite dissect-lemma E F = refl

postulate lemV : ∀{A B}(M : ∅ ⊢ B)(V : Value M)(E : EC A B) → (E ▻ M) -→s (E ◅ V)

{-
lemV .(ƛ M) (V-ƛ M) E = step* refl base
lemV .(Λ M) (V-Λ M) E = step* refl base
lemV .(wrap _ _ _) (V-wrap V) E = step* refl (step** (lemV _ V (extEC E wrap-)) 
                                                     (step* (cong (stepV V) (dissect-lemma E wrap-)) base))
lemV .(con cn) (V-con cn) E = step* refl base
lemV M (V-I⇒ b {am = am} bt) E =  {! am  !}

lemV (M ·⋆ A / x₁) (V-IΠ b x) E = {!   !}
lemV (builtin b₁ / x₁) (V-IΠ b x) E
-}
{-
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
-}


lem62 : ∀{A B C}(L : ∅ ⊢ C)(E : EC A B)(E' : EC B C)
      → (E ▻ (E' [ L ]ᴱ)) -→s (compEC' E E' ▻ L)
lem62 L E []          = base
lem62 L E (E' l· M')  = step* refl (lem62 L (extEC E (-· M')) E')
lem62 L E (VM ·r E')  = step* refl (step**
  (lemV _ VM (extEC E (-· (E' [ L ]ᴱ))))
  (step* (cong (stepV VM) (dissect-lemma E (-· (E' [ L ]ᴱ))))
         (lem62 L (extEC E (VM ·-)) E')))
lem62 L E (E' ·⋆ A / refl)   = step* refl (lem62 L (extEC E (-·⋆ A)) E')
lem62 L E (wrap E')   = step* refl (lem62 L (extEC E wrap-) E')
lem62 L E (unwrap E' / refl) = step* refl (lem62 L (extEC E unwrap-) E')


{-# TERMINATING #-}
unwindVE : ∀{A B C}(M : ∅ ⊢ A)(N : ∅ ⊢ B)(E : EC C B)(E' : EC B A)
      → N ≡ E' [ M ]ᴱ
      → (VM : Value M)
      → (VN : Value N)
      → (compEC' E E' ◅ VM) -→s (E ◅ VN)
unwindVE A B E E' refl VM VN with dissect E' | inspect dissect E'
... | inj₁ refl | I[ eq ] rewrite dissect-inj₁ E' refl eq rewrite uniqueVal A VM VN = base
... | inj₂ (_ ,, E'' ,, (V-ƛ M ·-)) | I[ eq ] rewrite dissect-inj₂ E' E'' (V-ƛ M ·-) eq 
    = ⊥-elim (lemVβ (lemVE _ E'' (subst Value (extEC-[]ᴱ E'' (V-ƛ M ·-) A) VN)))
... | inj₂ (_ ,, E'' ,, (V-I⇒ b {am = zero} x ·-)) | I[ eq ] rewrite dissect-inj₂ E' E'' (V-I⇒ b x ·-) eq 
    = ⊥-elim (valred (lemVE _ E'' (subst Value (extEC-[]ᴱ E'' (V-I⇒ b x ·-) A) VN)) (β-builtin b (deval (V-I⇒ b x)) x A VM))
... | inj₂ (_ ,, E'' ,, (V-I⇒ b {am = suc am} x ·-)) | I[ eq ]  rewrite dissect-inj₂ E' E'' (V-I⇒ b x ·-) eq  
    = step* (trans (cong (λ E → stepV VM (dissect E)) (compEC'-extEC E E'' (V-I⇒ b x ·-))) (cong (stepV VM) (dissect-lemma (compEC' E E'') (V-I⇒ b x ·-)))) 
            (unwindVE _ _ E E'' (extEC-[]ᴱ E'' (V-I⇒ b x ·-) A) (V-I b (step x VM)) VN)
unwindVE .(Λ M) .(E' [ Λ M ]ᴱ) E E' refl (V-Λ M) VN | inj₂ (_ ,, E'' ,, -·⋆ C) | I[ eq ] rewrite dissect-inj₂ E' E'' (-·⋆ C) eq 
 = ⊥-elim (lemVβ⋆ (lemVE _ E'' (subst Value (extEC-[]ᴱ E'' (-·⋆ C) (Λ M)) VN)))
unwindVE A .(E' [ A ]ᴱ) E E' refl (V-IΠ b x) VN | inj₂ (_ ,, E'' ,, -·⋆ C) | I[ eq ] rewrite dissect-inj₂ E' E'' (-·⋆ C) eq  
 = step* (trans (cong (λ E → stepV _ (dissect E)) (compEC'-extEC E E'' (-·⋆ C))) (cong (stepV (V-IΠ b x)) (dissect-lemma (compEC' E E'') (-·⋆ C)))) (unwindVE _ _ E E'' (extEC-[]ᴱ E'' (-·⋆ C) A) (V-I b (step⋆ x refl refl)) VN) 
... | inj₂ (_ ,, E'' ,, wrap-) | I[ eq ] rewrite dissect-inj₂ E' E'' wrap- eq 
    = step* (trans (cong (λ E → stepV VM (dissect E)) (compEC'-extEC E E'' wrap-)) (cong (stepV VM) (dissect-lemma (compEC' E E'') wrap-))) (unwindVE _ _ E E'' (extEC-[]ᴱ E'' wrap- A) (V-wrap VM) VN)
unwindVE _ _ E E' refl (V-wrap VM) VN | inj₂ (_ ,, E'' ,, unwrap-) | I[ eq ] rewrite dissect-inj₂ E' E'' unwrap- eq 
    = ⊥-elim (valred (lemVE _ E'' (subst Value (extEC-[]ᴱ E'' unwrap- (deval (V-wrap VM))) VN)) (β-wrap VM refl))
unwindVE .(ƛ M) .(E' [ ƛ M ]ᴱ) E E' refl (V-ƛ M) VN | inj₂ (_ ,, E'' ,, (-· M')) | I[ eq ] rewrite dissect-inj₂ E' E'' (-· M') eq = ⊥-elim (lemVβ (lemVE (ƛ M · M') E'' (subst Value (extEC-[]ᴱ E'' (-· M') (ƛ M)) VN)))
unwindVE A .(E' [ A ]ᴱ) E E' refl V@(V-I⇒ b {am = zero} x) VN | inj₂ (_ ,, E'' ,, (-· M')) | I[ eq ] rewrite dissect-inj₂ E' E'' (-· M') eq 
  = ⊥-elim (valred (lemVE _ E'' (subst Value (extEC-[]ᴱ E'' (-· M') A) VN)) (β-builtin b A x M' (lemVE _ (extEC E'' (V ·-)) (subst Value (trans (extEC-[]ᴱ E'' (-· M') A) (sym (extEC-[]ᴱ E'' (V ·-) M'))) VN))))
unwindVE A .(E' [ A ]ᴱ) E E' refl V@(V-I⇒ b {am = suc am} x) VN | inj₂ (_ ,, E'' ,, (-· M')) | I[ eq ] rewrite dissect-inj₂ E' E'' (-· M') eq 
  = step* (trans (cong (λ E → stepV (V-I⇒ b x) (dissect E)) (compEC'-extEC E E'' (-· M'))) (cong (stepV (V-I⇒ b x)) (dissect-lemma (compEC' E E'') (-· M')))) 
             (step** (lemV M' (lemVE M' (extEC E'' (V-I⇒ b x ·-)) (subst Value (trans (extEC-[]ᴱ E'' (-· M') A) (sym (extEC-[]ᴱ E'' (V-I⇒ b x ·-) M'))) VN)) (extEC (compEC' E E'') (V-I⇒ b x ·-))) 
                     (step* (cong (stepV _) (dissect-lemma (compEC' E E'') (V-I⇒ b x ·-))) 
                            ((unwindVE (A · M') _ E E'' (extEC-[]ᴱ E'' (-· M') A) (V-I b (step x (lemVE M' (extEC E'' (V-I⇒ b x ·-))  
                              (subst Value (trans (extEC-[]ᴱ E'' (-· M') A)  (sym (extEC-[]ᴱ E'' (V-I⇒ b x ·-) M'))) VN)))) VN))))  

unwindE : ∀{A B C}(M : ∅ ⊢ A)(N : ∅ ⊢ B)(E : EC C B)(E' : EC B A)
      → N ≡ E' [ M ]ᴱ
      → (VN : Value N)
      → (compEC' E E' ▻ M) -→s (E ◅ VN)

unwindE M N E E' refl VN = step**
  (lemV M _ (compEC' E E'))
  (unwindVE M N E E' refl (lemVE M E' VN) VN)


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
... | refl ,, X ,, refl = local (compEC E E'') _ r (trans q (cong (_[ _ ]ᴱ) X)) q'
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
  ⊥-elim (valredex (lemVE L E₁ (subst Value p VM)) r)
refocus E M VM E₁ L r p | inj₂ (_ ,, E₂ ,, (-· N)) | I[ eq ] with rlemma51! N
refocus E M VM E₁ L r p | inj₂ (C ,, E₂ ,, (-· N)) | I[ eq ] | step ¬VN E₃ r' p' U with rlemma51! (E [ M ]ᴱ)
... | done VEM = ⊥-elim (valredex (lemVE _ E₁ (subst Value p VEM)) r)
... | step ¬VEM E₄ r'' p'' U'  rewrite dissect-inj₂ E E₂ (-· N) eq with U' _ p r
... | refl ,, _ ,, refl with U' (compEC' (extEC E₂ (VM ·-)) E₃) (trans (extEC-[]ᴱ E₂ (-· N) M) (trans (trans (cong (λ N →  E₂ [ M · N ]ᴱ) p') (sym (extEC-[]ᴱ E₂ (VM ·-) _))) (trans (compEC-[]ᴱ (extEC E₂ (VM ·-)) E₃ _) (cong (λ E → E [ _ ]ᴱ) (compEC-eq (extEC E₂ (VM ·-)) E₃))))) r'
... | refl ,, refl ,, refl = locate E₂ (-· N) [] refl VM (lemV'· (λ VN → valredex (lemVE L _ (subst Value p' VN)) r')) ((VM EC.·r E₃)) (sym (trans (extEC-[]ᴱ E₂ (-· N) M) (trans (trans (cong (λ N →  E₂ [ M · N ]ᴱ) p') (sym (extEC-[]ᴱ E₂ (VM ·-) _))) (trans (compEC-[]ᴱ (extEC E₂ (VM ·-)) E₃ _) (cong (λ E → E [ _ ]ᴱ) (compEC-eq (extEC E₂ (VM ·-)) E₃))))))
-- same proof twice
refocus E .(ƛ M) (V-ƛ M) E₁ L r p | inj₂ (_ ,, E₂ ,, (-· N)) | I[ eq ] | done VN with rlemma51! (E [ ƛ M ]ᴱ)
... | done VEƛM = ⊥-elim (valredex (lemVE L E₁ (subst Value p VEƛM)) r)
... | step ¬VEƛM E₃ x₁ x₂ U rewrite dissect-inj₂ E E₂ (-· N) eq with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (-· N) (ƛ M)) (β (β-ƛ VN))
... | refl ,, refl ,, refl = locate E₂ (-· N) [] refl (V-ƛ M) (λ V → lemVβ V) [] (sym (extEC-[]ᴱ E₂ (-· N) (ƛ M)))
refocus E M V@(V-I⇒ b {am = 0} x) E₁ L r p | inj₂ (_ ,, E₂ ,, (-· N)) | I[ eq ] | done VN with rlemma51! (E [ M ]ᴱ)
... | done VEM =
  ⊥-elim (valredex (lemVE L E₁ (subst Value p VEM)) r)
... | step ¬VEM E₃ x₂ x₃ U rewrite dissect-inj₂ E E₂ (-· N) eq with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (-· N) M) (β (β-builtin b M x N VN))
... | refl ,, refl ,, refl = locate E₂ (-· N) [] refl V (λ V → valred V (β-builtin b M x N VN)) [] (sym (extEC-[]ᴱ E₂ (-· N) M))
refocus E M (V-I⇒ b {am = suc _} x) E₁ L r p | inj₂ (_ ,, E₂ ,, (-· N)) | I[ eq ] | done VN rewrite dissect-inj₂ E E₂ (-· N) eq with refocus E₂ (M · N) (V-I b (step x VN)) E₁ L r (trans (sym (extEC-[]ᴱ E₂ (-· N) M)) p)
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
  ⊥-elim (valredex (lemVE L E₁ (subst Value p VEM)) r)
... | step ¬VEM E₃ x₁ x₂ U  rewrite dissect-inj₂ E E₂ (V ·-) eq
  with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (V ·-) M) (β (β-ƛ VM))
... | refl ,, refl ,, refl = locate E₂ (V ·-) [] refl VM (λ V → lemVβ V) [] (sym (extEC-[]ᴱ E₂ (V ·-) M))
refocus E M VM E₁ L r p | inj₂ (_ ,, E₂ ,, (V@(V-I⇒ b {am = 0} x) ·-)) | I[ eq ] with rlemma51! (E [ M ]ᴱ)
... | done VEM =
  ⊥-elim (valredex (lemVE L E₁ (subst Value p VEM)) r)
... | step ¬VEM E₃ x₁ x₂ U rewrite dissect-inj₂ E E₂ (V ·-) eq
  with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (V ·-) M) (β (β-builtin b _ x M VM))
... | refl ,, refl ,, refl = locate E₂ (V ·-) [] refl VM (λ V → valred V (β-builtin b _ x M VM)) [] (sym (extEC-[]ᴱ E₂ (V ·-) M))
refocus E M VM E₁ L r p | inj₂ (_ ,, E₂ ,, _·- {t = t} (V@(V-I⇒ b {am = suc _} x))) | I[ eq ] rewrite dissect-inj₂ E E₂ (V ·-) eq with refocus E₂ (t · M) (V-I b (step x VM)) E₁ L r (trans (sym (extEC-[]ᴱ E₂ (V ·-) M)) p)
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
... | done VEƛM = ⊥-elim (valredex (lemVE L E₁ (subst Value p VEƛM)) r)
... | step ¬VEƛM E₃ x₁ x₂ U rewrite dissect-inj₂ E E₂ (-·⋆ A) eq with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ (-·⋆ A) (Λ M)) (β (β-Λ refl))
... | refl ,, refl ,, refl = locate E₂ (-·⋆ A) [] refl (V-Λ M) (λ V → lemVβ⋆ V) [] (sym (extEC-[]ᴱ E₂ (-·⋆ A) (Λ M)))
refocus E M (V-IΠ b x) E₁ L r p | inj₂ (_ ,, E₂ ,, -·⋆ A) | I[ eq ] rewrite dissect-inj₂ E E₂ (-·⋆ A) eq with refocus E₂ (M ·⋆ A / refl) (V-I b (step⋆ x refl refl)) E₁ L r (trans (sym (extEC-[]ᴱ E₂ (-·⋆ A) M)) p)
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
  ⊥-elim (valredex (lemVE L E₁ (subst Value p VEM)) r)
... | step ¬VEM E₃ x₁ x₂ U rewrite dissect-inj₂ E E₂ unwrap- eq
  with U E₁ p r
... | refl ,, refl ,, refl with U E₂ (extEC-[]ᴱ E₂ unwrap- (wrap A B M)) (β (β-wrap VM refl))
... | refl ,, refl ,, refl = locate E₂ unwrap- [] refl (V-wrap VM) (λ V → valred V (β-wrap VM refl)) [] (sym (extEC-[]ᴱ E₂ unwrap- (wrap A B M)))


lem-→s⋆ : ∀{A B}(E : EC A B){L N} →  L —→⋆ N -> (E ▻ L) -→s (E ▻ N)
lem-→s⋆ E (β-ƛ V) = step*
  refl
  (step** (lemV _ (V-ƛ _) (extEC E (-· _)))
          (step* (cong (stepV (V-ƛ _)) (dissect-lemma E (-· _)))
                 (step** (lemV _ V (extEC E (V-ƛ _ ·-)))
                         (step* (cong (stepV V) (dissect-lemma E (V-ƛ _ ·-)))
                                base))))
lem-→s⋆ E (β-Λ refl) = step*
  refl
  (step** (lemV _ (V-Λ _) (extEC E (-·⋆ _)))
          (step* (cong (stepV (V-Λ _)) (dissect-lemma E (-·⋆ _)))
                 base))
lem-→s⋆ E (β-wrap V refl) = step*
  refl
  (step** (lemV _ (V-wrap V) (extEC E unwrap-))
          (step* (cong (stepV (V-wrap V)) (dissect-lemma E unwrap-))
                 base))
lem-→s⋆ E (β-builtin b t bt u vu) = step* 
   refl 
   (step** (lemV t (V-I⇒ b bt) (extEC E (-· u)))
           (step* (cong (stepV (V-I⇒ b bt)) (dissect-lemma E (-· u))) 
                  (step** (lemV u vu (extEC E (V-I⇒ b bt ·-))) 
                          (step* (cong (stepV vu) (dissect-lemma E (V-I⇒ b bt ·-))) base)))) 

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
... | done VMN = ⊥-elim (¬VFM (lemVE (M · E₁ [ _ ]ᴱ) E (subst Value (extEC-[]ᴱ E (-· (E₁ [ _ ]ᴱ)) M) VMN)))
... | step ¬VEMN E₂ x₆ x₇ U' with U' (compEC' E E') x₁ (β r)
... | refl ,, refl ,, refl with U' (compEC' (extEC E (V ·-)) E₁) (trans (extEC-[]ᴱ E (-· N) M) (trans (trans (sym (extEC-[]ᴱ E (V ·-) _)) (compEC-[]ᴱ (extEC E (V ·-)) E₁ _)) (cong (_[ _ ]ᴱ) (compEC-eq (extEC E (V ·-)) E₁)))) x₃
... | refl ,, x ,, refl rewrite x = step* (cong (stepV V) (dissect-lemma E (-· (E₁ [ L ]ᴱ)))) (step** (lem62 L (extEC E (V ·-)) E₁) (lem-→s⋆ _ r))
lemmaF' .(ƛ M) (-· N) E E' L L' (V-ƛ M) r ¬VFM x₁ | done VN with rlemma51! (extEC E (-· N) [ ƛ M ]ᴱ)
... | done VƛMN = ⊥-elim (lemVβ (lemVE _ E (subst Value (extEC-[]ᴱ E (-· N) (ƛ M)) VƛMN)))
... | step ¬VƛMN E₁ x₂ x₃ U with U E (extEC-[]ᴱ E (-· N) (ƛ M)) (β (β-ƛ VN))
... | refl ,, refl ,, refl with U (compEC' E E') x₁ (β r)
lemmaF' .(ƛ M) (-· N) E E' L _ (V-ƛ M) (β-ƛ _) ¬VFM x₁ | done VN | step ¬VƛMN E₁ x₂ x₃ U | refl ,, refl ,, refl | refl ,, x ,, refl = step*
  (cong (stepV (V-ƛ M)) (dissect-lemma E (-· N)))
  (step** (lemV N VN (extEC E (V-ƛ M ·-)))
          (step* (cong (stepV VN) (dissect-lemma E (V-ƛ M ·-))) (subst (λ E' →  (E ▻ (M [ N ])) -→s (E' ▻ (M [ N ]))) x base)))

lemmaF' M (-· N) E E' L L' V@(V-I⇒ b {am = 0} x) r ¬VFM x₁ | done VN with rlemma51! (extEC E (-· N) [ M ]ᴱ)
... | done VMN = ⊥-elim (valred (lemVE _ E (subst Value (extEC-[]ᴱ E (-· N) M) VMN)) (β-builtin b M x N VN))
... | step ¬VMN E₁ x₃ x₄ U with U E (extEC-[]ᴱ E (-· N) M) (β (β-builtin b M x N VN))
... | refl ,, refl ,, refl with U (compEC' E E') x₁ (β r)
lemmaF' M (-· N) E E' .(M · N) _ V@(V-I⇒ b {am = 0} x) (β-builtin b₁ .M bt .N vu) ¬VFM x₁ | done VN | step ¬VMN E x₃ x₄ U | refl ,, refl ,, refl | refl ,, q ,, refl with uniqueVal N VN vu | uniqueVal M V (V-I⇒ b₁ bt)
... | refl | refl = step*
  (cong (stepV V) (dissect-lemma E (-· N)))
  (step** (lemV N VN (extEC E (V ·-)))
          (step* (cong (stepV VN) (dissect-lemma E (V ·-))) (subst (λ E' → (E ▻ _) -→s (E' ▻ _)) q base)))
lemmaF' M (-· N) E E' L L' (V-I⇒ b {am = suc _} x) r ¬VFM x₁ | done VN =
  ⊥-elim (¬VFM (V-I b (step x VN)))

lemmaF' M (VN ·-) E E' L L' V x x₁ x₂ with rlemma51! (extEC E (VN ·-) [ M ]ᴱ)
... | done VNM = ⊥-elim (x₁ (lemVE (deval VN · M) E (subst Value (extEC-[]ᴱ E (VN ·-) M) VNM)))
lemmaF' M (V-ƛ M₁ ·-) E E' L L' V x x₁ x₂ | step ¬VƛM₁M E₁ x₃ x₄ U with U (compEC' E E') x₂ (β x)
... | refl ,, refl ,, refl with U E (extEC-[]ᴱ E (V-ƛ M₁ ·-) M) (β (β-ƛ V))
lemmaF' M (V-ƛ M₁ ·-) E E' L L' V (β-ƛ _) x₁ x₂ | step ¬VƛM₁M E₁ x₃ x₄ U | refl ,, refl ,, refl | refl ,, q ,, refl = step* (cong (stepV V) (dissect-lemma E (V-ƛ M₁ ·-))) ((subst (λ E' → (E ▻ _) -→s (E' ▻ _)) (sym q) base))
lemmaF' M (V-I⇒ b {am = suc _} x₃ ·-) E E' L L' V x x₁ x₂ | step ¬VNM E₁ x₄ x₅ x₆ = ⊥-elim (x₁ (V-I b (step x₃ V)))
lemmaF' M (VN@(V-I⇒ b {am = 0} x₃) ·-) E E' L L' V x x₁ x₂ | step ¬VNM E₁ x₄ x₅ U with U E (extEC-[]ᴱ E (VN ·-) M) (β (β-builtin b _ x₃ M V))
... | refl ,, refl ,, refl with U (compEC' E E') x₂ (β x)
lemmaF' M (VN@(V-I⇒ b {am = 0} x₃) ·-) E E' L L' V x x₁ x₂ | step ¬VNM E₁ x₄ x₅ U | refl ,, refl ,, refl | refl ,, q ,, refl rewrite determinism⋆ x (β-builtin b _ x₃ M V) = step*
  (cong (stepV V) (dissect-lemma E (VN ·-)))
  (subst (λ E' → (E ▻ _) -→s (E' ▻ _)) q base)
lemmaF' M (-·⋆ A) E E' L L' V x x₁ x₂ with rlemma51! (extEC E (-·⋆ A) [ M ]ᴱ)
... | done VM·⋆A = ⊥-elim (x₁ (lemVE (M ·⋆ A / refl) E (subst Value (extEC-[]ᴱ E (-·⋆ A) M) VM·⋆A)))
lemmaF' M (-·⋆ A) E E' L L' V x x₁ x₂ | step ¬VM·⋆A E₁ x₃ x₄ U with U (compEC' E E') x₂ (β x)
lemmaF' .(Λ M) (-·⋆ A) E E' L L' (V-Λ M) x x₁ x₂ | step ¬VM·⋆A .(compEC' E E') x₃ x₄ U | refl ,, refl ,, refl with U E (extEC-[]ᴱ E (-·⋆ A) (Λ M)) (β (β-Λ refl))
lemmaF' .(Λ M) (-·⋆ A) E E' L L' (V-Λ M) x x₁ x₂ | step ¬VM·⋆A .(compEC' E E') x₃ x₄ U | refl ,, refl ,, refl | refl ,, q ,, refl rewrite determinism⋆ x (β-Λ refl) = step*
  (cong (stepV (V-Λ M)) (dissect-lemma E (-·⋆ A)))
  (subst (λ E' → (E ▻ _) -→s (E' ▻ _)) (sym q) base)
lemmaF' M (-·⋆ A) E E' L L' (V-IΠ b x₅) x x₁ x₂ | step ¬VM·⋆A .(compEC' E E') x₃ x₄ U | refl ,, refl ,, refl = ⊥-elim (x₁ (V-I b (step⋆ x₅ refl refl)))
lemmaF' M wrap- E E' L L' V x x₁ x₂ = ⊥-elim (x₁ (V-wrap V))
lemmaF' (wrap A B M) unwrap- E E' L L' (V-wrap V) x x₁ x₂ with rlemma51! (extEC E unwrap- [ wrap A B M ]ᴱ)
... | done VEunwrapwrapV = ⊥-elim (x₁ (lemVE (unwrap (wrap A B M) refl) E (subst Value (extEC-[]ᴱ E unwrap- (wrap A B M)) VEunwrapwrapV)))
... | step ¬VEunwrapwrapV E₁ x₄ x₅ U with U (compEC' E E') x₂ (β x)
lemmaF' (wrap A B M) unwrap- E E' L L' (V-wrap V) x x₁ x₂ | step ¬VEunwrapwrapV E₁ x₄ x₅ U | refl ,, refl ,, refl with U E (extEC-[]ᴱ E unwrap- (wrap A B M)) (β (β-wrap V refl))
lemmaF' (wrap A B M) unwrap- E E' L L' (V-wrap V) x x₁ x₂ | step ¬VEunwrapwrapV E₁ x₄ x₅ U | refl ,, refl ,, refl | refl ,, q ,, refl rewrite determinism⋆ x (β-wrap V refl) = step*
  (cong (stepV (V-wrap V)) (dissect-lemma E unwrap-))
  (subst (λ E' → (E ▻ _) -→s (E' ▻ _)) (sym q) base)

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

thm2 : ∀{A}(M N : ∅ ⊢ A)(V : Value N) → M —↠ N → ([] ▻ M) -→s ([] ◅ V)
thm2 M N V p = thm1 M M [] refl N V p

box2box : ∀{A}(M M' : ∅ ⊢ A)(V : Value M)(V' : Value M')
  → □ V -→s □ V' → Σ (M ≡ M') λ p → subst Value p V ≡ V'
box2box M .M V .V base = refl ,, refl
box2box M M' V V' (step* refl p) = box2box M M' V V' p

diamond2box : ∀{A B}(M : ∅ ⊢ B)(V : Value M)
  → ◆ A -→s □ V → ⊥
diamond2box M V (step* refl p) = diamond2box M V p

thm1b : ∀{A B}(M : ∅ ⊢ A)(M' : ∅ ⊢ B)(E : EC B A)
  → M' ≡ E [ M ]ᴱ → (N : ∅ ⊢ B)(V : Value N)
  → (E ▻ M) -→s (□ V)
  → M' —↠ N

thm1bV : ∀{A B}(M : ∅ ⊢ A)(W : Value M)(M' : ∅ ⊢ B)(E : EC B A)
  → M' ≡ E [ M ]ᴱ → (N : ∅ ⊢ B)(V : Value N)
  → (E ◅ W) -→s (□ V)
  → M' —↠ N

thm1b (ƛ M) M' E p N V (step* refl q) = thm1bV (ƛ M) (V-ƛ M) M' E p N V q
thm1b (M · M₁) M' E p N V (step* refl q) =
  thm1b M _ (extEC E (-· M₁)) (trans p (sym (extEC-[]ᴱ E (-· M₁) M))) N V q
thm1b (Λ M) M' E p N V (step* refl q) = thm1bV (Λ M) (V-Λ M) M' E p N V q
thm1b (M ·⋆ A / refl) M' E p N V (step* refl q) =
  thm1b M _ (extEC E (-·⋆ A)) (trans p (sym (extEC-[]ᴱ E (-·⋆ A) M))) N V q
thm1b (wrap A B M) M' E p N V (step* refl q) =
  thm1b M _ (extEC E wrap-) (trans p (sym (extEC-[]ᴱ E wrap- M))) N V q
thm1b (unwrap M refl) M' E p N V (step* refl q) =
  thm1b M _ (extEC E unwrap-) (trans p (sym (extEC-[]ᴱ E unwrap- M))) N V q
thm1b (con c) M' E p N V (step* refl q) = thm1bV (con c) (V-con c) M' E p N V q
thm1b (builtin b / refl) M' E p N V (step* refl q) =
  thm1bV (builtin b / refl) (ival b) M' E p N V q
thm1b (error _) M' E p N V (step* refl q) = ⊥-elim (diamond2box N V q)

thm1bV M W M' E p N V (step* x q) with dissect E | inspect dissect E
thm1bV M W M' E p N V (step* refl q) | inj₂ (_ ,, E' ,, (-· N')) | I[ eq ]
  rewrite dissect-inj₂ E E' (-· N') eq =
  thm1b N'
        M'
        (extEC E' (W ·-))
        (trans p (trans (extEC-[]ᴱ E' (-· N') M)
                        (sym (extEC-[]ᴱ E' (W ·-) N'))))
        N
        V
        q
thm1bV M W M' E p N V (step* refl q) | inj₂ (_ ,, E' ,, (V-ƛ M₁ ·-)) | I[ eq ]
  rewrite dissect-inj₂ E E' (V-ƛ M₁ ·-) eq = trans—↠
    (ruleEC E' (β-ƛ W) (trans p (extEC-[]ᴱ E' (V-ƛ M₁ ·-) M)) refl)
    (thm1b (M₁ [ M ]) _ E' refl N V q)
thm1bV M W M' E p N V (step* refl q) | inj₂ (_ ,, E' ,, (VI@(V-I⇒ b {am = 0} x₁) ·-)) | I[ eq ] rewrite dissect-inj₂ E E' (VI ·-) eq = trans—↠
  (ruleEC E' (β-builtin b _ x₁ M W) (trans p (extEC-[]ᴱ E' (VI ·-) M)) refl)
  (thm1b (BUILTIN' b (step x₁ W)) _ E' refl N V q)
thm1bV M W M' E p N V (step* refl q) | inj₂ (_ ,, E' ,, (VI@(V-I⇒ b {am = suc _} x₁) ·-)) | I[ eq ] rewrite dissect-inj₂ E E' (VI ·-) eq =
  thm1bV (_ · M)
         (V-I b (step x₁ W))
         M'
         E'
         (trans p (extEC-[]ᴱ E' (VI ·-) M))
         N
         V
         q
thm1bV .(Λ M) (V-Λ M) M' E p N V (step* refl q) | inj₂ (_ ,, E' ,, -·⋆ A) | I[ eq ] rewrite dissect-inj₂ E E' (-·⋆ A) eq = trans—↠ (ruleEC E' (β-Λ refl) (trans p (extEC-[]ᴱ E' (-·⋆ A) (Λ M))) refl) (thm1b (M [ A ]⋆) _ E' refl N V q)
thm1bV M (V-IΠ b x₁) M' E p N V (step* refl q) | inj₂ (_ ,, E' ,, -·⋆ A) | I[ eq ] rewrite dissect-inj₂ E E' (-·⋆ A) eq =
  thm1bV (M ·⋆ A / refl)
         (V-I b (step⋆ x₁ refl refl))
         M'
         E'
         (trans p (extEC-[]ᴱ E' (-·⋆ A) M))
         N
         V
         q

thm1bV M W M' E p N V (step* refl q) | inj₂ (_ ,, E' ,, wrap-) | I[ eq ] rewrite dissect-inj₂ E E' wrap- eq = thm1bV (wrap _ _ M) (V-wrap W) _ E' (trans p (extEC-[]ᴱ E' wrap- M)) N V q
thm1bV .(wrap _ _ _) (V-wrap W) M' E p N V (step* refl q) | inj₂ (_ ,, E' ,, unwrap-) | I[ eq ] rewrite dissect-inj₂ E E' unwrap- eq = trans—↠ (ruleEC E' (β-wrap W refl) (trans p (extEC-[]ᴱ E' unwrap- _)) refl) (thm1b _ _ E' refl N V q)
thm1bV M W M' E refl N V (step* refl q) | inj₁ refl | I[ eq ] rewrite dissect-inj₁ E refl eq with box2box M N W V q
... | refl ,, refl = refl—↠

thm2b : ∀{A}(M N : ∅ ⊢ A)(V : Value N) → ([] ▻ M) -→s (□ V) → M —↠ N
thm2b M N V p = thm1b M M [] refl N V p