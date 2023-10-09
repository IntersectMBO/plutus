---
title: CC machine for terms
layout: page
---


```
module Algorithmic.CC where
```

## Imports

```
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;trans;cong) 
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Data.Product using (Σ;_×_;∃) 
                         renaming (_,_ to _,,_)
open import Data.List using (_∷_;[])
open import Data.Vec as Vec using (_∷_;[];lookup)

open import Utils using (*;bubble)
open import Utils.List using ([];_∷_;_:<_;start;bubble;_<><_;lem-≣-<>>;lemma<>2;no-empty-≣-<>>;IBwd)
open import Type using (Ctx⋆;∅)
open import Type.BetaNormal using (_⊢Nf⋆_)
open import Algorithmic using (Ctx;_⊢_;lookupCase;bwdMkCaseType;lemma-bwdfwdfunction')
open Ctx
open _⊢_
open import Algorithmic.Signature using (_[_]SigTy)
open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.ReductionEC using (Value;BApp;EC;Frame;ival;deval;BUILTIN';V-I;VList)
open Value
open BApp
open EC
open Frame

dissect : ∀{A B}(E : EC A B) → A ≡ B ⊎ Σ (∅ ⊢Nf⋆ *) λ C → EC A C × Frame C B
dissect []        = inj₁ refl
dissect (E l· M') with dissect E
... | inj₁ refl           = inj₂ (_ ,, [] ,, -· M')
... | inj₂ (C ,, E' ,, F) = inj₂ (C ,, E' l· M' ,, F)
dissect (VM ·r E) with dissect E
... | inj₁ refl           = inj₂ (_ ,, [] ,, VM ·-)
... | inj₂ (C ,, E' ,, F) = inj₂ (C ,, VM ·r E' ,, F)
dissect (E ·⋆ A / refl) with dissect E
... | inj₁ refl           = inj₂ (_ ,, [] ,,  -·⋆ A)
... | inj₂ (C ,, E' ,, F) = inj₂ (C ,, E' ·⋆ A / refl ,, F)
dissect (wrap E) with dissect E
... | inj₁ refl           = inj₂ (_ ,, [] ,, wrap-)
... | inj₂ (C ,, E' ,, F) = inj₂ (C ,, wrap E' ,, F)
dissect (unwrap E / refl) with dissect E
... | inj₁ refl           = inj₂ (_ ,, [] ,, unwrap-)
... | inj₂ (C ,, E' ,, F) = inj₂ (C ,, unwrap E' / refl ,, F)
dissect (constr i TSS p {tidx} vs ts E) with dissect E 
... | inj₁ refl           = inj₂ (_ ,, ([] ,, (constr- i TSS p {tidx} vs ts)))
... | inj₂ (C ,, E' ,, F) = inj₂ (_ ,, ((constr i TSS p {tidx} vs ts E') ,, F))
dissect (case cs E)  with dissect E 
... | inj₁ refl           = inj₂ (_ ,, ([] ,, (case- cs)))
... | inj₂ (C ,, E' ,, F) = inj₂ (_ ,, ((case cs E') ,, F))

compEC : ∀{A B C} → EC A B → EC B C → EC A C
compEC [] E' = E'
compEC (E  l· M') E' = compEC E E' l· M'
compEC (VM ·r E) E' = VM ·r compEC E E'
compEC (E ·⋆ A / refl) E' = compEC E E' ·⋆ A / refl
compEC (wrap E) E' = wrap (compEC E E')
compEC (unwrap E / refl) E' = unwrap (compEC E E') / refl
compEC (constr i TSS p {tidx} vs ts E) E' = constr i TSS p {tidx} vs ts (compEC E E')
compEC (case cs E) E' = case cs (compEC E E')

extEC : ∀{A B C}(E : EC A B)(F : Frame B C) → EC A C
extEC [] (-· M') = [] l· M'
extEC [] (-·v V) = [] l· deval V
extEC [] (VM ·-) = VM ·r []
extEC [] (-·⋆ A) = [] ·⋆ A / refl
extEC [] wrap- = wrap []
extEC [] unwrap- = unwrap [] / refl
extEC [] (constr- i TSS p {tidx} vs ts) = constr i TSS p {tidx} vs ts []
extEC [] (case- cs) = case cs []
extEC (E l· M') F = extEC E F l· M'
extEC (VM ·r E) F = VM ·r extEC E F
extEC (E ·⋆ A / refl) F = extEC E F ·⋆ A / refl
extEC (wrap E) F = wrap (extEC E F)
extEC (unwrap E / refl) F = unwrap (extEC E F) / refl
extEC (constr i _ p {tidx} vs ts E) F = constr i _ p {tidx} vs ts (extEC E F)
extEC (case cases E) F = case cases (extEC E F)

```

# the machine

```
data State (T : ∅ ⊢Nf⋆ *) : Set where
  _▻_ : {H : ∅ ⊢Nf⋆ *} → EC T H → ∅ ⊢ H → State T
  _◅_ : {H : ∅ ⊢Nf⋆ *} → EC T H → {t : ∅ ⊢ H} → Value t → State T
  □  : {t : ∅ ⊢ T} →  Value t → State T
  ◆   : (A : ∅ ⊢Nf⋆ *)  →  State T

extValueFrames : ∀{T H BS XS} → EC T H → {xs : IBwd (∅ ⊢_) BS} → VList xs → XS ≡ bwdMkCaseType BS H → EC T XS
extValueFrames E [] refl = E
extValueFrames E (vs :< v) refl = extValueFrames (extEC E (-·v v)) vs refl

stepV : ∀{A B }{M : ∅ ⊢ A}(V : Value M)
       → (B ≡ A) ⊎ ∃ (λ C → EC B C × Frame C A)
       → State B
stepV V (inj₁ refl) = □ V
stepV V (inj₂ (_ ,, E ,, (-· N))) = extEC E (V ·-) ▻ N 
stepV V (inj₂ (_ ,, E ,, -·v V')) = stepV V' (inj₂ (_ ,, E ,, (V ·-)))
stepV V (inj₂ (_ ,, E ,, (V-ƛ M ·-))) = E ▻ (M [ deval V ])
stepV V (inj₂ (_ ,, E ,, V-I⇒ b {am = 0} q ·-)) = 
          E ▻ BUILTIN' b (step q V)
stepV V (inj₂ (_ ,, E ,, V-I⇒ b {am = suc am} q ·-)) = 
          E ◅ V-I b (step q V)
stepV (V-Λ M) (inj₂ (_ ,, E ,, -·⋆ A)) = E ▻ (M [ A ]⋆)
stepV (V-IΠ b  {σA = σ} q) (inj₂ (_ ,, E ,, -·⋆ A)) = 
          E ◅ V-I b (step⋆ q refl {σ [ A ]SigTy})
stepV V (inj₂ (_ ,, E ,, wrap-)) = E ◅ V-wrap V
stepV (V-wrap V) (inj₂ (_ ,, E ,, unwrap-)) = E ▻ deval V -- E ◅ V
stepV V (inj₂ (_ ,, E ,, constr- i A p vs ts)) with Vec.lookup A i in eq  
stepV V (inj₂ (_ ,, E ,, constr- i _ refl {tidx} vs ts)) | [] with no-empty-≣-<>> tidx 
... | ()
stepV V (inj₂ (_ ,, E ,, constr- {VS = VS} {H} i _ refl {r}{tidx} vs [])) | _ ∷ _  = 
     E ◅ V-constr i _ (sym eq) (sym (trans (cong ([] <><_) (lem-≣-<>> r)) (lemma<>2 VS (H ∷ [])))) (vs :< V) refl
stepV V (inj₂ (_ ,, E ,, constr- {VS = VS} i A refl {r} vs (t ∷ ts))) | _ ∷ _  
    = extEC E (constr- i A (sym eq) {bubble r} (vs :< V) ts) ▻ t
stepV (V-constr e A refl refl vs x) (inj₂ (_ ,, E ,, case- cs)) = 
    extValueFrames E vs (lemma-bwdfwdfunction' (Vec.lookup A e)) ▻ lookupCase e cs

stepT : ∀{A} → State A → State A
stepT (E ▻ ƛ M) = E ◅ V-ƛ M
stepT (E ▻ (M · M')) = extEC E (-· M') ▻ M
stepT (E ▻ Λ M) = E ◅ V-Λ M
stepT (E ▻ (M ·⋆ A / refl)) = extEC E (-·⋆ A) ▻ M
stepT (E ▻ wrap A B M) = extEC E wrap- ▻ M
stepT (E ▻ unwrap M refl) = extEC E unwrap- ▻ M
stepT (E ▻ constr e A refl z)  with Vec.lookup A e in eq  
stepT (E ▻ constr e A refl []) | [] = E ◅ V-constr e A (sym eq) refl [] refl
stepT (E ▻ constr e A refl (x ∷ xs)) | a ∷ as = 
        extEC E (constr- e A (sym eq) {start} [] xs) ▻  x
stepT (E ▻ case M cases) = extEC E (case- cases) ▻ M
stepT (E ▻ con c refl) = E ◅ V-con c
stepT (E ▻ (builtin b / refl)) = E ◅ ival b
stepT (E ▻ error A) = ◆ A 
stepT (E ◅ V) = stepV V (dissect E)
stepT (□ V) = □ V
stepT (◆ A) = ◆ A 
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
```


