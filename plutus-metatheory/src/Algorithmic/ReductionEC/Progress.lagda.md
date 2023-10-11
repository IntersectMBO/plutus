```
module Algorithmic.ReductionEC.Progress where
```
## Imports

```
open import Data.Nat using (zero;suc)
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec as Vec using ([];_∷_;lookup)
open import Data.Product using (Σ;_×_) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;trans;cong;subst)  

open import Utils using (*;bubble;≡-subst-removable)
open import Utils.List 
open import Type using (Ctx⋆;∅)
open import Algorithmic using (Ctx;_⊢_;ConstrArgs;constr-cong)
open Ctx
open _⊢_

open import Algorithmic.Signature using (_[_]SigTy)

open import Type.BetaNormal using (_⊢Nf⋆_)
open _⊢Nf⋆_

open import Algorithmic.ReductionEC using (Value;BApp;_—→⋆_;_—→_;Error;EC;V-I;ival;E-error;VList)
open Value
open BApp
open _—→⋆_
open _—→_
open EC
```

# Progress proof

```
data Progress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{N : ∅ ⊢ A}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M
```

## Progress for lists 

When processing constructors, we need to know the progress of a list of terms.
A ProgressList is a zipper consisting of:
  * a typed backwards list of constructors already evaluated (vs),
  * Progress on the current term M of type H  
  * a (typed) lists of terms to be evaluated (ts)

```
data FocusedProgDissect : ∀{tot}(itot : IList (∅ ⊢_) tot) → Set 
     where 
     done  : ∀{bs}{ibs : IBwd (∅ ⊢_) bs}{tot}{itot : IList (∅ ⊢_) tot}
              {idx : tot ≣ bs <>> []}
             (x : (itot ≣I ibs <>> []) idx)
             (vs : VList ibs)
        → FocusedProgDissect itot
     step  :  ∀{tot}{itot : IList (∅ ⊢_) tot}
           → ∀{bs}{ibs : IBwd (∅ ⊢_) bs}(vs : VList ibs) --evaluated
           → ∀{A : ∅ ⊢Nf⋆ *} {M : ∅ ⊢ A}{N : ∅ ⊢ A} → (st : M —→ N)  --current step
           → ∀ {ls : List (∅ ⊢Nf⋆ *)}(cs : ConstrArgs ∅ ls) 
           → {idx : tot ≣ bs <>> (A ∷ ls)}
           → (x : (itot ≣I ibs <>> (M ∷ cs)) idx)
           → FocusedProgDissect itot

progress : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M

-- Walk the list to look for the first term than can make progress or is an error.
progress-focus : ∀{tot}{itot : IList (∅ ⊢_) tot}{bs}{ibs : IBwd (∅ ⊢_) bs}
                  {ls}{idx : tot ≣ bs <>> ls} 
               → (cs : IList (∅ ⊢_) ls)
               → (iidx : (itot ≣I ibs <>> cs) idx)
               → VList ibs
               → FocusedProgDissect itot
progress-focus [] x Vs = done x Vs
progress-focus (c ∷ cs) x Vs with progress c 
... | step st = step Vs st cs x
... | done V = progress-focus cs (bubble x) (Vs :< V)

progress (ƛ M)        = done (V-ƛ M)
progress (M · M')     with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (E l· M') p refl refl)
... | step (ruleErr E refl) = step (ruleErr (E l· M') refl)
... | done VM with progress M'
... | step (ruleEC E p refl refl) = step (ruleEC (VM ·r E) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (VM ·r E) refl)
progress (.(ƛ M) · M') | done (V-ƛ M) | done VM' =
  step (ruleEC [] (β-ƛ VM') refl refl)
progress (M · M') | done (V-I⇒ b {am = 0} q) | done VM' =
  step (ruleEC [] (β-builtin b M q M' VM') refl refl)
progress (M · M') | done (V-I⇒ b {am = suc _} q) | done VM' =
  done (V-I b (step q VM'))
progress (Λ M)        = done (V-Λ M)
progress (M ·⋆ A / refl) with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (E ·⋆ A / refl) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (E ·⋆ A / refl) refl)
... | done (V-Λ M') = step (ruleEC [] (β-Λ refl) refl refl)
progress (M ·⋆ A / refl) | done (V-IΠ b {tm = 0} {σA = σ} q) = done (V-I b (step⋆ q refl {σ [ A ]SigTy}))
progress (M ·⋆ A / refl) | done (V-IΠ b {tm = suc _} {σA = σ} q) =
  done (V-I b (step⋆ q refl {σ [ A ]SigTy}))
progress (wrap A B M) with progress M
... | done V            = done (V-wrap V)
... | step (ruleEC E p refl refl) = step (ruleEC (wrap E) p refl refl)
... | step (ruleErr E refl)  = step (ruleErr (wrap E) refl)
progress (unwrap M refl) with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (unwrap E / refl) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (unwrap E / refl) refl)
... | done (V-wrap V) = step (ruleEC [] (β-wrap V refl) refl refl)
progress (con c refl)      = done (V-con c)
progress (builtin b / refl ) = done (ival b)
progress (error A)    = step (ruleErr [] refl)
progress (constr i TSS refl cs)  with progress-focus cs start []
... | done {bs}{ibs}{idx = idx} x Vs = done (V-constr i 
                                                     TSS 
                                                     refl 
                                                     (trans (sym (lemma<>2 bs [])) (cong ([] <><_) (sym (lem-≣-<>> idx)))) 
                                                     Vs 
                                                     (trans (≡-subst-removable (IList (_⊢_ ∅)) _ _ (ibs <>>I [])) (sym (lem-≣I-<>>1' x))))
... | step Vs (ruleEC E p refl refl) cs {idx} x = 
                     step (ruleEC (constr i TSS refl {idx} Vs cs E) 
                           p 
                           (constr-cong (trans (sym (lem-≣-<>> idx)) refl) 
                                         (trans (lem-≣I-<>>1' x) 
                                                (≡-subst-removable (IList (_⊢_ ∅)) (sym (lem-≣-<>> idx)) (trans (sym (lem-≣-<>> idx)) refl) _)))
                           refl)
... | step Vs (ruleErr E refl) cs {idx} x = 
             step (ruleErr (constr i TSS refl {idx} Vs cs E) 
                    (constr-cong (trans (sym (lem-≣-<>> idx)) refl) 
                                 (trans (lem-≣I-<>>1' x) 
                                        (≡-subst-removable (IList (_⊢_ ∅)) (sym (lem-≣-<>> idx)) (trans (sym (lem-≣-<>> idx)) refl) _))) 
                  )
progress (case M cases)  with progress M 
... | step (ruleEC E p refl refl) = step (ruleEC (case cases E) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (case cases E) refl)
... | done (V-constr e TSS refl refl vs refl) = step (ruleEC [] (β-case e TSS refl vs refl cases) refl refl)

 