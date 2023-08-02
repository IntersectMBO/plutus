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
open import Algorithmic using (Ctx;_⊢_;ConstrArgs)
open Ctx
open _⊢_

open import Algorithmic.Signature using (_[_]SigTy)

open import Type.BetaNormal using (_⊢Nf⋆_)
open _⊢Nf⋆_

open import Algorithmic.ReductionEC using (Value;BApp;_—→⋆_;_—→_;Error;EC;V-I;ival;E-error;VListZipper;mkVZ;VList)
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

  error :
      Error M
      -------
    → Progress M
```

## Progress for lists 

When processing constructors, we need to know the progress of a list of terms.
A ProgressList is a zipper consisting of:
  * a typed backwards list of constructors already evaluated (vs),
  * Progress on the current term M of type H  
  * a (typed) lists of terms to be evaluated (ts)

```
PList : ∀{ts} → IList (∅ ⊢_) ts → Set 
PList = IIList Progress
           
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
           → ∀ {ls : List (∅ ⊢Nf⋆ *)}{cs : ConstrArgs ∅ ls} (rest : PList cs) -- progress of rest
           → {idx : tot ≣ bs <>> (A ∷ ls)}
           → (x : (itot ≣I ibs <>> (M ∷ cs)) idx)
           → FocusedProgDissect itot
     error :  ∀{tot}{itot : IList (∅ ⊢_) tot}
           → ∀{bs}{ibs : IBwd (∅ ⊢_) bs}(vs : VList ibs) --evaluated
           → ∀{A : ∅ ⊢Nf⋆ *} {M : ∅ ⊢ A} (err : Error M)
           → ∀ {ls : List (∅ ⊢Nf⋆ *)}{cs : ConstrArgs ∅ ls} (rest : PList cs) -- progress of rest
           → {idx : tot ≣ bs <>> (A ∷ ls)} → (iidx : (itot ≣I ibs <>> (M ∷ cs)) idx)
           → FocusedProgDissect itot
progress : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M

-- Walk the list to look for the first term than can make progress or is an error.
progress-focus : ∀{tot}{itot : IList (∅ ⊢_) tot}{bs}{ibs : IBwd (∅ ⊢_) bs}
                  {ls}{cs : IList (∅ ⊢_) ls}{idx : tot ≣ bs <>> ls} 
               → (iidx : (itot ≣I ibs <>> cs) idx)
               → VList ibs
               → PList cs
               → FocusedProgDissect itot
progress-focus x Vs [] = done x Vs
progress-focus x Vs (step st ∷ Ps) = step Vs st Ps x
progress-focus x Vs (done V ∷ Ps) = progress-focus (bubble x) (Vs :< V) Ps
progress-focus x Vs (error e ∷ Ps) = error Vs e Ps x               

progress-List :  ∀ {TS : List (∅ ⊢Nf⋆ *)}
                → (cs : ConstrArgs ∅ TS) 
                → PList cs
progress-List [] = []
progress-List (c ∷ cs) = progress c ∷ progress-List cs

progress-constr : ∀ {n} (e : Fin n)
                    (TSS : Vec.Vec (List (∅ ⊢Nf⋆ *)) n)
                    {cs : ConstrArgs ∅ (lookup TSS e)}
                    (ps : PList cs)
                  → FocusedProgDissect cs
progress-constr e TSS ps = progress-focus start [] ps

progress (ƛ M)        = done (V-ƛ M)
progress (M · M')     with progress M
... | error E-error = step (ruleErr ([] l· M') refl)
... | step (ruleEC E p refl refl) = step (ruleEC (E l· M') p refl refl)
... | step (ruleErr E refl) = step (ruleErr (E l· M') refl)
... | done VM with progress M'
... | step (ruleEC E p refl refl) = step (ruleEC (VM ·r E) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (VM ·r E) refl)
... | error E-error = step (ruleErr (VM ·r []) refl)
progress (.(ƛ M) · M') | done (V-ƛ M) | done VM' =
  step (ruleEC [] (β-ƛ VM') refl refl)
progress (M · M') | done (V-I⇒ b {am = 0} q) | done VM' =
  step (ruleEC [] (β-builtin b M q M' VM') refl refl)
progress (M · M') | done (V-I⇒ b {am = suc _} q) | done VM' =
  done (V-I b (step q VM'))
progress (Λ M)        = done (V-Λ M)
progress (M ·⋆ A / refl) with progress M
... | error E-error = step (ruleErr ([] ·⋆ A / refl) refl)
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
... | error E-error     = step (ruleErr (wrap []) refl)
progress (unwrap M refl) with progress M
... | step (ruleEC E p refl refl) = step (ruleEC (unwrap E / refl) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (unwrap E / refl) refl)
... | done (V-wrap V) = step (ruleEC [] (β-wrap V refl) refl refl)
... | error E-error = step (ruleErr (unwrap [] / refl) refl)
progress (con c refl)      = done (V-con c)
progress (builtin b / refl ) = done (ival b)
progress (error A)    = error E-error
progress (constr i TSS refl cs)  with progress-constr i TSS (progress-List cs)
... | done {bs}{ibs}{idx = idx} x Vs = done (V-constr i 
                                                     TSS 
                                                     refl 
                                                     (trans (sym (lemma<>2 bs [])) (cong ([] <><_) (sym (lem-≣-<>> idx)))) 
                                                     Vs 
                                                     (trans (≡-subst-removable (IList (_⊢_ ∅)) _ _ (ibs <>>I [])) (sym (lem-≣I-<>>1' x))))
... | step Vs (ruleEC E p refl refl) Ps x = 
                     step (ruleEC (constr i TSS refl {getIdx≡I x} (mkVZ Vs (iiGetIdx Ps)) E) 
                           p 
                           (cong (constr i TSS refl) (lem-≣I-<>>1' x)) 
                           refl)
... | step Vs (ruleErr E refl) Ps x = 
             step (ruleErr (constr i TSS refl {getIdx≡I x} (mkVZ Vs (iiGetIdx Ps)) E) 
                    (cong (constr i TSS refl) (lem-≣I-<>>1' x)))
... | error {ibs = ibs} Vs E-error Ps {idx = idx} x = 
               step (ruleErr (constr i TSS refl {idx} (mkVZ Vs _) []) 
                             (cong (constr i TSS refl) (trans (lem-≣I-<>>1' x) refl
                             )))                            
progress (case M cases)  with progress M 
... | step (ruleEC E p refl refl) = step (ruleEC (case cases E) p refl refl)
... | step (ruleErr E refl) = step (ruleErr (case cases E) refl)
... | done (V-constr e TSS refl refl vs refl) = step (ruleEC [] (β-case e TSS refl vs refl cases) refl refl)
... | error E-error = step (ruleErr (case cases []) refl)

{- These definitions seem unused
_↓ : ∀{A} → ∅ ⊢ A → Set
M ↓ = ∃ λ M' → M —→⋆ M'

-- progress in disguise
lemma51 : ∀{A}(M : ∅ ⊢ A)
        → Value M
        ⊎ ∃ λ B
        → ∃ λ (E : EC A B)
        → ∃ λ (L : ∅ ⊢ B)
        → (L ↓ ⊎ Error L)
        × M ≡ E [ L ]ᴱ
lemma51 (ƛ M) = inj₁ (V-ƛ M)
lemma51 (M · M') with lemma51 M
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, E l· M' ,, L ,, p ,, cong (_· M') q)
... | inj₁ VM with lemma51 M'
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, VM ·r E ,, L ,, p ,, cong (M ·_) q)
lemma51 (.(ƛ M) · M') | inj₁ (V-ƛ M)      | inj₁ VM' =
  inj₂ (_ ,, [] ,, _ ,, inj₁ (_ ,, β-ƛ VM') ,, refl)
lemma51 (M · M') | inj₁ (V-I⇒ b {as' = []} p x) | inj₁ VM' =
  inj₂ (_ ,, [] ,, _ ,, inj₁ (_ ,, β-builtin b M p x M' VM') ,, refl)
lemma51 (M · M') | inj₁ (V-I⇒ b {as' = a ∷ as'} p x) | inj₁ VM' =
  inj₁ (V-I b (bubble p) (step p x VM'))
lemma51 (Λ M) = inj₁ (V-Λ M)
lemma51 (M ·⋆ A / refl) with lemma51 M
... | inj₁ (V-Λ M') =
  inj₂ (_ ,, [] ,, M ·⋆ A / refl ,, inj₁ (M' [ A ]⋆ ,, (β-Λ refl)) ,, refl)
... | inj₂ (B ,, E ,, L ,, p ,, q) =
  inj₂ (B ,, E ·⋆ A / refl ,, L ,, p ,, cong (_·⋆ A / refl) q)
lemma51 (M ·⋆ A / refl) | inj₁ (V-IΠ b {as' = []} p x) =
  inj₂ (_ ,, [] ,, _ ,, inj₁ (_ ,, β-builtin⋆ b M p x A refl) ,, refl)
lemma51 (M ·⋆ A / refl) | inj₁ (V-IΠ b {as' = a ∷ as} p x) =
  inj₁ (V-I b (bubble p) (step⋆ p x refl))
lemma51 (wrap A B M) with lemma51 M
... | inj₁ V = inj₁ (V-wrap V)
... | inj₂ (C ,, E ,, L ,, p ,, p') =
  inj₂ (C ,, wrap E ,, L ,, p ,, cong (wrap A B) p')
lemma51 (unwrap M refl) with lemma51 M
... | inj₁ (V-wrap V) =
  inj₂ (_ ,, [] ,, unwrap M refl ,, inj₁ (deval V ,, β-wrap V refl) ,, refl)
... | inj₂ (B ,, E ,, L ,, p ,, p') =
  inj₂ (B ,, unwrap E / refl ,, L ,, p ,, cong (λ x → unwrap x refl) p')
lemma51 (con c) = inj₁ (V-con c)
lemma51 (builtin b / refl) = inj₁ (ival b)
lemma51 (error _) = inj₂ (_ ,, ([] ,, (error _ ,, (inj₂ E-error) ,, refl)))

progress' : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M
progress' M with lemma51 M
... | inj₁ V = done V
... | inj₂ (B ,, E ,, L ,, inj₁ (M' ,, p) ,, refl) = step (ruleEC E p refl refl)
... | inj₂ (B ,, E ,, L ,, inj₂ E-error ,, refl) = step (ruleErr E refl)

-}
 