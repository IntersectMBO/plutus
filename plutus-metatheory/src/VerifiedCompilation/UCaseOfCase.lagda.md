```
module VerifiedCompilation.UCaseOfCase where

```

## Imports

```
open import Data.Nat using (ℕ;zero;suc)
open import Data.Empty using (⊥)
open import Scoped using (ScopedTm; Weirdℕ)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Untyped.CEK using (BApp; fullyAppliedBuiltin; BUILTIN; stepper; State; Stack)
open import Evaluator.Base using (maxsteps)
open import Builtin using (Builtin; ifThenElse)
open import Data.List using (List; zip; [_])
open import Utils as U using (Maybe;nothing;just;Either)
open import RawU using (TmCon)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
```

## Translation Relation

This compiler stage only applies to the very specific case where an `IfThenElse` builtin exists in a `case` expression.
It moves the `IfThenElse` outside and creates two `case` expressions with each of the possible lists of cases. 

This translation relation has a constructor for the specific case, and then inductive constructors for everything else
to traverse the ASTs.

```
data _⊢̂_⊳̂_ (X : Set) : (X ⊢) → (X ⊢) → Set where
--   refl : ∀ {X : Set} {x : X ⊢} → X ⊢̂ x ⊳̂ x
   caseofcase : ∀ {b : X ⊢} {tn tn' fn fn' : ℕ} {alts alts' tt ft tt' ft' : List (X ⊢)} 
                → All (λ altpair → X ⊢̂ (proj₁ altpair) ⊳̂ (proj₂ altpair)) (zip alts alts') -- recursive translation for the other case patterns 
                → All (λ altpair → X ⊢̂ (proj₁ altpair) ⊳̂ (proj₂ altpair)) (zip tt tt') -- recursive translation for the true branch
                → All (λ altpair → X ⊢̂ (proj₁ altpair) ⊳̂ (proj₂ altpair)) (zip ft ft') -- recursive translation for the false branch
                ----------------------
                → X ⊢̂
                       (case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
                       ⊳̂ ((((force (builtin ifThenElse)) · b) · (case (constr tn' tt') alts')) · (case (constr tn' tt') alts'))
   var : ∀ {x : X} → X ⊢̂ (` x) ⊳̂ (` x) 
   ƛ   : ∀ {x x' : Maybe X ⊢}
           → Maybe X ⊢̂ x ⊳̂ x'
           ----------------------
           →  X ⊢̂ ƛ x ⊳̂ ƛ x' 
   _·_ : ∀ {f t f' t' : X ⊢} → (X ⊢̂ f ⊳̂ f') → (X ⊢̂ t ⊳̂ t') → (X ⊢̂ (f · t) ⊳̂ (f' · t'))
   force : ∀ {t t' : X ⊢} → X ⊢̂ t ⊳̂ t' → X ⊢̂ force t ⊳̂ force t'  
   delay : ∀ {t t' : X ⊢} → X ⊢̂ t ⊳̂ t' → X ⊢̂ delay t ⊳̂ delay t'  
   con : ∀ {tc : TmCon} → X ⊢̂ con tc ⊳̂ con tc
   constr : ∀ {xs xs' : List (X ⊢)} { n : ℕ }
                → All (λ altpair → X ⊢̂ (proj₁ altpair) ⊳̂ (proj₂ altpair)) (zip xs xs')
                ------------------------
                → X ⊢̂ constr n xs ⊳̂ constr n xs' 
   case :  ∀ {p p' : X ⊢} {alts alts' : List (X ⊢)}
                → All (λ altpair → X ⊢̂ (proj₁ altpair) ⊳̂ (proj₂ altpair)) (zip alts alts') -- recursive translation for the other case patterns
                → X ⊢̂ p ⊳̂ p'
                ------------------------
                → X ⊢̂ case p alts ⊳̂ case p alts' 
   builtin : ∀ {b : Builtin} → X ⊢̂ builtin b ⊳̂ builtin b
   error : X ⊢̂ error ⊳̂ error

```

## Decision Procedure

Since this compiler phase is just a syntax re-arrangement in a very particular situation, we can
match on that situation in the before and after ASTs and apply the translation rule for this, or
expect anything else to be unaltered.

This can just traverse the ASTs applying the constructors from the transition relation.

```
--_⊢̂_⊳̂?_ : {X : Set} (ast ast' : X ⊢) → Dec (X ⊢̂ ast ⊳̂ ast')
--_⊢̂_⊳̂?_ ast ast' = ?

```

## Semantic Equivalence

We can show that this translation never alters the semantics of the statement. This is shown
in terms of the CEK machine evaluation. Since it is a simple re-arrangement of the syntax, it
isn't a refinement argument - the state before and after the operation is the same type, and is
unaltered by the syntax re-arrangement.

This does rely on the encoding of the semantics of `IfThenElse` in the CEK module, since we
need to show that the effective list of cases is the same as it would have been without the re-arrangement.

The `stepper` function uses the CEK machine to evaluate a term. Here we call it with a very
large gas budget and begin in an empty context (which assumes the term is closed).

```
--semantic_equivalence : ∀ {X set} {ast ast' : ⊥ ⊢}
 --                    → ⊥ ⊢ ast ⊳ ast'
 -- <Some stuff about whether one runs out of gas -- as long as neither runs out of gas, _then_ they are equivilent> 
 --                    → (stepper maxsteps  (Stack.ϵ ; [] ▻ ast)) ≡ (stepper maxsteps (Stack.ε ; [] ▻ ast'))

-- ∀ {s : ℕ} → stepper s ast ≡ <valid terminate state> ⇔ ∃ { s' : ℕ } [ stepper s' ast' ≡ <same valid terminate state> ] 
```
