---
title: VerifiedCompilation.UForceDelay
layout: page
---

# Inliner Translation Phase
```
module VerifiedCompilation.UInline where

```
## Imports

```
open import VerifiedCompilation.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedTranslation using (Translation; TransMatch; translation?; Relation; convert; reflexive)
import Relation.Binary as Binary using (Decidable)
open import Untyped.RenamingSubstitution using (_[_]; weaken)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped.RenamingSubstitution using (weaken)
open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
import RawU
open import Data.List using (List; []; _∷_; sum; map)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Untyped.Purity using (Pure)
open import Untyped.Annotation using (unannotated; weakenAnnotation; Annotation; Annotation′; strip; read; ` ; ƛ; _·_; con; force; delay; constr; case; PointwiseAllᵣ; pcePointwiseAllᵣ)
open import Data.Product using (_,_)
open import Data.List.Relation.Unary.All using (All;toList)
```
## Translation Relation

Abstractly, inlining is much like β-reduction - where a term is applied to a
lambda, the term is substituted in. However, the UPLC compiler's inliner
sometimes performs "partial" inlining, where some instances of a variable are
inlined and some not. This is straightforward in the Haskell, which retains
variable names, but requires some more complexity to work with de Bruijn
indicies and intrinsic scopes.

The Haskell code works by building an environment of variable values and then
inlines from these. We can replicate that here, although we need to track the
applications and the bindings separately to keep them in the right order.

The scope of the terms needs to be handled carefully - as we descend into
lambdas things need to be weakened. However, where "complete" inlining
occurs the variables move back "up" a stage. In the relation this is handled
by weakening the right hand side term to bring the scopes into line, rather
than by trying to "strengthen" a subset of variables in an even more confusing
fashion.

We use a Zipper to track applied but not yet bound variables. We need two
constructors to track "complete" (i.e. deleted) and "partial" applications.
```
variable
  X Y : Set

data Zipper X : Set where
  □ : Zipper X
  _·_ : Zipper X → (X ⊢) → Zipper X
  _∘_ : Zipper X → (X ⊢) → Zipper X

zipWeaken : Zipper X → Zipper (Maybe X)
zipWeaken □ = □
zipWeaken (z · x) = zipWeaken z · weaken x
zipWeaken (z ∘ x) = zipWeaken z ∘ weaken x

```
Where a term is bound by a lambda, we need to enforce rules about the scopes.
Particularly, we need to enforce the `Maybe` system of de Bruijn indexing, so
that the subsequent functions can pattern match appropriately.

```
data Bind : (X : Set) → Set₁ where
  □ : Bind X
  _,_ : (b : Bind X) → (Maybe X ⊢) → Bind (Maybe X)

bind : Bind X → X ⊢ → Bind (Maybe X)
bind b t = (b , weaken t)

```

Note that `get` weakens the terms as it retrieves them. This is because we are
in the scope of the "tip" element. This is works out correctly, despite the fact
that the terms were weakened once when they were bound.
```
get : Bind X → X → Maybe (X ⊢)
get □ x = nothing
get (b , v) nothing = just v
get (b , v) (just x) with get b x
... | nothing = nothing
... | just v₁ = just (weaken v₁)
```
To remove unused names we need to count the usage of a "name"
(really a de Brujin index).
```
{-# TERMINATING #-}
usage : {X : Set} {{ _ : DecEq X}} → X → X ⊢ → ℕ
usage v (` x) with v ≟ x
... | yes refl = 1
... | no _ = 0
usage v (ƛ t) = usage (just v) t
usage v (t · t₁) = (usage v t) + (usage v t₁)
usage v (force t) = usage v t
usage v (delay t) = usage v t
usage v (con x) =  0
usage v (constr i xs) = sum (map (usage v) xs)
usage v (case t ts) = (usage v t) + sum (map (usage v) ts)
usage v (builtin b) = 0
usage v error = 0

```
# Decidable Inline Type

This recurses to the Translation type, but it needs to not do that initially or
the `translation?` decision procedure will recurse infinitely, so it is
limited to only matching a `Translation` in a non-empty environment.

Translation requires the `Relation` to be defined on an arbitrary,
unconstrained scope, but `Inlined a e` would be constrained by the
scope of the terms in `a` and `e`. Consequently we have to introduce a
new scope `Y`, but will only have constructors for places where this
matches the scope of the environment.

```

data Inlined : Zipper X → Bind X → (t₁ : X ⊢) → {t₂ : X ⊢} → Annotation ℕ t₂ → Set₁ where
  sub : {{ _ : DecEq X}} {v : X} {e : Zipper X} {b : Bind X} {t t' : X ⊢}
          → {a' : Annotation′ ℕ t'}
          → (get b v) ≡ just t
          → Inlined e b t' (0 , a')
          → Inlined e b (` v) (0 , a')

  c· : {{ _ : DecEq X}} {e : Zipper X} {b : Bind X} {t t' v : X ⊢}
          → {a' : Annotation′ ℕ t'}
          → {m : ℕ}
          → Inlined (e ∘ v) b t (m , a')
          → Inlined e b (t · v) (suc m , a')

  _·_ : {{ _ : DecEq X}} {e : Zipper X} {b : Bind X} {t₁ t₂ v₁ v₂ : X ⊢}
          → {a₂ : Annotation ℕ t₂} {av₂ : Annotation ℕ v₂}
          → Inlined (e · v₂) b t₁ a₂
          → Inlined □ b v₁ av₂
          → Inlined e b (t₁ · v₁) (0 , a₂ · av₂)

  cƛ : {{ _ : DecEq X}} {e : Zipper X} {b : Bind X} {t₁ : Maybe X ⊢} {t₂ v : X ⊢}
          → {a₂' : Annotation′ ℕ t₂}
          → Inlined (zipWeaken e) (bind b v) t₁ (weakenAnnotation (0 , a₂'))
          → Inlined (e ∘ v) b (ƛ t₁) (0 , a₂')

  ƛb : {{ _ : DecEq X}} {e : Zipper X} {b : Bind X} {t₁ t₂ : Maybe X ⊢} {v : X ⊢}
          → {a₂ : Annotation ℕ t₂}
          → Inlined (zipWeaken e) (bind b v) t₁ a₂
          → Inlined (e · v) b (ƛ t₁) (0 , (ƛ a₂))

  -- We can't recurse through Translation because it will become non-terminating,
  -- so traversing other AST nodes is done below.

  -- Everything should have zero on the annotations - non-zero should only happen
  -- where a LET has been removed, and this should be handled above.

  -- When traversing a lambda with no more applications to bind we can use the
  -- somewhat tautological (` nothing) term as the new zeroth value.
  ƛ : {{ _ : DecEq X}} {b : Bind X}{t t' : (Maybe X) ⊢}
          → {a' : Annotation ℕ t'}
          → Inlined □ (b , (` nothing)) t a'
          → Inlined □ b (ƛ t) (0 , (ƛ a'))
  -- We don't need a case for _·_ because we can always use the one above
  -- and use the binding zero times.
  force : {{ _ : DecEq X}} {e : Zipper X} {b : Bind X} {t t' : X ⊢}
          → {a' : Annotation ℕ t'}
          → Inlined e b t a'
          → Inlined e b (force t) (0 , (force a'))
  delay : {{ _ : DecEq X}} {e : Zipper X} {b : Bind X} {t t' : X ⊢}
          → {a' : Annotation ℕ t'}
          → Inlined e b t a'
          → Inlined e b (delay t) (0 , (delay a'))

  constr : {{ _ : DecEq X}} {e : Zipper X} {b : Bind X} {i : ℕ} {xs xs' : List (X ⊢)}
          → {as' : All (Annotation ℕ) xs'}
          → PointwiseAllᵣ (Inlined □ b) xs as'
          → Inlined e b (constr i xs) (0 , (constr i as'))
  case :  {{ _ : DecEq X}} {e : Zipper X} {b : Bind X} {t t' : X ⊢} {ts ts' : List (X ⊢)}
          → {a' : Annotation ℕ t'} {as' : All (Annotation ℕ) ts'}
          → Inlined e b t a'
          → PointwiseAllᵣ (Inlined e b) ts as'
          -- This won't work because the constr might have n arguments; Ask Roman what he meant by this!
          → Inlined e b (case t ts) (0 , (case a' as'))

  refl : {{ _ : DecEq X}} {e : Zipper X} {b : Bind X} {t : X ⊢}
          → {a′ : Annotation′ ℕ t}
          → Inlined e b t (0 , a′)

Inline : {X : Set} {{ _ : DecEq X}} → (X ⊢) → {t : X ⊢} → Annotation ℕ t → Set₁
Inline t a = Inlined □ □ t a

```
# Examples

```
postulate
  Vars : Set
  a b f g : Vars
  eqVars : DecEq Vars
  Zero One Two : RawU.TmCon

instance
  EqVars : DecEq Vars
  EqVars = eqVars

```
"Complete" inlining is just substitution in the same way as β-reduction.

[ (\a -> a) 1 ] becomes just 1
```
simple : Inlined {X = ⊥} □ □ ((ƛ (` nothing)) · (con One)) (1 , (con One))
simple = c· (cƛ (sub refl refl))

```

Nearly as simple, but now both sides end up with application structure:

[(\x y -> [ x y ]) a b ]  becomes [ a b ]

```
beforeEx1 : Vars ⊢
beforeEx1 = (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b))

afterEx1 : Vars ⊢
afterEx1 = ((` a) · (` b))

a-afterEx1 : Annotation ℕ afterEx1
a-afterEx1 = (2 , ((0 , ` a) · (0 , ` b)))

ex1 : Inlined □ □ beforeEx1 a-afterEx1
ex1 = c· (c· (cƛ (cƛ ((sub refl refl) · (sub refl refl)))))

```
Partial inlining is allowed, so  `(\a -> f (a 0 1) (a 2)) g` can become  `(\a -> f (g 0 1) (a 2)) g`
```
beforeEx2 : Vars ⊢
beforeEx2 = (ƛ (((` (just f)) · (((` nothing) · (con Zero)) · (con One))) · ((` nothing) · (con Two)) )) · (` g)

afterEx2 : Vars ⊢
afterEx2 = (ƛ (((` (just f)) · (((` (just g)) · (con Zero)) · (con One))) · ((` nothing) · (con Two)) )) · (` g)

-- Nothing is deleted, so all the annotations are zero.
-- Writing them out is an ... exercise in ... something.
a-afterEx2 : Annotation ℕ afterEx2
a-afterEx2 = unannotated 0 afterEx2

ex2 : Inlined □ □ beforeEx2 a-afterEx2
ex2 = (ƛb ((refl · (((sub refl refl) · refl) · refl)) · refl)) · refl

```
Interleaved inlining and not inlining should also work, along with correcting the scopes
as lambdas are removed.

```
Ex3Vars = Maybe (Maybe ⊥)

beforeEx3 : Ex3Vars ⊢
beforeEx3 = (ƛ ((ƛ ((` (just nothing)) · (` nothing))) · (` (just nothing)))) · (` nothing)

afterEx3 : Ex3Vars ⊢
afterEx3 = (ƛ ((` (just nothing)) · (` nothing))) · (` nothing)

a-afterEx3 : Annotation ℕ afterEx3
a-afterEx3 = (1 , (unannotated 0  (ƛ ((` (just nothing)) · (` nothing))) · ((0 , (` nothing)))))

ex3 : Inlined □ □ beforeEx3 a-afterEx3
ex3 = c· (cƛ ((ƛb ((sub refl refl) · refl)) · refl))

```
The `callsiteInline` example from the test suite:

`(\a -> f (a 0 1) (a 2)) (\x y -> g x y)`

inlining `a` at the first position, becomes


`(\a -> f ((\x y -> g x y) 0 1) (a 2)) (\x y -> g x y)`

```

callsiteInlineBefore : Vars ⊢
callsiteInlineBefore = (ƛ (((weaken (` f)) · (((` nothing) · (con Zero)) · (con One))) · ((` nothing) · (con Two)))) · (ƛ (ƛ (((weaken (weaken (` g))) · (` (just nothing))) · (` nothing))))

callsiteInlineAfter : Vars ⊢
callsiteInlineAfter = (ƛ (((weaken (` f)) · (((weaken (ƛ (ƛ (((weaken (weaken (` g))) · (` (just nothing))) · (` nothing))))) · (con Zero)) · (con One))) · ((` nothing) · (con Two)))) · (ƛ (ƛ (((weaken (weaken (` g))) · (` (just nothing))) · (` nothing))))

{-
callsiteInline : Inlined [] □ callsiteInlineBefore callsiteInlineAfter
callsiteInline = {!!} -- partial (ƛb (partial (partial refl (partial (partial (sub refl) refl) refl)) refl)) refl
-}
```
Continuing to inline:
`(\a -> f ((\x y -> g x y) 0 1) (a 2)) (\x y -> g x y)`

`f ((\x y -> g x y) 0 1) ((\x y -> g x y) 2) `

`f (g 0 1) ((\y -> g 2 y)) `

```
callsiteInlineFinal : Vars ⊢
callsiteInlineFinal = ((` f) · (((` g) · (con Zero)) · (con One))) · (ƛ (((` (just g)) · (con Two)) · (` nothing)))

-- This can't be done in one step without recursion.
--callsiteFinalProof : Inlined [] □ callsiteInlineBefore callsiteInlineFinal
--callsiteFinalProof = complete (ƛ+ (partial (partial refl (complete (complete (sub refl (ƛ+ (ƛ+ (partial (partial refl (sub refl refl)) (sub refl refl)))))))) (complete (sub refl (ƛ+ (ƛ (partial (partial refl (sub refl refl)) refl)))))))

```
## Decision Procedure

```
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; isVar?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay; isvar)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; inlineT; pcePointwise)
open import Relation.Nullary using (_×-dec_; contradiction)
open import Agda.Builtin.Sigma using (_,_)
open Eq using (trans; sym; subst)
open import Data.Maybe.Properties using (just-injective)
open import Agda.Primitive using (lzero; lsuc)

isInline? : {X : Set} {{_ : DecEq X}} → (ast : X ⊢) → {ast' : X ⊢} → (a' : Annotation ℕ ast') → ProofOrCE (Inline ast a')

{-# TERMINATING #-}
isIl? : {X : Set} {{_ : DecEq X}} → (e : Zipper X) → (b : Bind X) → (ast : X ⊢)  → {ast'  : X ⊢} → (a' : Annotation ℕ ast') → ProofOrCE {𝓂 = lzero} {𝓃 = lsuc lzero} (Inlined e b ast a')
isIl? e b ast (0 , a') with ast ≟ (strip (0 , a'))
... | yes refl = proof refl
isIl? {X = X} e b (` v) (zero , a') | no ¬refl with (get b v) in getb
... | nothing = ce {X = X} {X' = Annotation ℕ _} (λ { (sub getbv≡just x₁) → contradiction (trans (sym getbv≡just) getb) λ () ; refl → ¬refl refl}) inlineT v (zero , a')
... | just t = proof (sub getb refl)
isIl? {X = X} e b (ƛ ast) (zero , a') | no ¬refl with isLambda? isTerm? (strip (0 , a'))
... | no ¬lambda with e
...   | □ = ce {X = X ⊢} {X' = Annotation ℕ _} (λ { (ƛ x) → ¬lambda (islambda (isterm _)) ; refl → ¬refl refl} ) inlineT (ƛ ast) (zero , a')
...   | ee · x = ce {X = X ⊢} {X' = Annotation ℕ _} (λ { (ƛb x) → ¬lambda (islambda (isterm _)) ; refl → ¬refl refl} ) inlineT (ƛ ast) (zero , a')
...   | ee ∘ v with isIl? (zipWeaken ee) (bind b v) ast (weakenAnnotation (zero , a'))
...     | proof p = proof (cƛ p)
...     | ce ¬p t b a = ce (λ { (cƛ x) → ¬p x ; refl → ¬refl refl} ) t b a
isIl? e b (ƛ ast) (zero , ƛ NN) | no ¬refl | yes _ with e
isIl? e b (ƛ ast) (zero , ƛ NN) | no ¬refl | yes _ | □ with isIl? □ (b , (` nothing)) ast NN
... | proof p = proof (ƛ p)
... | ce ¬p t b a = ce (λ { (ƛ x) → ¬p x ; refl → ¬refl refl} ) t b a
isIl? e b (ƛ ast) (zero , ƛ NN) | no ¬refl | yes _ | ee · v with isIl? (zipWeaken ee) (bind b v) ast NN
... | proof p = proof (ƛb p)
... | ce ¬p t b a = ce (λ { (ƛb x) → ¬p x ; refl → ¬refl refl} ) t b a
isIl? e b (ƛ ast) (zero , ƛ NN) | no ¬refl | yes _ | ee ∘ v with isIl? (zipWeaken ee) (bind b v) ast (weakenAnnotation (zero , ƛ NN))
... | proof p = proof (cƛ p)
... | ce ¬p t b a = ce (λ { (cƛ x) → ¬p x ; refl → ¬refl refl} ) t b a
isIl? {X = X} e b (ast · ast₁) (zero , a') | no ¬refl with isApp? isTerm? isTerm? (strip (zero , a'))
... | no ¬app = ce {X = X ⊢} {X' = Annotation ℕ _} (λ { (x · x₁) → ¬app (isapp (isterm _) (isterm _)) ; refl → ¬refl refl} ) inlineT (ast · ast₁) (zero , a')
isIl? {X = X} e b (ast · ast₁) (zero , (LL · MM)) | no ¬refl | yes _ with (isIl? □ b ast₁ MM)
... | ce ¬-il-ast₁-MM t b a = ce (λ { (x · x₁) → ¬-il-ast₁-MM x₁ ; refl → ¬refl refl }) t b a
... | proof il-ast₁-MM with (isIl? (e · (strip MM)) b ast LL)
...   | ce ¬il-ast-LL t b a = ce (λ { (x · x₁) → ¬il-ast-LL x ; refl → ¬refl refl} ) t b a
...   | proof il-ast-LL = proof (il-ast-LL · il-ast₁-MM)
isIl? {X = X} e b (force ast) (zero , a') | no ¬refl with isForce? isTerm? (strip (zero , a'))
... | no ¬force = ce {X = X ⊢} {X' = Annotation ℕ _} (λ { (force x) → ¬force (isforce (isterm _)) ; refl → ¬refl refl} ) inlineT (force ast) (zero , a')
isIl? {X = X} e b (force ast) (zero , force MM) | no ¬refl | yes _ with isIl? e b ast MM
... | proof p = proof (force p)
... | ce ¬p t b a = ce (λ { (force x) → ¬p x ; refl → ¬refl refl} ) t b a
isIl? {X = X} e b (delay ast) (zero , a') | no ¬refl with isDelay? isTerm? (strip (zero , a'))
... | no ¬delay = ce {X = X ⊢} {X' = Annotation ℕ _} (λ { (delay x) → ¬delay (isdelay (isterm _)) ; refl → ¬refl refl} ) inlineT (force ast) (zero , a')
isIl? {X = X} e b (delay ast) (zero , delay MM) | no ¬refl | yes _ with isIl? e b ast MM
... | proof p = proof (delay p)
... | ce ¬p t b a = ce (λ { (delay x) → ¬p x ; refl → ¬refl refl} ) t b a
isIl? {X = X} e b (constr i xs) (zero , a') | no ¬refl with isConstr? allTerms? (strip (0 , a'))
... | no ¬constr = ce {X' = Annotation ℕ _} (λ { (constr x) → ¬constr (isconstr i (allterms _)) ; refl → ¬refl refl}) inlineT (constr i xs) (zero , a')
isIl? {X = X} e b (constr i xs) (zero , constr i₁ ts) | no ¬refl | yes _ with i ≟ i₁
... | no ¬i=i₁ = ce {X' = Annotation ℕ _} (λ { (constr x) → ¬i=i₁ refl ; refl → ¬refl refl}) inlineT (constr i xs) (zero , constr i₁ ts)
... | yes refl with pcePointwiseAllᵣ inlineT (isIl? □ b) xs ts
...   | ce ¬xs-ts t b a = ce (λ { (constr x) → ¬xs-ts x ; refl → ¬refl refl}) t b a
...   | proof xs-ts = proof (constr xs-ts)
isIl? {X = X} e b (case ast ts) (zero , a') | no ¬refl with isCase? isTerm? allTerms? (strip (0 , a'))
... | no ¬case = ce {X' = Annotation ℕ _} (λ { (case x x₁) → ¬case (iscase (isterm _) (allterms _)) ; refl → ¬refl refl} ) inlineT (case ast ts) (zero , a')
isIl? {X = X} e b (case ast ts) (zero , case t' ts') | no ¬refl | yes _ with isIl? e b ast t'
... | ce ¬p t b a = ce (λ { (case x x₁) → ¬p x ; refl → ¬refl refl}) t b a
... | proof p with pcePointwiseAllᵣ inlineT (isIl? e b) ts ts'
...   | ce ¬ps t b a = ce (λ { (case x x₁) → ¬ps x₁ ; refl → ¬refl refl}) t b a
...   | proof ps = proof (case p ps)
isIl? {X = X} e b (con x) (zero , a') | no ¬refl = ce {X = X ⊢} {X' = Annotation ℕ _} (λ { refl → ¬refl refl} ) inlineT (con x) (zero , a')
isIl? {X = X} e b (builtin b₁) (zero , a') | no ¬refl = ce {X = X ⊢} {X' = Annotation ℕ _} (λ { refl → ¬refl refl} ) inlineT (builtin b₁) (zero , a')
isIl? {X = X} e b error (zero , a') | no ¬refl = ce {X = X ⊢} {X' = Annotation ℕ _} (λ { refl → ¬refl refl} ) inlineT error (zero , a')
isIl? e b ast (suc n , a') with isApp? isTerm? isTerm? ast
... | yes (isapp (isterm t) (isterm v)) with isIl? (e ∘ v) b t (n , a')
...   | proof p = proof (c· p)
...   | ce ¬p tag before after = ce (λ { (c· x) → ¬p x} ) tag before after
isIl? {X = X} e b ast (suc n , a') | no ¬app = ce {X = X ⊢} {X' = Annotation ℕ _} (λ { (c· x) → ¬app (isapp (isterm _) (isterm _))} ) inlineT ast (suc n , a')

isInline? ast a' with (isIl? □ □ ast a')
... | proof p = proof p
... | ce ¬p tag before after = ce ¬p tag before after

```
