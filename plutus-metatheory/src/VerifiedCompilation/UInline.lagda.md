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
open import Data.Nat using (ℕ; _+_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Untyped.Purity using (Pure)
```
## Translation Relation

(λ ( f · (` 0) )) · b
==>
(f · b)

(λ ((` 0) · x)) · (λ (f (`0))) -- before1
==>
((λ (f (`0))) · x) -- a1/b2
==>
(f x) -- after2


(λ ((f (` 0)) · (g (` 0)))) · b
= partial =>
(λ ((f (` 0)) · (g b))) · b

(λ ((f (` 0)) · (g (` 0)))) · b
= complete =>
(f b) · (g b)

(λ N) · M
==>
LET M N

LET M N[`0]
==>
LET M N[M]

LET M N
= (` 0) not in N =>
N

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

A list of terms is fine for tracking unbound applications.
```
variable
  X Y : Set

listWeaken : List (X ⊢) → List ((Maybe X) ⊢)
listWeaken [] = []
listWeaken (v ∷ vs) = ((weaken v) ∷ (listWeaken vs))
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

[ M X , M M X , M M M X ] : Bind (M M M X)


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

data Inlined : List (X ⊢) → Bind X → (X ⊢) → (X ⊢) → Set₁ where
  sub : {{ _ : DecEq X}} {v : X} {e : List (X ⊢)} {b : Bind X} {t t' : X ⊢}
          → (get b v) ≡ just t
          → Inlined e b t t'
          → Inlined e b (` v) t'


{-
  complete : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t₁ t₂ v : X ⊢}
          → Inlined (v ∷ e) b t₁ t₂
          → Inlined e b (t₁ · v) t₂
  partial : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t₁ t₂ v₁ v₂ : X ⊢}
  -}

```

[] □ ((ƛ ƛ ƛ t) · a · b) t'

==> _·_

[b] □  ((ƛ ƛ ƛ t) · a) t'

==> _·_

[a , b] □  (ƛ ƛ ƛ t) t'

==> ƛb

[wk b] (□ , wk a) (ƛ ƛ t) (wk t')

==> ƛb

[] (□ , wk a , wk wk b) (ƛ t) (wk (wk t'))

==> ƛ

[] (□ , wk a , wk wk b , (` nothing)) t (wk (wk (wk t')))

```

  _·_ : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t₁ t₂ v₁ v₂ : X ⊢}
          → Inlined (v₂ ∷ e) b t₁ t₂
          → Inlined [] b v₁ v₂
          → Inlined e b (t₁ · v₁) (t₂ · v₂)

  ƛb : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t₁ t₂ : Maybe X ⊢} {v : X ⊢}
          → Inlined (listWeaken e) (bind b v) t₁ t₂
          → Inlined (v ∷ e) b (ƛ t₁) (ƛ t₂)

  -- We can't recurse through Translation because it will become non-terminating,
  -- so traversing other AST nodes is done below.

  -- When traversing a lambda with no more applications to bind we can use the
  -- somewhat tautological (` nothing) term as the new zeroth value.
  ƛ : {{ _ : DecEq X}} {b : Bind X}{t t' : (Maybe X) ⊢}
          → Inlined [] (b , (` nothing)) t t'
          → Inlined [] b (ƛ t) (ƛ t')
  -- We don't need a case for _·_ because we can always use partial
  -- and use the binding zero times.
  force : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t t' : X ⊢}
          → Inlined e b t t'
          → Inlined e b (force t) (force t')
  delay : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t t' : X ⊢}
          → Inlined e b t t'
          → Inlined e b (delay t) (delay t')
  constr : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {i : ℕ} {xs xs' : List (X ⊢)}
          → Pointwise (Inlined e b) xs xs'
          → Inlined e b (constr i xs) (constr i xs')
  case :  {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t t' : X ⊢} {ts ts' : List (X ⊢)}
          → Inlined e b t t'
          → Pointwise (Inlined e b) ts ts'
          → Inlined e b (case t ts) (case t' ts')
  refl : {{ _ : DecEq X}} {e : List (X ⊢)} {b : Bind X} {t : X ⊢}
          → Inlined e b t t


Inline : {X : Set} {{ _ : DecEq X}} → (X ⊢) → (X ⊢) → Set₁
Inline = Translation (λ {Y} → Inlined {Y} [] □)
```
Separating the "clean up" step allows the Inliner to be syntax directed.

ƛ (ƛ (` 1) · b) · a

== inline =>

ƛ (ƛ a · b) · a

== dead code =>

ƛ a · b


```

data Clean : (X ⊢) → (X ⊢) → Set₁ where
  clean : {a t' : X ⊢} {t : (Maybe X) ⊢}
    → Pure a
    → Clean t (weaken t')
    → Clean (ƛ t · a) t'
  refl : {t : X ⊢}
    → Clean t t
  _·_ : {t t' a a' : X ⊢}
    → Clean t t'
    → Clean a a'
    → Clean (t · a) (t' · a')
  ƛ : {t t' : X ⊢}
    → Clean t t'
    → Clean (ƛ (weaken t)) (ƛ (weaken t'))


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
--simple : Inlined {X = ⊥} [] □ ((ƛ (` nothing)) · (con One)) (con One)
simple : Inlined {X = ⊥} [] □ ((ƛ (` nothing)) · (con One)) ((ƛ (con One)) · (con One))
simple = ƛb (sub refl refl) · refl

simple-clean : Clean {⊥} ((ƛ (con One)) · (con One)) (con One)
simple-clean = clean Pure.con refl

```

Nearly as simple, but now both sides end up with application structure:

[(\x y -> [ x y ]) a b ]  becomes [ a b ]

```
beforeEx1 : Vars ⊢
beforeEx1 = (((ƛ (ƛ ((` (just nothing)) · (` nothing)))) · (` a)) · (` b))

uncleanEx1 : Vars ⊢
uncleanEx1 = (((ƛ (ƛ ((weaken (weaken (` a))) · (weaken (weaken (` b)))))) · (` a)) · (` b))

afterEx1 : Vars ⊢
afterEx1 = ((` a) · (` b))

ex1 : Inlined {X = Vars} [] □ beforeEx1 uncleanEx1
ex1 = ((ƛb (ƛb ((sub refl refl) · (sub refl refl)))) · refl) · refl --complete (complete (ƛ+ (ƛ+ (partial (sub refl) (sub refl)))))

ex1-clean : Clean uncleanEx1 afterEx1
ex1-clean = {!!}
```
Partial inlining is allowed, so  `(\a -> f (a 0 1) (a 2)) g` can become  `(\a -> f (g 0 1) (a 2)) g`
```
beforeEx2 : Vars ⊢
beforeEx2 = (ƛ (((` (just f)) · (((` nothing) · (con Zero)) · (con One))) · ((` nothing) · (con Two)) )) · (` g)

afterEx2 : Vars ⊢
afterEx2 = (ƛ (((` (just f)) · (((` (just g)) · (con Zero)) · (con One))) · ((` nothing) · (con Two)) )) · (` g)

ex2 : Inlined {X = Vars} [] □ beforeEx2 afterEx2
ex2 = {!!} -- partial (ƛb (partial (partial refl (partial (partial (sub refl) refl) refl)) refl)) refl

```
Interleaved inlining and not inlining should also work, along with correcting the scopes
as lambdas are removed.
```
Ex3Vars = Maybe (Maybe ⊥)

beforeEx3 : Ex3Vars ⊢
beforeEx3 = (ƛ ((ƛ ((` (just nothing)) · (` nothing))) · (` (just nothing)))) · (` nothing)

afterEx3 : Ex3Vars ⊢
afterEx3 = (ƛ ((` (just nothing)) · (` nothing))) · (` nothing)

ex3 : Inlined {X = Ex3Vars} [] □ beforeEx3 afterEx3
ex3 = {!!} -- complete (ƛ+ (partial (ƛb (partial (sub refl) refl)) refl))

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

callsiteInline : Inlined [] □ callsiteInlineBefore callsiteInlineAfter
callsiteInline = {!!} -- partial (ƛb (partial (partial refl (partial (partial (sub refl) refl) refl)) refl)) refl

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

isInline? : {X : Set} {{_ : DecEq X}} → (ast ast' : X ⊢) → ProofOrCE (Inline ast ast')

{-# TERMINATING #-}
isIl? : {X : Set} {{_ : DecEq X}} → (e : List (X ⊢)) → (b : Bind X) → (ast ast' : X ⊢) → ProofOrCE (Inlined e b ast ast')
isIl? e b ast ast' = {!!}
{-
isIl? e b ast ast' with ast ≟ ast'
... | yes refl = proof refl
isIl? e b (` v₁) ast' | no ast≠ast' with get b v₁ in get-v
... | nothing = ce (λ { (sub x) → contradiction (trans (sym get-v) x) λ () ; refl → ast≠ast' refl} ) inlineT (` v₁) ast'
... | just t with t ≟ ast'
...     | yes refl = proof (sub get-v)
...     | no ¬t=ast' = ce (λ { (sub x) → contradiction (trans (sym get-v) x) λ { refl → ¬t=ast' refl}  ; refl → ast≠ast' refl} ) inlineT t ast'
{-
...    | proof p = proof (sub get-v)
...    | ce ¬p tag bf af = ce (λ { (sub x xx) → contradiction (subst (λ t → Inlined e b t ast') (just-injective (trans (sym x) get-v))) λ z → ¬p (z xx) ; refl → ast≠ast' refl } ) inlineT t ast'
-}
isIl? e b (ƛ t₁) ast' | no ast≠ast' with isLambda? isTerm? ast'
isIl? (v ∷ e) b (ƛ t₁) ast' | no ast≠ast' | no ¬ƛ with isIl? (listWeaken e) (bind b v) t₁ (weaken ast')
...   | ce ¬p t b a = ce (λ { (ƛb x) → ¬ƛ (islambda (isterm _)) ; (ƛ+ x) → ¬p x ; refl → ast≠ast' refl} ) t b a
...   | proof p = proof (ƛ+ p)
isIl? [] b (ƛ t₁) ast' | no ast≠ast' | no ¬ƛ = ce (λ { (ƛ x) → ¬ƛ (islambda (isterm _)) ; refl → ast≠ast' refl }) inlineT (ƛ t₁) ast'
isIl? {X} [] b (ƛ t₁) ast' | no ast≠ast' | yes (islambda (isterm t₂)) with isIl? [] (b , (` nothing)) t₁ t₂
... | ce ¬p t b a = ce (λ { (ƛ x) → ¬p x ; refl → ast≠ast' refl} ) t b a
... | proof p = proof (ƛ {X = X} p)
isIl? (v ∷ e) b (ƛ t₁) ast' | no ast≠ast' | yes (islambda (isterm t₂)) with isIl? (listWeaken e) (bind b v) t₁ t₂
... | proof p = proof (ƛb p)
... | ce ¬pb t bf af with isIl? (listWeaken e) (bind b v) t₁ (weaken ast')
...    | proof p = proof (ƛ+ p)
...    | ce ¬p t b a = ce (λ { (ƛb x) → ¬pb x ; (ƛ+ x) → ¬p x ; refl → ast≠ast' refl} ) t bf af
isIl? {X} ⦃ de ⦄ e b (t₁ · t₂) ast' | no ast≠ast' with (isApp? isTerm? isTerm?) ast'
... | yes (isapp (isterm t₁') (isterm t₂')) with isIl? e b t₂ t₂'
...    | proof pt₂' with isIl? (t₂' ∷ e) b t₁ t₁'
...       | proof p = proof (partial p pt₂')
...       | ce ¬pf t bf af with isIl? (t₂ ∷ e) b t₁ ast'
...          | proof p = proof (complete p)
...          | ce ¬p t b a = ce (λ  { (complete x) → ¬p x ; (partial x x₁) → ¬pf x ; refl → ast≠ast' refl } ) t bf af
isIl? e b (t₁ · t₂) ast' | no ast≠ast' | yes (isapp (isterm t₁') (isterm t₂')) | ce ¬pf t bf af with isIl? (t₂ ∷ e) b t₁ ast'
... | proof p = proof (complete p)
... | ce ¬p t b a = ce (λ { (complete x) → ¬p x ; (partial x x₁) → ¬pf x₁ ; refl → ast≠ast' refl }) t b a
isIl? e b (t₁ · t₂) ast' | no ast≠ast' | no ¬app with isIl? (t₂ ∷ e) b t₁ ast'
...    | ce ¬p t b a = ce (λ { (complete x) → ¬p x ; (partial x x₁) → ¬app (isapp (isterm _) (isterm _)) ; refl → ast≠ast' refl }) t b a
...    | proof p = proof (complete p)
isIl? e b (force ast) ast' | no ast≠ast' with (isForce? isTerm?) ast'
... | no ¬force = ce (λ { (force x) → ¬force (isforce (isterm _)) ; refl → ast≠ast' refl} ) inlineT (force ast) ast'
... | yes (isforce (isterm x)) with isIl? e b ast x
...    | proof pp = proof (force pp)
...    | ce ¬p t b a = ce (λ { (force xx) → ¬p xx ; refl → ast≠ast' refl }) t b a
isIl? e b (delay ast) ast' | no ast≠ast' with (isDelay? isTerm?) ast'
... | no ¬delay = ce (λ { (delay xx) → ¬delay (isdelay (isterm _)) ; refl → ast≠ast' refl }) inlineT (delay ast) ast'
... | yes (isdelay (isterm x)) with isIl? e b ast x
...    | ce ¬p t b a = ce (λ { (delay xx) → ¬p xx ; refl → ast≠ast' refl }) t b a
...    | proof p = proof (delay p)
isIl? {X} e b (con x) ast' | no ast≠ast' = ce (λ { refl → ast≠ast' refl} ) inlineT (con {X} x) ast'
isIl? e b (constr i xs) ast' | no ast≠ast' with (isConstr? allTerms?) ast'
... | no ¬constr = ce (λ { (constr x) → ¬constr (isconstr i (allterms _)) ; refl → ast≠ast' refl}) inlineT (constr i xs) ast'
... | yes (isconstr i₁ (allterms xs')) with i ≟ i₁
... | no i≠i₁ = ce (λ { (constr x) → i≠i₁ refl ; refl → i≠i₁ refl} ) inlineT (constr i xs) ast'
... | yes refl with pcePointwise inlineT (isIl? e b) xs xs'
...    | proof pp = proof (constr pp)
...    | ce ¬p t b a = ce (λ { (constr x) → ¬p x ; refl → ast≠ast' refl} ) t b a
isIl? e b (case t ts) ast' | no ast≠ast' with (isCase? isTerm? allTerms?) ast'
... | no ¬case = ce (λ { (case x xs) → ¬case (iscase (isterm _) (allterms _)) ; refl → ast≠ast' refl}) inlineT (case t ts) ast'
... | yes (iscase (isterm t₁) (allterms ts₁)) with isIl? e b t t₁
...   | ce ¬p t b a = ce (λ { (case x x₁) → ¬p x ; refl → ast≠ast' refl} ) t b a
...   | proof p with pcePointwise inlineT (isIl? e b) ts ts₁
...     | ce ¬p t b a = ce (λ { (case x x₁) → ¬p x₁ ; refl → ast≠ast' refl} ) t b a
...     | proof ps = proof (case p ps)
isIl? {X} e b (builtin b₁) ast' | no ast≠ast' = ce (λ { refl → ast≠ast' refl} ) inlineT (builtin {X} b₁) ast'
isIl? {X} e b error ast' | no ast≠ast' = ce (λ { refl → ast≠ast' refl} ) inlineT (error {X}) ast'
-}
isInline? = translation? inlineT (λ {Y} → isIl? {Y} [] □)

```
