---
title: VerifiedCompilation.UntypedViews
layout: page
---
# Predicates and View Types for Untyped Terms
```
module VerifiedCompilation.UntypedViews where
module SimpleTypeClass where

open import Untyped using (_⊢; `; ƛ; case; constr; _·_; force; delay; con; builtin; error)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation
open import Utils as U using (Maybe; nothing; just; Either)
open import Relation.Nullary using (_×-dec_)
open import Data.Product using (_,_; _×_)
open import RawU using (TmCon)
open import Builtin using (Builtin; addInteger)
open import Untyped.Equality using (decEq-⊢; _≟_)
open import Data.List using (List; [_])
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Function using (_∋_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise; _∷_; [])
open import Data.List using (List; _∷_; []; map)

```
## Pattern Views for Terms

Because many of the translations only run on a very specific AST pattern, we need a
[View](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/view-from-the-left/F8A44CAC27CCA178AF69DD84BC585A2D)
to recognise that pattern and extract the variables.

Following suggestions from Philip Wadler: creating Views for each Term type and then
allowing them to accept arbitrary sub-views should make this reusable. We can create
patterns using nested calls to these views, and decide them with nested calls to the
decision procedures.
```

Pred : Set₁
Pred = {X : ℕ} → (X ⊢) → Set

ListPred : Set₁
ListPred = {X : ℕ} → List (X ⊢) → Set

data isVar { X : ℕ } : (X ⊢) → Set where
  isvar : (v : Fin X) → isVar (` v)
isVar? : {X : ℕ} → Decidable (isVar {X})
isVar? (` x) = yes (isvar x)
isVar? (ƛ x) = no λ ()
isVar? (x · x₁) = no (λ ())
isVar? (force x) = no (λ ())
isVar? (delay x) = no (λ ())
isVar? (con x) = no (λ ())
isVar? (constr i xs) = no (λ ())
isVar? (case x ts) = no (λ ())
isVar? (builtin b) = no (λ ())
isVar? error = no (λ ())

data isLambda (P : Pred) { X : ℕ } : (X ⊢) → Set where
  islambda : {t : (suc X ⊢)} → P t → isLambda P (ƛ t)
isLambda? : {X : ℕ} {P : Pred} → ({X : ℕ} → Decidable (P {X})) → Decidable (isLambda P {X})
isLambda? isP? (` x) = no λ ()
isLambda? isP? (ƛ t) with isP? t
...                                | no ¬p = no λ { (islambda x) → ¬p x}
...                                | yes p = yes (islambda p)
isLambda? isP? (t _⊢.· t₁) = no (λ ())
isLambda? isP? (_⊢.force t) = no (λ ())
isLambda? isP? (_⊢.delay t) = no (λ ())
isLambda? isP? (_⊢.con x) = no (λ ())
isLambda? isP? (constr i xs) = no (λ ())
isLambda? isP? (case t ts) = no (λ ())
isLambda? isP? (_⊢.builtin b) = no (λ ())
isLambda? isP? _⊢.error = no (λ ())

data isApp (P Q : Pred) {X : ℕ}  : (X ⊢) → Set where
  isapp : {l r : (X ⊢)} → P l → Q r → isApp P Q (l · r)
isApp? : {X : ℕ} → {P Q : Pred} → ({X : ℕ} → Decidable (P {X})) → ({X : ℕ} → Decidable (Q {X})) → Decidable (isApp P Q {X})
isApp? isP? isQ? (` x) = no (λ ())
isApp? isP? isQ? (ƛ t) = no (λ ())
isApp? isP? isQ? (t · t₁) with (isP? t) ×-dec (isQ? t₁)
...                                    | no ¬p = no λ { (isapp x x₁) → ¬p (x , x₁)}
...                                    | yes (p , q) = yes (isapp p q)
isApp? isP? isQ? (force t) = no (λ ())
isApp? isP? isQ? (delay t) = no (λ ())
isApp? isP? isQ? (con x) = no (λ ())
isApp? isP? isQ? (constr i xs) = no (λ ())
isApp? isP? isQ? (case t ts) = no (λ ())
isApp? isP? isQ? (builtin b) = no (λ ())
isApp? isP? isQ? error = no (λ ())

data isForce (P : Pred) {X : ℕ} : (X ⊢) → Set where
  isforce : {t : (X ⊢)} → P t → isForce P (force t)
isForce? : {X : ℕ} → {P : Pred} → ({X : ℕ} → Decidable (P {X})) → Decidable (isForce P {X})
isForce? isP? (` x) = no (λ ())
isForce? isP? (ƛ t) = no (λ ())
isForce? isP? (t · t₁) = no (λ ())
isForce? isP? (force t) with isP? t
...                                  | no ¬p = no λ { (isforce x) → ¬p x}
...                                  | yes p = yes (isforce p)
isForce? isP? (delay t) = no (λ ())
isForce? isP? (con x) = no (λ ())
isForce? isP? (constr i xs) = no (λ ())
isForce? isP? (case t ts) = no (λ ())
isForce? isP? (builtin b) = no (λ ())
isForce? isP? error = no (λ ())


data isDelay (P : Pred) {X : ℕ} : (X ⊢) → Set where
  isdelay : {t : (X ⊢)} → P t → isDelay P (delay t)
isDelay? : {X : ℕ} → {P : Pred} → ({X : ℕ} → Decidable (P {X})) → Decidable (isDelay P {X})
isDelay? isP? (` x) = no (λ ())
isDelay? isP? (ƛ t) = no (λ ())
isDelay? isP? (t · t₁) = no (λ ())
isDelay? isP? (force t) = no (λ ())
isDelay? isP? (delay t) with isP? t
...                                  | yes p = yes (isdelay p)
...                                  | no ¬p = no λ { (isdelay x) → ¬p x }
isDelay? isP? (con x) = no (λ ())
isDelay? isP? (constr i xs) = no (λ ())
isDelay? isP? (case t ts) = no (λ ())
isDelay? isP? (builtin b) = no (λ ())
isDelay? isP? error = no (λ ())

data isCon {X : ℕ} : (X ⊢) → Set where
  iscon : (t : TmCon)  → isCon {X} (con t)
isCon? : {X : ℕ} → Decidable (isCon {X})
isCon? (` x) = no (λ ())
isCon? (ƛ t) = no (λ ())
isCon? (t · t₁) = no (λ ())
isCon? (force t) = no (λ ())
isCon? (delay t) = no (λ ())
isCon? (con c) = yes (iscon c)
isCon? (constr i xs) = no (λ ())
isCon? (case t ts) = no (λ ())
isCon? (builtin b) = no (λ ())
isCon? error = no (λ ())

data isConstr (Qs : ListPred) {X : ℕ} : (X ⊢) → Set where
  isconstr : (i : ℕ) → {xs : List (X ⊢)} → Qs xs → isConstr Qs (constr i xs)
isConstr? : {X : ℕ} → {Qs : ListPred} → ({X : ℕ} → Decidable (Qs {X})) → Decidable (isConstr Qs {X})
isConstr? isQs? (` x) = no (λ())
isConstr? isQs? (ƛ t) = no (λ())
isConstr? isQs? (t · t₁) = no (λ())
isConstr? isQs? (force t) = no (λ())
isConstr? isQs? (delay t) = no (λ())
isConstr? isQs? (con x) = no (λ())
isConstr? isQs? (constr i xs) with isQs? xs
...                                           | no ¬q = no λ { (isconstr i₁ q) → ¬q q }
...                                           | yes q = yes (isconstr i q)
isConstr? isQs? (case t ts) = no (λ())
isConstr? isQs? (builtin b) = no (λ())
isConstr? isQs? error = no (λ())

data isCase (P : Pred) (Qs : ListPred) { X : ℕ } : (X ⊢) → Set where
  iscase : {t : (X ⊢)} → {ts : List (X ⊢)} → P t → Qs ts → isCase P Qs (case t ts)
isCase? : {X : ℕ} → {P : Pred} → {Qs : ListPred} → ({X : ℕ} → Decidable (P {X})) → ({X : ℕ} → Decidable (Qs {X})) → Decidable (isCase P Qs {X})
isCase? isP? isQs? (` x) = no (λ ())
isCase? isP? isQs? (ƛ t) = no (λ ())
isCase? isP? isQs? (t · t₁) = no (λ ())
isCase? isP? isQs? (force t) = no (λ ())
isCase? isP? isQs? (delay t) = no (λ ())
isCase? isP? isQs? (con x) = no (λ ())
isCase? isP? isQs? (constr i xs) = no (λ ())
isCase? isP? isQs? (case t ts) with (isP? t) ×-dec (isQs? ts)
...                                            | no ¬pqs = no λ { (iscase p qs) → ¬pqs (p , qs)}
...                                            | yes (p , qs) = yes (iscase p qs)
isCase? isP? isQs? (builtin b) = no (λ ())
isCase? isP? isQs? error = no (λ ())

data isBuiltin {X : ℕ} : (X ⊢) → Set where
  isbuiltin : (b : Builtin) → isBuiltin {X} (builtin b)
isBuiltin? : {X : ℕ} → Decidable (isBuiltin {X})
isBuiltin? (` x) = no (λ ())
isBuiltin? (ƛ t) = no (λ ())
isBuiltin? (t · t₁) = no (λ ())
isBuiltin? (force t) = no (λ ())
isBuiltin? (delay t) = no (λ ())
isBuiltin? (con x) = no (λ ())
isBuiltin? (constr i xs) = no (λ ())
isBuiltin? (case t ts) = no (λ ())
isBuiltin? (builtin b) = yes (isbuiltin b)
isBuiltin? error = no (λ ())

data isError {X : ℕ} : (X ⊢) → Set where
  iserror : isError {X} error
isError? : {X : ℕ} → Decidable (isError {X})
isError? (` x) = no (λ ())
isError? (ƛ t) = no (λ ())
isError? (t · t₁) = no (λ ())
isError? (force t) = no (λ ())
isError? (delay t) = no (λ ())
isError? (con x) = no (λ ())
isError? (constr i xs) = no (λ ())
isError? (case t ts) = no (λ ())
isError? (builtin b) = no (λ ())
isError? error = yes iserror
```
Some basic views that will match any Term, to be used for "wildcard" parts of the pattern.
```
data isTerm { X : ℕ } : (X ⊢) → Set where
  isterm : (t : X ⊢) → isTerm t
isTerm? : {X : ℕ} → Decidable (isTerm {X})
isTerm? t = yes (isterm t)

data allTerms { X : ℕ } : List (X ⊢) → Set where
  allterms : (ts : List (X ⊢)) → allTerms ts
allTerms? : {X : ℕ} → Decidable (allTerms {X})
allTerms? ts = yes (allterms ts)
```
## An Example
```
data TestPat {X : ℕ} : (X ⊢) → Set where
  tp : (t : X ⊢) (ts ts₂ : List (X ⊢)) → TestPat {X} (case (case t ts) ts₂)
isTestPat? : {X : ℕ} → Decidable (TestPat {X})
isTestPat? v with isCase? (isCase? isTerm? allTerms?) allTerms? v
... | yes (iscase (iscase (isterm t) (allterms ts)) (allterms ts₁)) = yes (tp t ts ts₁)
... | no ¬tp = no λ { (tp t ts ts₂) → ¬tp (iscase (iscase (isterm t) (allterms ts)) (allterms ts₂)) }

```

## Views

The following are slight generalizations on the previously defined views, with
convenient syntax. It allows you to compose them with existing decision
procedures such as _≟_ to match for example on a specific built-in function or
specific terms that were matched before. See the example at the end of this
module.

We define a predicate for each UPLC term constructor which witnesses that a term
starts with that constructor. Each such predicate is parametrised by predicates
for all arguments of that term constructor.

```
Pr : Set → Set₁
Pr A = A → Set
```

### Notation
For each term constructor, a `ᵖ` suffix denotes the predicate, A `!` suffix
denotes the witness of the predicate and a `?` suffix denotes the decision
procedure (see below).

```

private variable
  X : ℕ

data `ᵖ (P : Pr (Fin X)) : Pr (X ⊢ ) where
  `! : ∀ {n} → P n → `ᵖ P (` n)

data ƛᵖ (P : Pr (suc X ⊢)) : Pr (X ⊢) where
  ƛ! : ∀ {M} → P M → ƛᵖ P (ƛ M)

infixl 7 _·ᵖ_
infixl 7 _·!_

data _·ᵖ_ (P Q : Pr (X ⊢)) : Pr (X ⊢) where
  _·!_ : ∀ {M N} → P M → Q N → (P ·ᵖ Q) (M · N)

data forceᵖ (P : Pr (X ⊢)) : Pr (X ⊢) where
  force! : ∀ {M} → P M → forceᵖ P (force M)

data delayᵖ (P : Pr (X ⊢)) : Pr (X ⊢) where
  delay! : ∀ {M} → P M → delayᵖ P (delay M)

data caseᵖ (P : Pr (X ⊢)) (Ps : Pr (List (X ⊢))) : Pr (X ⊢) where
  case! : ∀ {M Ms} → P M → Ps Ms → caseᵖ P Ps (case M Ms)

data constrᵖ (P : Pr ℕ) (Ps : Pr (List (X ⊢))) : Pr (X ⊢) where
  constr! : ∀ {i Ms} → P i → Ps Ms → constrᵖ P Ps (constr i Ms)

data conᵖ (P : Pr TmCon) : Pr (X ⊢) where
  con! : ∀ {k} → P k → conᵖ P (con {X} k)

data builtinᵖ (P : Pr Builtin) : Pr (X ⊢) where
  builtin! : ∀ {b} → P b → builtinᵖ P (builtin {X} b)

data errorᵖ : Pr (X ⊢) where
  error! : errorᵖ {X} error
```

Each predicate is decidable if the predicates on sub-terms are decidable.

```
`? : ∀ {P : Pr (Fin X)} → Decidable P →  Decidable (`ᵖ P)
`? P? M with M
... | ƛ x         = no λ ()
... | x · x₁      = no λ ()
... | force x     = no λ ()
... | delay x     = no λ ()
... | con x       = no λ ()
... | constr i xs = no λ ()
... | case x ts   = no λ ()
... | builtin b   = no λ ()
... | error       = no λ ()
... | (` x)
  with P? x
... | yes Px = yes (`! Px)
... | no ¬Px = no (λ {(`! Px) → ¬Px Px})

ƛ? : ∀ {P : Pr (suc X ⊢)} → Decidable P → Decidable (ƛᵖ P)
ƛ? P? M with M
... | ` x         = no λ ()
... | t · t₁      = no λ ()
... | force t     = no λ ()
... | delay t     = no λ ()
... | con x       = no λ ()
... | constr i xs = no λ ()
... | case t ts   = no λ ()
... | builtin b   = no λ ()
... | error       = no λ ()
... | ƛ t
  with P? t
... | yes PM = yes (ƛ! PM)
... | no ¬PM = no λ {(ƛ! PM) → ¬PM PM }

infixl 7 _·?_

_·?_  : ∀ {P Q : Pr (X ⊢)} → Decidable P → Decidable Q → Decidable (P ·ᵖ Q)
(P? ·? Q?) M with M
... | ` _        = no λ ()
... | ƛ _        = no λ ()
... | force _    = no λ ()
... | delay _    = no λ ()
... | con _      = no λ ()
... | constr _ _ = no λ ()
... | case _ _   = no λ ()
... | builtin _  = no λ ()
... | error      = no λ ()
... | (M · N)
  with P? M ×-dec Q? N
... | yes (PM , QN) = yes (PM ·! QN)
... | no ¬PM×QN = no λ { (PM ·! QN) → ¬PM×QN (PM , QN)}


force? : ∀ {P : Pr (X ⊢)} → Decidable P → Decidable (forceᵖ P)
force? P? M with M
... | ` _        = no λ ()
... | ƛ _        = no λ ()
... | _ · _      = no λ ()
... | delay _    = no λ ()
... | con _      = no λ ()
... | constr _ _ = no λ ()
... | case _ _   = no λ ()
... | builtin _  = no λ ()
... | error      = no λ ()
... | force M
  with P? M
...   | yes PM = yes (force! PM)
...   | no ¬PM = no λ { (force! PM) → ¬PM PM}

delay? : {P : Pr (X ⊢)} → Decidable P → Decidable (delayᵖ P)
delay? P? M with M
... | ` _        = no λ ()
... | ƛ _        = no λ ()
... | _ · _      = no λ ()
... | force _    = no λ ()
... | con _      = no λ ()
... | constr _ _ = no λ ()
... | case _ _   = no λ ()
... | builtin _  = no λ ()
... | error      = no λ ()
... | delay N with P? N
...   | yes PN = yes (delay! PN)
...   | no ¬PN = no λ { (delay! PN) → ¬PN PN}

case? : {P : Pr (X ⊢)} {Q : Pr (List (X ⊢))} → Decidable P → Decidable Q → Decidable (caseᵖ P Q)
case? P? Q? M with M
... | ` _        = no λ ()
... | ƛ _        = no λ ()
... | _ · _      = no λ ()
... | force _    = no λ ()
... | delay _    = no λ ()
... | con _      = no λ ()
... | constr _ _ = no λ ()
... | builtin _  = no λ ()
... | error      = no λ ()
... | case M Ms with P? M ×-dec Q? Ms
...   | yes (Pn , QMs) = yes (case! Pn QMs)
...   | no ¬PQ = no λ {(case! Pn QMs) → ¬PQ (Pn , QMs)}

constr? : {P : Pr ℕ} {Q : Pr (List (X ⊢))} → Decidable P → Decidable Q → Decidable (constrᵖ P Q)
constr? P? Q? M with M
... | ` _        = no λ ()
... | ƛ _        = no λ ()
... | _ · _      = no λ ()
... | force _    = no λ ()
... | delay _    = no λ ()
... | con _      = no λ ()
... | case _ _   = no λ ()
... | builtin _  = no λ ()
... | error      = no λ ()
... | constr i Ms with P? i ×-dec Q? Ms
...   | yes (Pi , QMs) = yes (constr! Pi QMs)
...   | no ¬PQ = no λ {(constr! Pi QMs) → ¬PQ (Pi , QMs)}

con? : ∀ {P} → Decidable P → Decidable {A = X ⊢} (conᵖ P)
con? P? M with M
... | ` _        = no λ ()
... | ƛ _        = no λ ()
... | _ · _      = no λ ()
... | force _    = no λ ()
... | delay _    = no λ ()
... | constr _ _ = no λ ()
... | case _ _   = no λ ()
... | builtin _      = no λ ()
... | error      = no λ ()
... | con b  with P? b
...   | yes Pb = yes (con! Pb)
...   | no ¬Pb = no λ {(con! Pb) → ¬Pb Pb}

builtin? : ∀ {P} → Decidable P → Decidable {A = X ⊢} (builtinᵖ P)
builtin? P? M with M
... | ` _        = no λ ()
... | ƛ _        = no λ ()
... | _ · _      = no λ ()
... | force _    = no λ ()
... | delay _    = no λ ()
... | con _      = no λ ()
... | constr _ _ = no λ ()
... | case _ _   = no λ ()
... | error      = no λ ()
... | builtin b  with P? b
...   | yes Pb = yes (builtin! Pb)
...   | no ¬Pb = no λ {(builtin! Pb) → ¬Pb Pb}


error? : Decidable {A = X ⊢} (errorᵖ)
error? M with M
... | ` _        = no λ ()
... | ƛ _        = no λ ()
... | _ · _      = no λ ()
... | force _    = no λ ()
... | delay _    = no λ ()
... | con _      = no λ ()
... | constr _ _ = no λ ()
... | case _ _   = no λ ()
... | builtin _  = no λ ()
... | error      = yes error!
```

`match` is the trivial predicate that always holds:

```
data match {A : Set} : Pr A where
  match! : (x : A) → match x

⋯ : ∀{A} → Decidable (match {A})
⋯ x = yes (match! x)

```

Views for lists:

```
data _∷ᵖ_ {A : Set} ( P : Pr A ) (Q : Pr (List A)) : Pr (List A) where
  _∷!_ : ∀ {x xs} → P x → Q xs → (P ∷ᵖ Q) (x ∷ xs)

_∷?_ : ∀ {A : Set} {P : Pr A} {Q} → Decidable P → Decidable Q → Decidable (P ∷ᵖ Q)
(P? ∷? Q?) [] = no λ()
(P? ∷? Q?) (x ∷ xs) with P? x ×-dec Q? xs
... | yes (Px , Qxs) = yes (Px ∷! Qxs)
... | no  ¬PQ = no λ {(P ∷! Q) → ¬PQ (P , Q)}

data []ᵖ {A : Set} : Pr (List A) where
  []! : []ᵖ []

[]? : ∀ {A : Set} → Decidable ([]ᵖ {A})
[]? [] = yes []!
[]? (_ ∷ _) = no λ()
```

Shorthand for singleton lists:

```
singleton? : ∀ {A : Set} → Decidable (match {A} ∷ᵖ []ᵖ)
singleton? = ⋯ ∷? []?
```

## Inhabited types

In decision procedures that use the above views, we often find ourselves writing
trivial proof terms. E.g. suppose we have a predicate for application of the
identity function to any term:

```
private
  app-id : Pr (X ⊢)
  app-id = ƛᵖ (`ᵖ (_≡_ zero)) ·ᵖ match
```

Given a term that satisfies the predicate, there is only one trivial proof
(inhabitant):

```
  ex : 0 ⊢
  ex = ƛ (` zero) · ƛ (` zero)

  _ : app-id ex
  _ = ƛ! (`! refl) ·! match! (ƛ (` zero))
```

Instead of writing out those proofs, we can use a typeclass with instance search. The term
can then instead be given with `inhabitant`.

```
record Inhabited (A : Set) : Set where
  constructor inh
  field inhabitant : A

open Inhabited {{...}} public

```

Each of the term predicates has an instance:

```
instance
  inh-var : ∀ {n : Fin X} {P} → {{Inhabited (P n)}} → Inhabited (`ᵖ P (` n))
  inh-var {X} {n} = inh (`! inhabitant)

  inh-lam : ∀ {X} {M : suc X ⊢} {P} → {{Inhabited (P M)}} → Inhabited (ƛᵖ P (ƛ M))
  inh-lam = inh (ƛ! inhabitant)

  inh-app : ∀ {X} {P Q} {M N : X ⊢} → {{Inhabited (P M)}} → {{Inhabited (Q N)}} →  Inhabited ((P ·ᵖ Q) (M · N))
  inh-app = inh (inhabitant ·! inhabitant)

  inh-force : ∀ {X} {P} {M : X ⊢} → {{Inhabited (P M)}} → Inhabited (forceᵖ P (force M))
  inh-force = inh (force! inhabitant)

  inh-delay : ∀ {X} {P} {M : X ⊢} → {{Inhabited (P M)}} → Inhabited (delayᵖ P (delay M))
  inh-delay = inh (delay! inhabitant)

  inh-case : ∀ {X} {P Q} {M : X ⊢} {Ms : List (X ⊢)} →
    {{Inhabited (P M)}} →
    {{Inhabited (Q Ms)}} →
    Inhabited (caseᵖ P Q (case M Ms))
  inh-case = inh (case! inhabitant inhabitant)

  inh-constr : ∀ {X} {P Q} {i} {Ms : List (X ⊢)} →
    {{Inhabited (P i)}} →
    {{Inhabited (Q Ms)}} →
    Inhabited (constrᵖ P Q (constr i Ms))
  inh-constr = inh (constr! inhabitant inhabitant)

  inh-builtin : ∀ {X P b} →
    {{Inhabited (P b) }} →
    Inhabited (builtinᵖ P (builtin {X} b))
  inh-builtin = inh (builtin! inhabitant)

  inh-con : ∀ {X P b} →
    {{Inhabited (P b) }} →
    Inhabited (conᵖ P (con {X} b))
  inh-con = inh (con! inhabitant)

  inh-error : ∀ {X} →
    Inhabited (errorᵖ (error {X}))
  inh-error = inh error!

  inh-match : ∀ {A : Set} {X : A} → Inhabited (match X)
  inh-match = record {inhabitant = match! _}

  inh-× : ∀ {A B} → {{ Inhabited A }} → {{ Inhabited B }} → Inhabited (A × B)
  inh-× = inh (inhabitant , inhabitant)

  inh-≡ : ∀ {A : Set} {x : A} → Inhabited (x ≡ x)
  inh-≡ = record {inhabitant = refl}

  inh-∷ᵖ : ∀ {A : Set} {x : A} {xs} {P Q} →
    {{Inhabited (P x)}} →
    {{Inhabited (Q xs)}} →
    Inhabited ((P ∷ᵖ Q) (x ∷ xs))
  inh-∷ᵖ = record {inhabitant = inhabitant ∷! inhabitant}

  inh-[]ᵖ : ∀ {A : Set} →
    Inhabited ([]ᵖ ([] {A = A}))
  inh-[]ᵖ = record {inhabitant = []!}

```

### Examples

`AddCom` relates term `M + N` to `N + M`.

```
data AddComm : X ⊢ → X ⊢ → Set where
  addComm :
    ∀ {M N : X ⊢} →
    AddComm (builtin addInteger · M · N) (builtin addInteger · N · M)

addComm? : (M N : X ⊢) → Dec (AddComm M N)
addComm? M N
  with (builtin? (_≟_ addInteger) ·? ⋯ ·? ⋯) M
... | no ¬P = no λ {addComm → ¬P inhabitant}
... | yes (builtin! refl ·! match! x ·! match! y)
  with (builtin? (_≟_ addInteger) ·? (_≟_ y) ·? (_≟_ x)) N
... | no ¬P = no λ {addComm → ¬P inhabitant}
... | yes (builtin! refl ·! refl ·! refl) = yes addComm
```
