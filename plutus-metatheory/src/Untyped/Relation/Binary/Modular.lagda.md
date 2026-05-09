---
title: Untyped.Relation.Binary.Modular
layout: page
---
```
module Untyped.Relation.Binary.Modular where

```

## Imports

```
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.List using (List; _∷_; [])
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)

open import Untyped using (_⊢)
open import RawU using (TmCon)
open import Builtin using (Builtin)
open import Untyped.Equality using (_≟_)
open import Untyped.Relation.Binary.Core
open import Untyped.Relation.Binary.Structures
open import Untyped.Relation.Binary.Properties
open import VerifiedCompilation.UntypedViews

open _⊢
```

## Approach

This uses the fixpoint-of-functors approach to construct inductive relations out
of reusable parts. See the end of the file for an example translation relation.

In essence, each rule of a translation relation is defined as a single
constructor in an inductive type, with a type parameter for the relation that
that can be used for recursive uses.

## Relation transformers

Relation transformers are relations parametrised by other relations. The
parameter has a polarity annotation so that relations may only use it in
strictly positive positions. This makes it possible to take a fixpoint without
Agda's positivity checker failing.

```
RelationT : Set₁
RelationT = @++ Relation → Relation
```

## Basic combinators for relation transformers

```
infixr 5 _+_

data _+_ (F G : RelationT) (@++ R : Relation) : Relation where
  inl : ∀ {X} {M N : X ⊢} → F R M N → (F + G) R M N
  inr : ∀ {X} {M N : X ⊢} → G R M N → (F + G) R M N

Empty : RelationT
Empty R M N = ⊥

data Fix (F : RelationT) : Relation where
  fix :
    ∀ {X} {M N : X ⊢}
    → F (Fix F) M N
    → (Fix F) M N

Const : @++ Relation → RelationT
Const R _ = R
```

## Relation transformers for equivalence relations

```
data Transitivity (@++ R : Relation) : Relation where
  transF : ∀ {X} {L M N : X ⊢} →
    R L M →
    R M N →
    Transitivity R L N

data Symmetry (@++ R : Relation) : Relation where
  symF : ∀ {X} {M N : X ⊢} →
    R M N →
    Symmetry R N M

data Reflexivity (@++ R : Relation) : Relation where
  reflF : ∀ {X} {M : X ⊢} →
    Reflexivity R M M
```


## Term compatibilty rules

These are typical rules that are part of a translation relation.

```
data CompatVar (@++ R : Relation) : Relation where
  `F_ :
    ∀ {X} (x : Fin X)
    -------------------------
    → CompatVar R (` x) (` x)

data CompatLambda (@++ R : Relation) : Relation where
  ƛF :
    ∀ {X} {M M' : suc X ⊢}
    → R M M'
    -----------------------------
    → CompatLambda R (ƛ M) (ƛ M')

data CompatApply (@++ R : Relation) : Relation where
  _·F_ :
    ∀ {X} {M M' N N' : X ⊢}
    → R M M'
    → R N N'
    ---------------------------------
    → CompatApply R (M · N) (M' · N')

data CompatForce (@++ R : Relation) : Relation where
  forceF :
    ∀ {X} {M M' : X ⊢}
    → R M M'
    ------------------------------------
    → CompatForce R (force M) (force M')

data CompatDelay (@++ R : Relation) : Relation where
  delayF :
    ∀ {X} {M M' : X ⊢}
    → R M M'
    ------------------------------------
    → CompatDelay R (delay M) (delay M')

data CompatCon (@++ R : Relation) : Relation where
  conF :
    ∀ {X} {c : TmCon}
    -------------------------------------
    → CompatCon R (con {n = X} c) (con c)

data CompatConstr (@++ R : Relation) : Relation where
  constrF :
    ∀ {X} {i : ℕ} {xs xs' : List (X ⊢)}
    → Pointwise R xs xs'
    ---------------------------------------------
    → CompatConstr R (constr i xs) (constr i xs')

data CompatCase (@++ R : Relation) : Relation where
  caseF :
    ∀ {X} {t t' : X ⊢} {ts ts' : List (X ⊢)}
    → R t t'
    → Pointwise R ts ts'
    --------------------------------------
    → CompatCase R (case t ts) (case t' ts')

data CompatBuiltin (@++ R : Relation) : Relation where
  builtinF :
    ∀ {X} {b : Builtin}
    -------------------------------------------------
    → CompatBuiltin R (builtin {n = X} b) (builtin b)

data CompatError (@++ R : Relation) : Relation where
  errorF :
    ∀ {X}
    -----------------------------------------------
    → CompatError R (error {n = X}) (error {n = X})
```

Term-compatibility can be constructed by using compatibility rules of all constructors:

```
CompatTerm : RelationT
CompatTerm
  = CompatVar + CompatLambda + CompatApply + CompatForce + CompatDelay
  + CompatCon + CompatConstr + CompatCase + CompatBuiltin + CompatError + Empty
```

## Pattern synonyms

Convenient synonyms for constructing/matching cases of `CompatTerm`

```
-- TODO: solve this with metaprogramming or typeclasses
pattern p0 p = inl p
pattern p1 p = inr (p0 p)
pattern p2 p = inr (p1 p)
pattern p3 p = inr (p2 p)
pattern p4 p = inr (p3 p)
pattern p5 p = inr (p4 p)
pattern p6 p = inr (p5 p)
pattern p7 p = inr (p6 p)
pattern p8 p = inr (p7 p)
pattern p9 p = inr (p8 p)

pattern compat-varF n     = p0 (`F n)
pattern compat-lambdaF p  = p1 (ƛF p)
pattern compat-applyF p q = p2 (p ·F q)
pattern compat-forceF p   = p3 (forceF p)
pattern compat-delayF p   = p4 (delayF p)
pattern compat-conF       = p5 conF
pattern compat-constrF p  = p6 (constrF p)
pattern compat-caseF p q  = p7 (caseF p q)
pattern compat-builtinF   = p8 builtinF
pattern compat-errorF     = p9 errorF
```


## Structures

If a relation has the `CompatTerm` rules, then it forms a `TermCompatible` structure.

```
CompatTerm-TermCompatible : ∀ {R : Relation} → CompatTerm R ⊆ R → TermCompatible R
CompatTerm-TermCompatible inj = record
  { compat-var     = inj (compat-varF _)
  ; compat-ƛ       = λ RM → inj (compat-lambdaF RM)
  ; compat-·       = λ RM RN → inj (compat-applyF RM RN)
  ; compat-force   = λ RM → inj (compat-forceF RM)
  ; compat-delay   = λ RM → inj (compat-delayF RM)
  ; compat-constr  = λ RMS → inj (compat-constrF RMS)
  ; compat-case    = λ RM RMS → inj (compat-caseF RM RMS)
  ; compat-con     = inj compat-conF
  ; compat-builtin = inj compat-builtinF
  ; compat-error   = inj compat-errorF
  }
```


## Decision procedures

A decision procedure for a relation transformer requires a decision procedure
for the relation it abstracts over:

```
DecidableT : RelationT → Set₁
DecidableT F =
  ∀ {R : Relation}
  → DecidableRel R
  → DecidableRel (F R)
```

## Decision procedures for combinators

```
infixr 5 _+-dec_
_+-dec_ :
  ∀ {F G : RelationT}
  → DecidableT F
  → DecidableT G
  → DecidableT (F + G)
_+-dec_ F? G? R? M M'
  with F? R? M M'
... | yes P = yes (inl P)
... | no ¬P
  with G? R? M M'
... | yes P = yes (inr P)
... | no ¬Q = no λ {(inl P) → ¬P P; (inr Q) → ¬Q Q}

empty? : DecidableT Empty
empty? R? M M' = no λ ()

-- TODO: how to make this terminating? Accessibility proofs?
{-# TERMINATING #-}
Fix-dec : ∀ {F : RelationT} →
  DecidableT F →
  DecidableRel (Fix F)
Fix-dec F? M N
  with F? (Fix-dec F?) M N
... | yes P = yes (fix P)
... | no ¬P = no λ {(fix P) → ¬P P}

```

## Decision procedures for compatibility rules

```
compatVar? :
  DecidableT CompatVar
compatVar? R? M M'
  with (`? ⋯) M
... | no ¬M = no λ {(`F _) → ¬M inhabitant }
... | yes (`! (match! x)) with (`? (_≟_ x) M')
...   | no ¬M' = no λ {(`F _) → ¬M' inhabitant}
...   | yes (`! refl) = yes (`F _)

compatApply? :
  DecidableT CompatApply
compatApply? R? M M'
  with (⋯ ·? ⋯) M ×-dec (⋯ ·? ⋯) M'
... | no ¬MM' = no λ { (_ ·F _) → ¬MM' (inhabitant , inhabitant)}
... | yes ( match! M ·! match! N
          , match! M' ·! match! N') with R? M M' ×-dec R? N N'
...   | no ¬RMM'×RNN' = no λ { (RM ·F RN) → ¬RMM'×RNN' ( RM , RN )}
...   | yes (RMM' , RNN') = yes (RMM' ·F RNN')

compatLam? :
  DecidableT CompatLambda
compatLam? R? M M'
  with (ƛ? ⋯) M ×-dec (ƛ? ⋯) M'
... | no ¬MM' = no λ { (ƛF _) → ¬MM' (inhabitant , inhabitant)}
... | yes (ƛ! (match! N) , ƛ! (match! N')) with R? N N'
...   | no ¬NN' = no λ { (ƛF NN') → ¬NN' NN'}
...   | yes NN' = yes (ƛF NN')

compatForce? :
  DecidableT CompatForce
compatForce? R? M M'
  with force? ⋯ M ×-dec force? ⋯ M'
... | no ¬MM' = no λ { (forceF _) → ¬MM' inhabitant}
... | yes (force! (match! N) , force! (match! N'))
  with R? N N'
...   | no ¬NN' = no λ { (forceF NN) → ¬NN' NN}
...   | yes NN = yes (forceF NN)

compatDelay? :
  DecidableT CompatDelay
compatDelay? R? M M'
  with delay? ⋯ M ×-dec delay? ⋯ M'
... | no ¬MM' = no λ { (delayF _) → ¬MM' inhabitant}
... | yes (delay! (match! N) , delay! (match! N'))
  with R? N N'
...   | no ¬NN' = no λ { (delayF NN) → ¬NN' NN}
...   | yes NN = yes (delayF NN)

compatConstr? :
  DecidableT CompatConstr
compatConstr? R? M M'
  with constr? ⋯ ⋯ M
... | no ¬M = no λ { (constrF _) → ¬M inhabitant}
... | yes (constr! (match! i) (match! Ms))
  with constr? (_≟_ i) ⋯ M'
... | no ¬M' = no λ { (constrF _) → ¬M' inhabitant}
... | yes (constr! refl (match! Ms'))
  with pointwise? R? Ms Ms'
... | no ¬MsMs' = no λ { (constrF MsMs') → ¬MsMs' MsMs'}
... | yes MsMs' = yes (constrF MsMs')

compatCase? :
  DecidableT CompatCase
compatCase? R? M M'
  with case? ⋯ ⋯ M ×-dec case? ⋯ ⋯ M'
... | no ¬MM' = no λ { (caseF _ _) → ¬MM' (inhabitant , inhabitant)}
... | yes (case! (match! M) (match! Ms) , case! (match! M') (match! Ms'))
  with R? M M' ×-dec pointwise? R? Ms Ms'
... | no ¬MMs = no λ { (caseF MM' MsMs') → ¬MMs (MM' , MsMs')}
... | yes (MM' , MsMs') = yes (caseF MM' MsMs')

compatCon? : DecidableT CompatCon
compatCon? R? M M'
  with con? ⋯ M 
... | no ¬M = no λ {conF → ¬M inhabitant}
... | yes (con! (match! K))
  with con? (_≟_ K) M'
...   | no ¬M' = no λ {conF → ¬M' inhabitant}
...   | yes (con! refl) = yes conF


compatBuiltin? : DecidableT CompatBuiltin
compatBuiltin? R? M M'
  with builtin? ⋯ M 
... | no ¬M = no λ {builtinF → ¬M inhabitant}
... | yes (builtin! (match! K))
  with builtin? (_≟_ K) M'
...   | no ¬M' = no λ {builtinF → ¬M' inhabitant}
...   | yes (builtin! refl) = yes builtinF


compatError? : DecidableT CompatError
compatError? R? M M'
  with error? M ×-dec error? M'
... | yes (error! , error!) = yes errorF
... | no ¬MM' = no λ { errorF → ¬MM' inhabitant}

compatTerm? : DecidableT CompatTerm
compatTerm?
  =     compatVar?
  +-dec compatLam?
  +-dec compatApply?
  +-dec compatForce?
  +-dec compatDelay?
  +-dec compatCon?
  +-dec compatConstr?
  +-dec compatCase?
  +-dec compatBuiltin?
  +-dec compatError?
  +-dec empty?
```


## Refinements

Given partial refinement functions for both transformers, we can define a choice operator:

```
infixr 5 _<|>_
_<|>_ :
  ∀ {F G : RelationT} {R : Relation}
  → Refinement? (F R)
  → Refinement? (G R)
  → Refinement? ((F + G) R)
(f <|> g) M
  with f M
... | just (N , RMN) = just (N , inl RMN)
... | nothing
  with g M
... | just (N , SMN) = just (N , inr SMN)
... | nothing = nothing
```


## Example relation: remove force/delay

Suppose there is a compiler pass that removes each force and delay construct, by
mapping `delay` to a `ƛ`, and `force` into an application `_· constr 0 []`. We
will define a translation relation and decision procedure.

```
private module Example where

  open import Data.Bool using (true; false)
  open import Data.Nat using (ℕ; zero; suc)

  open import Untyped.RenamingSubstitution using (weaken)
```

We define a rule for transforming `delay`:

```
  data DelayLambda (@++ R : Relation) : Relation where
    delay-lambda :
      ∀ {X} {M : X ⊢} {M' : suc X ⊢}
      → R (weaken M) M'
      ----------------------------------------
      → DelayLambda R (delay M) (ƛ M')
```

And its corresponding decision procedure:

```
  dec-DelayLambda : DecidableT DelayLambda
  dec-DelayLambda R? M M'
    with (delay? ⋯ M) ×-dec (ƛ? ⋯ M')
  ... | no ¬delay×ƛ = no λ {(delay-lambda _) → ¬delay×ƛ inhabitant}
  ... | yes (delay! (match! N) , ƛ! (match! N'))
    with R? (weaken N) N'
  ... | yes RNN' = yes (delay-lambda RNN')
  ... | no ¬RNN' = no λ {(delay-lambda RNN') → ¬RNN' RNN'}
```

Similarly for the `force` transformation:

```
  data ForceApply (@++ R : Relation) : Relation where
    force-apply :
      ∀ {X} {M M' : X ⊢}
      → R M M'
      ----------------------------------------
      → ForceApply R (force M) (M' · constr 0 [])

  dec-ForceApply : DecidableT ForceApply
  dec-ForceApply R? M M'
    with (force? ⋯ M) ×-dec ((⋯ ·? (constr? (_≟ 0) []?)) M')
  ... | no ¬force×· = no λ {(force-apply _) → ¬force×· inhabitant}
  ... | yes (force! (match! N) , (match! N') ·! (constr! refl []!))
    with R? N N'
  ... | no ¬RNN = no λ {(force-apply RNN) → ¬RNN RNN}
  ... | yes RNN = yes (force-apply RNN)
```

The translation relation is now defined by composing the two rules with
compatibility rules of the other language constructs (note that we don't include
the compatibility rules for force and delay)

```
  RemoveFD : Relation
  RemoveFD = Fix
    ( ForceApply + DelayLambda
    + CompatVar + CompatLambda + CompatApply
    + CompatCon + CompatConstr + CompatCase
    + CompatBuiltin + CompatError
    )

  dec-RemoveFD : DecidableRel RemoveFD
  dec-RemoveFD = Fix-dec
    (     dec-ForceApply
    +-dec dec-DelayLambda
    +-dec compatVar?
    +-dec compatLam?
    +-dec compatApply?
    +-dec compatCon?
    +-dec compatConstr?
    +-dec compatCase?
    +-dec compatBuiltin?
    +-dec compatError?
    )
```

On terms without force/delay, the relation is the identity:

```
  L : 1 ⊢
  L = ` zero · ` zero

  _ : does (dec-RemoveFD L L) ≡ true
  _ = refl

```

Terms with force/delay have to be transformed:

```
  M-pre : 1 ⊢
  M-pre = force (delay (` zero))

  M-post : 1 ⊢
  M-post = (ƛ (` (suc zero))) · (constr 0 [])

  _ : does (dec-RemoveFD M-pre M-post) ≡ true
  _ = refl

  _ : does (dec-RemoveFD M-pre M-pre) ≡ false
  _ = refl
```
