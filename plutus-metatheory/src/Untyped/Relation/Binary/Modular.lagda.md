---
title: Extensible translation relations
layout: page
---
```
module Untyped.Relation.Binary.Modular where

open import Untyped
```

## Imports

```
open import Untyped.Equality using (DecEq; _≟_;decPointwise)
open import VerifiedCompilation.UntypedViews
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; convert; reflexive)
open import Relation.Nullary using (_×-dec_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error; con-integer)
open import Builtin using (Builtin;equals;decBuiltin)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (trans; sym; subst)
open import Untyped.CEK using (lookup?; lookup?-deterministic)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; _∷_; []; [_])
open import Data.Maybe using (Maybe; just; nothing)
-- open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_,_)
open import RawU using (tag2TyTag; tmCon)
open import Agda.Builtin.Int using (Int)
open import Data.Empty using (⊥)
open import Function using (case_of_)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; caseReduceT)
open import Untyped.Reduction using (iterApp)
open import RawU using (tag2TyTag; tmCon; TmCon)
open import Data.Empty using (⊥)
open import Data.Bool using (true; false; Bool)

open import Untyped.Relation.Binary
open import Untyped.Relation.Binary.Properties
```

## Basic combinators for relation transformers

```
infixr 5 _+_

data _+_ (F G : RelationT) (@++ R : Relation) : Relation where
  inl : ∀ {X} {M N : X ⊢} → F R M N → (F + G) R M N
  inr : ∀ {X} {M N : X ⊢} → G R M N → (F + G) R M N

data Fix (F : RelationT) : Relation where
  fix : ∀ {X} {M N : X ⊢} → F (Fix F) M N → (Fix F) M N

Empty : RelationT
Empty R M N = ⊥

Const : @++ Relation → RelationT
Const R _ = R
```


## Term compatibilty rules

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


CompatTerm : RelationT
CompatTerm = CompatVar + CompatLambda + CompatApply + CompatForce + CompatDelay + CompatCon + CompatConstr + CompatCase + CompatBuiltin + CompatError + Empty

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

## Pattern synonyms

```

module Patterns
  (R : Relation)
  (inj : CompatTerm R ⊆ R)
  where

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

  pattern compat-varF n     = (p0 (`F n))
  pattern compat-lambdaF p  = (p1 (ƛF p))
  pattern compat-applyF p q = (p2 (p ·F q))
  pattern compat-forceF p   = (p3 (forceF p))
  pattern compat-delayF p   = (p4 (delayF p))
  pattern compat-conF       = (p5 conF)
  pattern compat-constrF p  = (p6 (constrF p))
  pattern compat-caseF p q  = (p7 (caseF p q))
  pattern compat-builtinF   = p8 builtinF
  pattern compat-errorF     = p9 errorF

open Patterns public
```


## Structures

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

```
DecidableT : RelationT → Set₁
DecidableT F =
  ∀ {R : Relation}
  → DecidableRel R
  → DecidableRel (F R)

private variable
  R : Relation

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

pointwise? : ∀ {R : Relation} →
  DecidableRel R →
  ∀ {X} (Ms Ns : List (X ⊢)) →
  Dec (Pointwise R Ms Ns)
pointwise? R? [] []         = yes []
pointwise? R? (x ∷ xs) (y ∷ ys)
  with R? x y ×-dec pointwise? R? xs ys
... | yes (Rxy , Rxsys) = yes (Rxy ∷ Rxsys)
... | no ¬R = no λ {(R ∷ Rs ) → ¬R (R , Rs)}
pointwise? R? (_ ∷ _) []    = no λ ()
pointwise? R? [] (_ ∷ _)    = no λ ()


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


## Examples

```

private module Example where

  Identity : Relation
  Identity = Fix CompatTerm

  _ : Identity {1} (` zero ) (` zero)
  _ = fix (compat-varF _)

  _ : Identity {1} (` zero · ` zero) (` zero · ` zero)
  _ = fix (compat-applyF (fix (compat-varF _)) (fix (compat-varF _)))

  _ : Identity {1} (ƛ (` zero)) (ƛ (` zero))
  _ = fix (compat-lambdaF (fix (compat-varF _)))

  lc-id? : DecidableRel Identity
  lc-id? = Fix-dec compatTerm?

  _ : Dec.does (lc-id? {2} (` zero · ` zero) (` zero · ` zero)) ≡ true
  _ = refl

```
