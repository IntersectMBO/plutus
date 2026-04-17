---
title: VerifiedCompilation.UConstantFold
layout: page
---

# Constant Fold Translation Phase

```
{-# OPTIONS --type-in-type #-}

module VerifiedCompilation.UConstantFold where

```

## Imports

```
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; _+_; _-_; _<?_; _≤?_) renaming (_*_ to _**_; _≟_ to _ℤ≟_)
open import Data.Bool using (Bool; if_then_else_; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Function using (case_of_)

open import Untyped using (_⊢; builtin; con; force; _·_; error; `; ƛ; delay; constr; case)
open import RawU using (tmCon; TyTag; TmCon; decTyTag; ⟦_⟧tag)
open import Builtin.Signature using (_⊢♯; integer; bool; unit; pdata)
open _⊢♯
open import Builtin using (Builtin)
open import Builtin using ( addInteger; subtractInteger; multiplyInteger
                           ; divideInteger; quotientInteger; remainderInteger; modInteger
                           ; equalsInteger; lessThanInteger; lessThanEqualsInteger
                           ; ifThenElse; chooseUnit
                           ; fstPair; sndPair
                           ; chooseList; mkCons; headList; tailList; nullList; dropList
                           ; chooseData; constrData; mapData; listData; iData
                           ; unConstrData; unMapData; unListData; unIData
                           ; equalsData; mkPairData; mkNilData; mkNilPairData
                           ; div; quot; rem; mod)
open import Utils using (DATA; dropLIST; eqDATA; decIf; _×_; _,_; List; []; _∷_)
open Utils.DATA
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; ConstantFoldT; DecidableCE)
open import VerifiedCompilation.UntypedTranslation using (Translation; translation?; Relation)
open import Untyped.Equality using (_≟_)

```

## Evaluation of Certified Builtins

`evalCF` evaluates a single certified builtin application to a constant, returning
`nothing` if the term is not a fully-applied certified builtin with constant arguments.

```

evalCF : ∀ {X : ℕ} → X ⊢ → Maybe (X ⊢)

-- Integer arithmetic (binary, no force)
evalCF (builtin addInteger · con (tmCon integer i) · con (tmCon integer j)) =
  just (con (tmCon integer (i + j)))
evalCF (builtin subtractInteger · con (tmCon integer i) · con (tmCon integer j)) =
  just (con (tmCon integer (i - j)))
evalCF (builtin multiplyInteger · con (tmCon integer i) · con (tmCon integer j)) =
  just (con (tmCon integer (i ** j)))
evalCF (builtin divideInteger · con (tmCon integer i) · con (tmCon integer j))
  with j ℤ≟ (Data.Integer.+_ 0)
... | yes _ = nothing
... | no _  = just (con (tmCon integer (div i j)))
evalCF (builtin quotientInteger · con (tmCon integer i) · con (tmCon integer j))
  with j ℤ≟ (Data.Integer.+_ 0)
... | yes _ = nothing
... | no _  = just (con (tmCon integer (quot i j)))
evalCF (builtin remainderInteger · con (tmCon integer i) · con (tmCon integer j))
  with j ℤ≟ (Data.Integer.+_ 0)
... | yes _ = nothing
... | no _  = just (con (tmCon integer (rem i j)))
evalCF (builtin modInteger · con (tmCon integer i) · con (tmCon integer j))
  with j ℤ≟ (Data.Integer.+_ 0)
... | yes _ = nothing
... | no _  = just (con (tmCon integer (mod i j)))

-- Integer comparisons (binary, no force)
evalCF (builtin equalsInteger · con (tmCon integer i) · con (tmCon integer j)) =
  just (con (tmCon bool (does (i ℤ≟ j))))
evalCF (builtin lessThanInteger · con (tmCon integer i) · con (tmCon integer j)) =
  just (con (tmCon bool (does (i <? j))))
evalCF (builtin lessThanEqualsInteger · con (tmCon integer i) · con (tmCon integer j)) =
  just (con (tmCon bool (does (i ≤? j))))

-- ifThenElse (1 force, 3 args; branches may be any terms)
evalCF (force (builtin ifThenElse) · con (tmCon bool b) · vt · vf) =
  just (if b then vt else vf)

-- chooseUnit (1 force, 2 args; result may be any term)
evalCF (force (builtin chooseUnit) · con (tmCon unit _) · v) =
  just v

-- fstPair / sndPair (2 forces, 1 arg)
evalCF (force (force (builtin fstPair)) · con (tmCon (pair t1 _) (x , _))) =
  just (con (tmCon t1 x))
evalCF (force (force (builtin sndPair)) · con (tmCon (pair _ t2) (_ , y))) =
  just (con (tmCon t2 y))

-- chooseList (2 forces, 3 args; branches may be any terms)
evalCF (force (force (builtin chooseList)) · con (tmCon (list _) []) · vnil · _) =
  just vnil
evalCF (force (force (builtin chooseList)) · con (tmCon (list _) (_ ∷ _)) · _ · vcons) =
  just vcons

-- mkCons (1 force, 2 args; check element type matches list type)
evalCF (force (builtin mkCons) · con (tmCon t x) · con (tmCon (list ts) xs))
  with decTyTag t ts
... | yes refl = just (con (tmCon (list ts) (x ∷ xs)))
... | no _     = nothing

-- headList / tailList / nullList (1 force, 1 arg)
evalCF (force (builtin headList) · con (tmCon (list t) (x ∷ _))) =
  just (con (tmCon t x))
evalCF (force (builtin tailList) · con (tmCon (list t) (_ ∷ xs))) =
  just (con (tmCon (list t) xs))
evalCF (force (builtin nullList) · con (tmCon (list _) [])) =
  just (con (tmCon bool true))
evalCF (force (builtin nullList) · con (tmCon (list _) (_ ∷ _))) =
  just (con (tmCon bool false))

-- dropList (1 force, 2 args)
evalCF (force (builtin dropList) · con (tmCon integer n) · con (tmCon (list t) xs)) =
  just (con (tmCon (list t) (dropLIST n xs)))

-- chooseData (1 force, 6 args; branches may be any terms)
evalCF (force (builtin chooseData) · con (tmCon pdata (ConstrDATA _ _)) · v · _ · _ · _ · _) =
  just v
evalCF (force (builtin chooseData) · con (tmCon pdata (MapDATA _)) · _ · v · _ · _ · _) =
  just v
evalCF (force (builtin chooseData) · con (tmCon pdata (ListDATA _)) · _ · _ · v · _ · _) =
  just v
evalCF (force (builtin chooseData) · con (tmCon pdata (iDATA _)) · _ · _ · _ · v · _) =
  just v
evalCF (force (builtin chooseData) · con (tmCon pdata (bDATA _)) · _ · _ · _ · _ · v) =
  just v

-- constrData (no force, 2 args)
evalCF (builtin constrData · con (tmCon integer i) · con (tmCon (list pdata) xs)) =
  just (con (tmCon pdata (ConstrDATA i xs)))

-- mapData / listData / iData (no force, 1 arg)
evalCF (builtin mapData · con (tmCon (list (pair pdata pdata)) xs)) =
  just (con (tmCon pdata (MapDATA xs)))
evalCF (builtin listData · con (tmCon (list pdata) xs)) =
  just (con (tmCon pdata (ListDATA xs)))
evalCF (builtin iData · con (tmCon integer i)) =
  just (con (tmCon pdata (iDATA i)))

-- unConstrData / unMapData / unListData / unIData (no force, 1 arg)
evalCF (builtin unConstrData · con (tmCon pdata (ConstrDATA i xs))) =
  just (con (tmCon (pair integer (list pdata)) (i , xs)))
evalCF (builtin unMapData · con (tmCon pdata (MapDATA xs))) =
  just (con (tmCon (list (pair pdata pdata)) xs))
evalCF (builtin unListData · con (tmCon pdata (ListDATA xs))) =
  just (con (tmCon (list pdata) xs))
evalCF (builtin unIData · con (tmCon pdata (iDATA i))) =
  just (con (tmCon integer i))

-- equalsData / mkPairData (no force, 2 args)
evalCF (builtin equalsData · con (tmCon pdata x) · con (tmCon pdata y)) =
  just (con (tmCon bool (eqDATA x y)))
evalCF (builtin mkPairData · con (tmCon pdata x) · con (tmCon pdata y)) =
  just (con (tmCon (pair pdata pdata) (x , y)))

-- mkNilData / mkNilPairData (no force, 1 arg)
evalCF (builtin mkNilData · con (tmCon unit _)) =
  just (con (tmCon (list pdata) []))
evalCF (builtin mkNilPairData · con (tmCon unit _)) =
  just (con (tmCon (list (pair pdata pdata)) []))

-- Default: not a certified builtin application with constant arguments
evalCF _ = nothing

```

## Translation Relation

`ConstantFold M M'` witnesses that `evalCF M` reduces to `M'`.

```

data ConstantFold : Relation where
  constantFold : {X : ℕ} {M M' : X ⊢}
               → evalCF M ≡ just M'
               → ConstantFold M M'

```

## Decision Procedure

```

isConstantFold? : {X : ℕ} → DecidableCE (ConstantFold {X})
isConstantFold? ast ast' with evalCF ast in eq
... | nothing =
      ce (λ { (constantFold p) → case trans (sym eq) p of λ { () } })
         ConstantFoldT ast ast'
... | just result with result ≟ ast'
...   | no ¬refl =
        ce (λ { (constantFold p) → ¬refl (just-injective (trans (sym eq) p)) })
           ConstantFoldT ast ast'
...   | yes refl = proof (constantFold eq)

UConstantFold : Relation
UConstantFold = Translation ConstantFold

isUConstantFold? : {X : ℕ} → DecidableCE (UConstantFold {X})
isUConstantFold? = translation? ConstantFoldT isConstantFold?

```
