---
title: VerifiedCompilation.UCaseOfCas
layout: page
---
# Untyped Case of Case Translation Phase

```
module VerifiedCompilation.UCaseOfCase where

```
## Imports

```
open import VerifiedCompilation.Util using (DecEq; _≟_; decPointwise)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Untyped.CEK using (BApp; fullyAppliedBuiltin; BUILTIN; stepper; State; Stack)
open import Evaluator.Base using (maxsteps)
open import Builtin using (Builtin; ifThenElse)
open import Data.List using (List; zip; [_])
open import Utils as U using (Maybe; nothing; just; Either)
open import RawU using (TmCon; tmCon; decTag; TyTag; ⟦_⟧tag; decTagCon; tmCon2TagCon)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat using (ℕ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; isEquivalence; cong)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
```

```
data CoCCase {X : Set} : (X ⊢) → Set where
  isCoCCase : (b : X ⊢) (tn fn : ℕ) (alts tt ft : List (X ⊢)) → CoCCase (case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
```
Construct the view - This is truly horrible; there really should be a better way :(
```
viewCoCCase : {X : Set} → (x : (X ⊢)) → Dec (CoCCase x)
viewCoCCase (case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts) = yes (isCoCCase b tn fn alts tt ft)
viewCoCCase (` x) = no (λ ())
viewCoCCase (ƛ x) = no (λ ())
viewCoCCase (x · x₁) = no (λ ())
viewCoCCase (force x) = no (λ ())
viewCoCCase (delay x) = no (λ ())
viewCoCCase (con x) = no (λ ())
viewCoCCase (constr i xs) = no (λ ())
viewCoCCase (case (` x) ts) = no λ ()
viewCoCCase (case (ƛ x) ts) = no λ ()
viewCoCCase (case (` x · x₁) ts) = no λ ()
viewCoCCase (case (ƛ x · x₁) ts) = no λ ()
viewCoCCase (case ((` x · x₂) · x₁) ts) = no λ ()
viewCoCCase (case ((ƛ x · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((` x · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((ƛ x · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case ((((x · x₄) · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((force (` x) · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((force (ƛ x) · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((force (x · x₄) · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((force (force x) · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((force (delay x) · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((force (con x) · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((force (constr i xs) · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((force (case x ts₁) · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · x₂) · ` x) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · x₂) · ƛ x₁) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · x₂) · (x₁ · x₄)) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · x₂) · force x₁) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · x₂) · delay x₁) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · x₂) · con x) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · ` x) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · ƛ x₂) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · (x₂ · x₄)) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · force x₂) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · delay x₂) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · con x) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.addInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.subtractInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.multiplyInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.divideInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.quotientInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.remainderInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.modInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.equalsInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.lessThanInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.lessThanEqualsInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.appendByteString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.consByteString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.sliceByteString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.lengthOfByteString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.indexByteString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.equalsByteString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.lessThanByteString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.lessThanEqualsByteString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.sha2-256) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.sha3-256) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.blake2b-256) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.verifyEd25519Signature) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.verifyEcdsaSecp256k1Signature) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.verifySchnorrSecp256k1Signature) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.appendString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.equalsString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.encodeUtf8) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.decodeUtf8) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.chooseUnit) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.trace) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.fstPair) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.sndPair) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.chooseList) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.mkCons) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.headList) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.tailList) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.nullList) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.chooseData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.constrData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.mapData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.listData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.iData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.unConstrData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.unMapData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.unListData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.unIData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.unBData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.equalsData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.serialiseData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.mkPairData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.mkNilData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.mkNilPairData) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G1-add) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G1-neg) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G1-scalarMul) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G1-equal) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G1-hashToGroup) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G1-compress) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G1-uncompress) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G2-add) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G2-neg) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G2-scalarMul) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G2-equal) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G2-hashToGroup) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G2-compress) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-G2-uncompress) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-millerLoop) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-mulMlResult) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.bls12-381-finalVerify) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.keccak-256) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.blake2b-224) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.byteStringToInteger) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin Builtin.integerToByteString) · x₃) · constr i₁ xs₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · case x₂ ts₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · builtin b₁) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · error) · constr i xs) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · x₂) · case x₁ ts₁) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · x₂) · builtin b₁) ts) = no λ ()
viewCoCCase (case (((force (builtin b) · x₃) · x₂) · error) ts) = no λ ()
viewCoCCase (case (((force error · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((delay x · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((con x · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((constr i xs · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((case x ts₁ · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((builtin b · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (((error · x₃) · x₂) · x₁) ts) = no λ ()
viewCoCCase (case ((force x · x₂) · x₁) ts) = no λ ()
viewCoCCase (case ((delay x · x₂) · x₁) ts) = no λ ()
viewCoCCase (case ((con x · x₂) · x₁) ts) = no λ ()
viewCoCCase (case ((constr i xs · x₂) · x₁) ts) = no λ ()
viewCoCCase (case ((case x ts₁ · x₂) · x₁) ts) = no λ ()
viewCoCCase (case ((builtin b · x₂) · x₁) ts) = no λ ()
viewCoCCase (case ((error · x₂) · x₁) ts) = no λ ()
viewCoCCase (case (force x · x₁) ts) = no λ ()
viewCoCCase (case (delay x · x₁) ts) = no λ ()
viewCoCCase (case (con x · x₁) ts) = no λ ()
viewCoCCase (case (constr i xs · x₁) ts) = no λ ()
viewCoCCase (case (case x ts₁ · x₁) ts) = no λ ()
viewCoCCase (case (builtin b · x₁) ts) = no λ ()
viewCoCCase (case (error · x₁) ts) = no λ ()
viewCoCCase (case (force x) ts) = no λ ()
viewCoCCase (case (delay x) ts) = no λ ()
viewCoCCase (case (con x) ts) = no λ ()
viewCoCCase (case (constr i xs) ts) = no λ ()
viewCoCCase (case (case x ts₁) ts) = no λ ()
viewCoCCase (case (builtin b) ts) = no λ ()
viewCoCCase (case error ts) = no λ ()
viewCoCCase (builtin b) = no (λ ())
viewCoCCase error = no (λ ())
```

The Case of Case `force` pattern view. 
```
data CoCForce {X : Set} : (X ⊢) → Set where
  isCoCForce : (b' : X ⊢) (tn' fn' : ℕ) (alts' alts'' tt' ft' : List (X ⊢))  → CoCForce (force ((((force (builtin ifThenElse)) · b') · (delay (case (constr tn' tt') alts'))) · (delay (case (constr fn' ft') alts''))))

viewCoCForce : {X : Set} → (x : (X ⊢)) → Dec (CoCForce x)
viewCoCForce (force ((((force (builtin ifThenElse)) · b') · (delay (case (constr tn' tt') alts'))) · (delay (case (constr fn' ft') alts'')))) = yes (isCoCForce b' tn' fn' alts' alts'' tt' ft')
viewCoCForce (` x) = no (λ ())
viewCoCForce (ƛ x) = no (λ ())
viewCoCForce (x · x₁) = no (λ ())
viewCoCForce (force (` x)) = {!!}
viewCoCForce (force (ƛ x)) = {!!}
viewCoCForce (force (x · x₁)) = {!!}
viewCoCForce (force (force x)) = {!!}
viewCoCForce (force (delay x)) = {!!}
viewCoCForce (force (con x)) = {!!}
viewCoCForce (force (constr i xs)) = {!!}
viewCoCForce (force (case x ts)) = {!!}
viewCoCForce (force (builtin b)) = {!!}
viewCoCForce (force error) = {!!}
viewCoCForce (delay x) = no (λ ())
viewCoCForce (con x) = no (λ ())
viewCoCForce (constr i xs) = no (λ ())
viewCoCForce (case x ts) = no (λ ())
viewCoCForce (builtin b) = no (λ ())
viewCoCForce error = no (λ ())
```
## Translation Relation

This compiler stage only applies to the very specific case where an `IfThenElse` builtin exists in a `case` expression.
It moves the `IfThenElse` outside and creates two `case` expressions with each of the possible lists of cases. 

This translation relation has a constructor for the specific case, and then inductive constructors for everything else
to traverse the ASTs.

```
data _⊢̂_⊳̂_ (X : Set) : (X ⊢) → (X ⊢) → Set where
   caseofcase : ∀ {b : X ⊢} {tn tn' fn fn' : ℕ} {alts alts' tt ft tt' ft' : List (X ⊢)}
                → Pointwise (X ⊢̂_⊳̂_) alts alts' -- recursive translation for the other case patterns 
                → Pointwise (X ⊢̂_⊳̂_) tt tt' -- recursive translation for the true branch 
                → Pointwise (X ⊢̂_⊳̂_) ft ft' -- recursive translation for the false branch
                ----------------------
                → X ⊢̂
                       (case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
                       ⊳̂ (force ((((force (builtin ifThenElse)) · b) · (delay (case (constr tn tt') alts'))) · (delay (case (constr fn ft') alts'))))
   var : ∀ {x : X} → X ⊢̂ (` x) ⊳̂ (` x)
   ƛ   : ∀ {x x' : Maybe X ⊢}
           → Maybe X ⊢̂ x ⊳̂ x'
           ----------------------
           →  X ⊢̂ ƛ x ⊳̂ ƛ x' 
   app : ∀ {f t f' t' : X ⊢} → (X ⊢̂ f ⊳̂ f') → (X ⊢̂ t ⊳̂ t') → (X ⊢̂ (f · t) ⊳̂ (f' · t'))
   force : ∀ {t t' : X ⊢} → X ⊢̂ t ⊳̂ t' → X ⊢̂ force t ⊳̂ force t'  
   delay : ∀ {t t' : X ⊢} → X ⊢̂ t ⊳̂ t' → X ⊢̂ delay t ⊳̂ delay t'  
   con : ∀ {tc : TmCon} → X ⊢̂ con tc ⊳̂ con tc
   constr : ∀ {xs xs' : List (X ⊢)} { n : ℕ }
                → Pointwise (X ⊢̂_⊳̂_) xs xs'
                ------------------------
                → X ⊢̂ constr n xs ⊳̂ constr n xs' 
   case :  ∀ {p p' : X ⊢} {alts alts' : List (X ⊢)}
                → Pointwise (X ⊢̂_⊳̂_) alts alts' -- recursive translation for the other case patterns
                → X ⊢̂ p ⊳̂ p'
                ------------------------
                → X ⊢̂ case p alts ⊳̂ case p' alts' 
   builtin : ∀ {b : Builtin} → X ⊢̂ builtin b ⊳̂ builtin b
   error : X ⊢̂ error ⊳̂ error
```

## Decision Procedure

Since this compiler phase is just a syntax re-arrangement in a very particular situation, we can
match on that situation in the before and after ASTs and apply the translation rule for this, or
expect anything else to be unaltered.

This must traverse the ASTs applying the constructors from the transition relation, so where
the structure is unchanged we still need to check the sub-components.

```
_⊢̂_⊳̂?_ : {X : Set} {{ _ : DecEq X }} → (ast : X ⊢) → (ast' : X ⊢) → Dec (X ⊢̂ ast ⊳̂ ast')
```
First, handle all the cases where both sides of the translation are the same structure. Only the Case of Case
pattern should change the structure.
```
_⊢̂_⊳̂?_ (` x) (` y) with x ≟ y
...                         | yes refl = yes var
...                         | no ¬p = no (λ { (var) → ¬p refl })
_⊢̂_⊳̂?_ (ƛ ast) (ƛ ast') with _⊢̂_⊳̂?_ ast ast'
...                                  | yes p = yes (ƛ p)
...                                  | no ¬p = no (λ { (ƛ x) → ¬p x })
_⊢̂_⊳̂?_ (ast · ast₁) (ast' · ast'₁) with _⊢̂_⊳̂?_ ast ast' | _⊢̂_⊳̂?_ ast₁ ast'₁
...                                              | yes p1                 | yes p2 = yes (app p1 p2)
...                                              | yes p1                 | no ¬p2 = no λ { (app a a₁) → ¬p2 a₁ }
...                                              | no ¬p1                 | _         = no λ { (app a a₁) → ¬p1 a }
_⊢̂_⊳̂?_ (force ast) (force ast') with _⊢̂_⊳̂?_ ast ast' 
...                                  | yes p = yes (force p)
...                                  | no ¬p = no λ { (force a) → ¬p a }
_⊢̂_⊳̂?_ (delay ast) (delay ast') with _⊢̂_⊳̂?_ ast ast'
...                                  | yes p = yes (delay p)
...                                  | no ¬p = no λ { (delay a) → ¬p a}
_⊢̂_⊳̂?_ (con tm) (con tm') with tm ≟ tm'
...                                  | yes refl = yes con
...                                  | no ¬p = no λ { (con) → ¬p refl }
_⊢̂_⊳̂?_ (constr i ast) (constr i' ast') with i ≟ i' | decPointwise _⊢̂_⊳̂?_ ast ast'
...                                                       | no ¬i≟i  | _       = no λ { (constr pw) → ¬i≟i refl }
...                                                       | yes refl | no ¬p = no λ { (constr pw) → ¬p pw }
...                                                       | yes refl | yes p = yes (constr p)
_⊢̂_⊳̂?_ (case p ast) (case p' ast') with _⊢̂_⊳̂?_ p p' | decPointwise _⊢̂_⊳̂?_ ast ast'
...                                                       | no ¬p⊳p'  | _       = no λ { (case pp pw) → ¬p⊳p' pw }
...                                                       | _             | no ¬p = no λ { (case pp pw) → ¬p pp }
...                                                       | yes p⊳p'   | yes pw = yes (case pw p⊳p')
_⊢̂_⊳̂?_ (builtin b) (builtin b') with b ≟ b'
...                                          | no ¬b=b = no λ { (builtin) → ¬b=b refl }
...                                          | yes refl = yes builtin
_⊢̂_⊳̂?_ error error = yes error
```
If we have `case` translated to `force` we need to be sure that it matches exactly the Case of Case pattern
```

_⊢̂_⊳̂?_ (case p ast) (force ast') with viewCoCCase (case p ast) | viewCoCForce (force ast')

... | no ¬p | _ = no λ { x → {!!}}
... | yes (isCoCCase _ _ _ _ _ _) | no ¬p = no {!!}

_⊢̂_⊳̂?_ .(case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
               .(force ((((force (builtin ifThenElse)) · b') · (delay (case (constr tn' tt') alts'))) · (delay (case (constr fn' ft') alts'')))) | yes (isCoCCase b tn fn alts tt ft) | yes (isCoCForce b' tn' fn' alts' alts'' tt' ft')
        with b ≟ b' | tn ≟ tn'   | fn ≟ fn'   | alts' ≟ alts''  | decPointwise _⊢̂_⊳̂?_ alts alts' | decPointwise _⊢̂_⊳̂?_ tt tt' | decPointwise _⊢̂_⊳̂?_ ft ft'
...         | no ¬b≟b' | _            | _            | _                | _                | _              | _              = no λ { (caseofcase _ _ _ ) → ¬b≟b' refl } 
...         | yes refl   | no tn≠tn' | _            | _                | _                | _              | _              = no λ { (caseofcase _ _ _ ) →  tn≠tn' refl } 
...         | yes refl   | yes refl   | no fn≠fn' | _                | _                | _              | _              = no  λ { (caseofcase _ _ _ ) → fn≠fn' refl }
...         | yes refl   | yes refl   | yes refl   | no ¬alts      | _                | _              | _              = no λ { (caseofcase _ _ _ ) → ¬alts refl }
...         | yes refl   | yes refl   | yes refl   | yes refl       | no ¬pw-alts | _              | _              = no λ { (caseofcase x _ _ ) → ¬pw-alts x }
...         | yes refl   | yes refl   | yes refl   | yes refl       | yes pw-alts | no tt≠tt'     | _              = no λ { (caseofcase _ x _ ) → tt≠tt' x }
...         | yes refl   | yes refl   | yes refl   | yes refl       | yes pw-alts | yes ps-tt   | no ft≠ft'     = no λ { (caseofcase _ _ x ) → ft≠ft' x }
...         | yes refl   | yes refl   | yes refl   | yes refl       | yes pw-alts | yes pw-tt  | yes pw-ft   = yes (caseofcase pw-alts pw-tt pw-ft)
{-
-}
{-
_⊢̂_⊳̂?_ .((case ((((force (builtin ifThenElse)) · b) · (constr tn tt)) · (constr fn ft)) alts)
               (force ((((force (builtin ifThenElse)) · b') · (delay (case (constr tn' tt') alts'))) · (delay (case (constr fn' ft') alts''))))) | isCoC b b' tn tn' fn fn' alts alts' alts'' tt ft tt' ft'
               = ?
                                                            
-}
```
No other structure changing patterns should be allowed
```
_⊢̂_⊳̂?_ _ _ = no {!!} -- λ ()

```

## Semantic Equivalence

We can show that this translation never alters the semantics of the statement. This is shown
in terms of the CEK machine evaluation. Since it is a simple re-arrangement of the syntax, it
isn't a refinement argument - the state before and after the operation is the same type, and is
unaltered buy the syntax re-arrangement.

This does rely on the encoding of the semantics of `IfThenElse` in the CEK module, since we
need to show that the effective list of cases is the same as it would have been without the re-arrangement.

The `stepper` function uses the CEK machine to evaluate a term. Here we call it with a very
large gas budget and begin in an empty context (which assumes the term is closed).

```
-- TODO: Several approaches are possible. 
--semantic_equivalence : ∀ {X set} {ast ast' : ⊥ ⊢}
 --                    → ⊥ ⊢̂ ast ⊳̂ ast'
 -- <Some stuff about whether one runs out of gas -- as long as neither runs out of gas, _then_ they are equivilent> 
 --                    → (stepper maxsteps  (Stack.ϵ ; [] ▻ ast)) ≡ (stepper maxsteps (Stack.ε ; [] ▻ ast'))

-- ∀ {s : ℕ} → stepper s ast ≡ <valid terminate state> ⇔ ∃ { s' : ℕ } [ stepper s' ast' ≡ <same valid terminate state> ] 
```
