---
title: Untyped reduction
style: page
---

```
module Untyped.Reduction where
```

## Imports

```
open import Untyped
open import Untyped.RenamingSubstitution
open import Builtin
open import Agda.Builtin.String using (primStringFromList; primStringAppend)
open import Data.Bool using (Bool;true;false)
open import Data.Nat using (ℕ;suc;zero;_<‴_;_≤‴_;≤‴-refl;≤‴-step)
open import Data.Integer using (_+_;_-_;_*_;∣_∣;_<?_;_≤?_;_≟_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Vec using (Vec;[];_∷_;_++_)
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
import Debug.Trace as Debug
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Fin using ()
open import Utils hiding (_≤L_;_:<_)
import Data.List
```

## Fixyt

```
infix 2 _—→_
```

## Builtin Arities

Typed builtins can take type and term arguments in any order. We
preserve this behaviour in the untyped language using delay/force. So,
arities are not just numbers they are lists of type/term labels.

```
data Label : Set where
  Type : Label
  Term : Label

data Bwd (A : Set) : Set where
  [] : Bwd A
  _:<_ : Bwd A → A → Bwd A

variable
  ls ls' : Bwd Label

infixl 10 _:<_

arity : Builtin → Bwd Label
arity addInteger = [] :< Term :< Term
arity subtractInteger = [] :< Term :< Term
arity multiplyInteger = [] :< Term :< Term
arity divideInteger = [] :< Term :< Term
arity quotientInteger = [] :< Term :< Term
arity remainderInteger = [] :< Term :< Term
arity modInteger = [] :< Term :< Term
arity lessThanInteger = [] :< Term :< Term
arity lessThanEqualsInteger = [] :< Term :< Term
arity greaterThanInteger = [] :< Term :< Term
arity greaterThanEqualsInteger = [] :< Term :< Term
arity equalsInteger = [] :< Term :< Term
arity concatenate = [] :< Term :< Term
arity takeByteString = [] :< Term :< Term
arity dropByteString = [] :< Term :< Term
arity lessThanByteString = [] :< Term :< Term
arity greaterThanByteString = [] :< Term :< Term
arity sha2-256 = [] :< Term
arity sha3-256 = [] :< Term
arity verifySignature = [] :< Term :< Term :< Term
arity equalsByteString = [] :< Term :< Term
arity ifThenElse = [] :< Type :< Term :< Term :< Term
arity charToString = [] :< Term
arity append = [] :< Term :< Term
arity trace = [] :< Term

data _≤L_ : Bwd Label → Bwd Label → Set where
  base     : ls ≤L ls
  skipType : ls :< Type ≤L ls' → ls ≤L ls'
  skipTerm : ls :< Term ≤L ls' → ls ≤L ls'

infix 5 _≤L_
```

## Error, values, telescopes of values, builtins

```
-- for untyped reduction, error also includes thing like impossible
-- applications
data Error {n} : n ⊢ → Set where
  E-error : Error error
```

```
ITel : Builtin → Bwd Label → Set

-- I cannot remember why there is both a FValue and a Value...
data FValue : 0 ⊢ → Set where
  V-ƛ : (t : suc 0 ⊢)
      → FValue (ƛ t)
  V-builtin : (b : Builtin)
            → ∀ {ls ls'}
            → ls' ≡ arity b
            → ls :< Term ≤L ls'
            → ITel b ls
            → (t : 0 ⊢)
            → FValue t

data Value  : 0 ⊢ → Set where
  V-F     : FValue t → Value t
  V-delay : Value (delay t)
  V-con   : (tcn : TermCon) → Value (con tcn)
  V-builtin⋆ : (b : Builtin)
            → ∀ {ls ls'}
            → ls' ≡ arity b
            → ls :< Type ≤L ls'
            → ITel b ls
            → (t : 0 ⊢)
            → Value t
  
ITel b []          = ⊤
ITel b (ls :< Type) = ITel b ls
ITel b (ls :< Term) = ITel b ls × Σ (0 ⊢) Value

deval : ∀{t} → Value t → 0 ⊢
deval {t} _ = t

IBUILTIN : (b : Builtin) → ITel b (arity b) → Σ (0 ⊢) λ t → Value t ⊎ Error t
IBUILTIN addInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  = _ , inl (V-con (integer (i + i')))
IBUILTIN subtractInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  = _ , inl (V-con (integer (i - i')))
IBUILTIN multiplyInteger 
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  = _ , inl (V-con (integer (i * i')))
IBUILTIN divideInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  with i' ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ , inl (V-con (integer (div i i')))
... | yes p = _ , inr E-error -- divide by zero
IBUILTIN quotientInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  with i' ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ , inl (V-con (integer (quot i i')))
... | yes p = _ , inr E-error -- divide by zero
IBUILTIN remainderInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  with i' ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ , inl (V-con (integer (rem i i')))
... | yes p = _ , inr E-error -- divide by zero
IBUILTIN modInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  with i' ≟ Data.Integer.ℤ.pos 0
... | no ¬p = _ , inl (V-con (integer (mod i i')))
... | yes p = _ , inr E-error -- divide by zero
IBUILTIN lessThanInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  with i <? i'
... | no ¬p = _ , inl (V-con (bool false))
... | yes p = _ , inl (V-con (bool true))
IBUILTIN lessThanEqualsInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  with i ≤? i'
... | no ¬p = _ , inl (V-con (bool false))
... | yes p = _ , inl (V-con (bool true))
IBUILTIN greaterThanInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  with i I>? i'
... | no ¬p = _ , inl (V-con (bool false))
... | yes p = _ , inl (V-con (bool true))
IBUILTIN greaterThanEqualsInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  with i I≥? i'
... | no ¬p = _ , inl (V-con (bool false))
... | yes p = _ , inl (V-con (bool true))
IBUILTIN equalsInteger
  ((tt , (t , V-con (integer i))) , (t' , V-con (integer i')))
  with i ≟ i'
... | no ¬p = _ , inl (V-con (bool false))
... | yes p = _ , inl (V-con (bool true))
IBUILTIN concatenate
  ((tt , (t , V-con (bytestring b))) , (t' , V-con (bytestring b')))
  = _ , inl (V-con (bytestring (concat b b')))
IBUILTIN takeByteString
  ((tt , (t , V-con (integer i))) , (t' , V-con (bytestring b)))
  = _ , inl (V-con (bytestring (take i b)))
IBUILTIN dropByteString
  ((tt , (t , V-con (integer i))) , (t' , V-con (bytestring b)))
  = _ , inl (V-con (bytestring (drop i b)))
IBUILTIN lessThanByteString
  ((tt , (t , V-con (bytestring b))) , (t' , V-con (bytestring b')))
  = _ , inl (V-con (bool (B< b b')))
IBUILTIN greaterThanByteString
  ((tt , (t , V-con (bytestring b))) , (t' , V-con (bytestring b')))
  = _ , inl (V-con (bool (B> b b')))
IBUILTIN sha2-256
  (tt , (t , V-con (bytestring b)))
  = _ , inl (V-con (bytestring (SHA2-256 b)))
IBUILTIN sha3-256
  (tt , (t , V-con (bytestring b)))
  = _ , inl (V-con (bytestring (SHA3-256 b)))
IBUILTIN verifySignature
  (((tt , (t , V-con (bytestring k))) , (t' , V-con (bytestring d))) , (t'' , V-con (bytestring c)))
   with verifySig k d c
... | just b = _ , inl (V-con (bool b))
... | nothing = _ , inr E-error -- not sure what this is for
IBUILTIN equalsByteString
  ((tt , (t , V-con (bytestring b))) , (t' , V-con (bytestring b')))
  = _ , inl (V-con (bool (equals b b')))
IBUILTIN ifThenElse
  (((tt , (t , V-con (bool true))) , (t' , v')) , (t'' , v''))
  = _ , inl v'
IBUILTIN ifThenElse
  (((tt , (t , V-con (bool false))) , (t' , v')) , (t'' , v''))
  = _ , inl v''
IBUILTIN charToString
  (tt , (t , V-con (char c)))
  = _ , inl (V-con (string (primStringFromList Data.List.[ c ])))
IBUILTIN append
  ((tt , (t , V-con (string s))) , (t' , V-con (string s')))
  = _ , inl (V-con (string (primStringAppend s s')))
IBUILTIN trace
  (tt , (t , v))
  = _ , inl (V-con unit)
IBUILTIN _ _ = error , inr E-error

IBUILTIN' : (b : Builtin) → ∀{ls} → ls ≡ arity b → ITel b ls → Σ (0 ⊢) λ t → Value t ⊎ Error t
IBUILTIN' b refl vs = IBUILTIN b vs
```

## Reduction

```
data _—→_ : 0 ⊢ → 0 ⊢ → Set where
  ξ-·₁ : t —→ t' → t · u —→ t' · u
  ξ-·₂ : FValue t → u —→ u' → t · u —→ t · u'

  β-ƛ : Value u → ƛ t · u —→ t [ u ]

  ξ-force : t —→ t' → force t —→ force t'

  β-delay : force (delay t) —→ t

  β-builtin : (b : Builtin)
            → ∀ {ls} t
            → (p : ls :< Term ≡ arity b)
            → (vs : ITel b ls)
            → ∀ {u} v
            → t · u —→ fst (IBUILTIN' b p (vs , u , v))

  β-builtin⋆ : (b : Builtin)
            → ∀ {ls} t
            → (p : ls :< Type ≡ arity b)
            → (vs : ITel b ls)
            → force t —→ fst (IBUILTIN' b p vs)


  E-·₁ : error · u —→ error
  E-·₂ : FValue t → t · error —→ error

  E-force : force error —→ error


  E-builtin⋆· : (b : Builtin)
              → ∀ t u
              -- TODO: more conditions required
              → t · u —→ error

  -- these correspond to type errors encountered at runtime
  E-con· : {tcn : TermCon} → con tcn · t —→ error
  E-con-force : {tcn : TermCon} → force (con tcn) —→ error
  E-FVal-force : FValue t → force t —→ error
  E-delay· : delay t · u —→ error

  -- this is a runtime type error that ceases to be a type error after erasure
  -- E-runtime : {t : n ⊢} → t —→ error

```


```
data _—→⋆_ : 0 ⊢ → 0 ⊢ → Set where
  refl  : t —→⋆ t
  trans—→⋆ : {t'' : 0 ⊢} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
```

## Progress

```
data Progress (t : 0 ⊢) : Set where
  step : t —→ u
         ----------
       → Progress t
  done : Value t
         ----------
       → Progress t
  error : Error t
          ----------
        → Progress t

progress-·V :
    Value t
  → Progress u
  → Progress (t · u)
progress-·V (V-con tcn)              v               = step E-con·
progress-·V (V-builtin⋆ b L p vs t)  v               = step (E-builtin⋆· b t _)
progress-·V (V-F v)                  (step q)        = step (ξ-·₂ v q)
progress-·V (V-F v)                  (error E-error) = step (E-·₂ v)
progress-·V (V-F (V-ƛ t))            (done v)        = step (β-ƛ v)
progress-·V V-delay                  v               = step E-delay·
progress-·V (V-F (V-builtin b p base vs t)) (done v) =
  step (β-builtin b t p vs v)
progress-·V (V-F (V-builtin b p (skipType q) vs t)) (done v) =
  done (V-builtin⋆ b p q (vs , _ , v) (t · _))
progress-·V (V-F (V-builtin b p (skipTerm q) vs t)) (done v) =
  done (V-F (V-builtin b p q (vs , _ , v) (t · _)))

progress-· : Progress t → Progress u → Progress (t · u)
progress-· (done v)        q = progress-·V v q
progress-· (step p)        q = step (ξ-·₁ p)
progress-· (error E-error) q = step E-·₁

progress-forceV : Value t → Progress (force t)
progress-forceV (V-F V)     = step (E-FVal-force V)
progress-forceV V-delay     = step β-delay
progress-forceV (V-con tcn) = step E-con-force
progress-forceV (V-builtin⋆ b p base vs t) =
  step (β-builtin⋆ b t p vs)
progress-forceV (V-builtin⋆ b p (skipTerm q) vs t) =
  done (V-F (V-builtin b p q vs (force t)))
progress-forceV (V-builtin⋆ b p (skipType q) vs t) =
  done (V-builtin⋆ b p q vs (force t))

progress-force : Progress t → Progress (force t)
progress-force (done v)        = progress-forceV v
progress-force (step p)        = step (ξ-force p)
progress-force (error E-error) = step E-force

ival : ∀ b → Value (builtin b)
ival addInteger =
  V-F (V-builtin addInteger refl (skipTerm base) _ (builtin addInteger))
ival subtractInteger =
  V-F (V-builtin subtractInteger refl (skipTerm base) _ (builtin subtractInteger))
ival multiplyInteger =
  V-F (V-builtin multiplyInteger refl (skipTerm base) _ (builtin multiplyInteger))
ival divideInteger = V-F (V-builtin divideInteger refl (skipTerm base) _ _)
ival quotientInteger = V-F (V-builtin quotientInteger refl (skipTerm base) _ _)
ival remainderInteger =
  V-F (V-builtin remainderInteger refl (skipTerm base) _ _)
ival modInteger = V-F (V-builtin modInteger refl (skipTerm base) _ _)
ival lessThanInteger = V-F (V-builtin lessThanInteger refl (skipTerm base) _ _)
ival lessThanEqualsInteger =
  V-F (V-builtin lessThanEqualsInteger refl (skipTerm base) _ _)
ival greaterThanInteger =
  V-F (V-builtin greaterThanInteger refl (skipTerm base) _ _)
ival greaterThanEqualsInteger =
  V-F (V-builtin greaterThanEqualsInteger refl (skipTerm base) _ _)
ival equalsInteger = V-F (V-builtin equalsInteger refl (skipTerm base) _ _)
ival concatenate = V-F (V-builtin concatenate refl (skipTerm base) _ _)
ival takeByteString = V-F (V-builtin takeByteString refl (skipTerm base) _ _)
ival dropByteString = V-F (V-builtin dropByteString refl (skipTerm base) _ _)
ival lessThanByteString =
  V-F (V-builtin lessThanByteString refl (skipTerm base) _ _)
ival greaterThanByteString =
  V-F (V-builtin greaterThanByteString refl (skipTerm base) _ _)
ival sha2-256 = V-F (V-builtin sha2-256 refl base _ _)
ival sha3-256 = V-F (V-builtin sha3-256 refl base _ _)
ival verifySignature =
  V-F (V-builtin verifySignature refl (skipTerm (skipTerm base)) _ _)
ival equalsByteString = V-F (V-builtin equalsByteString refl (skipTerm base) _ _)
ival ifThenElse =
  V-builtin⋆ ifThenElse refl (skipTerm (skipTerm (skipTerm base))) _ _
ival charToString = V-F (V-builtin charToString refl base _ _)
ival append = V-F (V-builtin append refl (skipTerm base) _ _)
ival trace = V-F (V-builtin trace refl base _ _)

progress : (t : 0 ⊢) → Progress t
progress (` ())
progress (ƛ t)        = done (V-F (V-ƛ t))
progress (t · u)      = progress-· (progress t) (progress u)
progress (force t)    = progress-force (progress t)
progress (delay t)    = done V-delay
progress (builtin b)  = done (ival b)
progress (con tcn)    = done (V-con tcn)
progress error       = error E-error
```

## Iterating progress to run programs

```
progressor : ℕ → (t : 0 ⊢) → Either RuntimeError (Maybe (0 ⊢))
progressor 0       t = inj₁ gasError
progressor (suc n) t with progress t
... | step {u = t'} p  = progressor n t'
... | done v  = inj₂ $ just (deval v)
... | error e = inj₂ $ just error -- userError
```

```
open import Data.Empty
open import Relation.Nullary

-- a value cannot make progress
{-
val-red : ∀{t : 0 ⊢} → Value t → ¬ (Σ (0 ⊢)  (t —→_))
val-red (V-F (V-ƛ t)) (t' , ())
--val-red (V-F (V-builtin b ts p)) (t' , ())
val-red (V-con tcn) (t' , ())
val-red (V-F (V-builtin b p q vs t)) (p' , q') = {!!}
val-red (V-builtin⋆ b p q vs t)      (p' , q') = {!!}
-}

{-
val-err : ∀{n}{t : n ⊢} → Value t → ¬ (Error t)
val-err (V-con tcn) ()
val-err (V-F (V-ƛ t)) ()
--val-err (V-F (V-builtin b ts p)) ()

err-red : ∀{n}{t : n ⊢} → Error t → ¬ (Σ (n ⊢)  (t —→_))
err-red E-error (_ , ())

valUniq : ∀{n}{t : n ⊢}(v v' : Value t) → v ≡ v'
valUniq (V-F (V-ƛ t)) (V-F (V-ƛ .t)) = refl
--valUniq (V-F (V-builtin b ts p)) (V-F (V-builtin .b .ts .p)) = refl
valUniq (V-con tcn) (V-con .tcn) = refl
valUniq V-delay V-delay = refl

det : ∀{n}{t t' t'' : n ⊢}(p : t —→ t')(q : t —→ t'') → t' ≡ t''

det (ξ-·₁ p) (ξ-·₁ q) = cong (_· _) (det p q)
det (ξ-·₁ p) (ξ-·₂ v q) = ⊥-elim (val-red (V-F v) (_ , p))
det (ξ-·₁ p) (E-·₂ v) = ⊥-elim (val-red (V-F v) (_ , p))
det (ξ-·₂ v p) (ξ-·₁ q) = ⊥-elim (val-red (V-F v) (_ , q))
det (ξ-·₂ v p) (ξ-·₂ w q) = cong (_ ·_) (det p q)
det (ξ-·₂ v p) (β-ƛ w) = ⊥-elim (val-red w (_ , p))
--det (ξ-·₂ v p) (sat-builtin w q) = ⊥-elim (val-red w (_ , p))
det (ξ-·₂ () p) E-con·
det (β-ƛ v) (ξ-·₂ w q) = ⊥-elim (val-red v (_ , q))
det (β-ƛ v) (β-ƛ w) = refl
det (β-ƛ (V-F ())) (E-·₂ v)
det (E-·₂ v) (β-ƛ (V-F ()))
{-
det (ξ-builtin b p) (ξ-builtin .b q) = cong (builtin b ≤‴-refl) (detT p q)
det (ξ-builtin b p) (β-builtin ts vs) = ⊥-elim (valT-redT vs (_ , p))
det (ξ-builtin b p) (E-builtin .b e q) = ⊥-elim (errT-redT q (_ , p))
det (β-builtin ts vs) (ξ-builtin b q) = ⊥-elim (valT-redT vs (_ , q))
det (β-builtin ts vs) (β-builtin .ts ws) = cong (BUILTIN _ ts) (valTUniq vs ws)
det (β-builtin ts vs) (E-builtin b v q) = ⊥-elim (valT-errT vs q)
det (sat-builtin v p) (ξ-·₂ w q) = ⊥-elim (val-red v (_ , q))
det (sat-builtin v p) (sat-builtin w .p) = refl
det (sat-builtin (V-F ()) p) (E-·₂ w)
-}
det E-·₁ E-·₁ = refl
det (E-·₂ v) (ξ-·₁ q) = ⊥-elim (val-red (V-F v) (_ , q))
--det (E-·₂ v) (sat-builtin (V-F ()) p)
det (E-·₂ v) (E-·₂ w) = refl
det (E-·₂ ()) E-con·
{-
det (E-builtin b ts p) (ξ-builtin .b q) = ⊥-elim (errT-redT p (_ , q))
det (E-builtin b ts p) (β-builtin ts vs) = ⊥-elim (valT-errT vs p)
det (E-builtin b ts p) (E-builtin .b w q) = refl
-}
det E-con· (ξ-·₂ () q)
det E-con· (E-·₂ ())
det E-con· E-con· = refl
det (ξ-force p) (ξ-force q) = cong force (det p q)
det (ξ-force ()) (E-FVal-force (V-ƛ t))
det β-delay β-delay = refl
det E-force E-force = refl
det E-con-force E-con-force = refl
det (E-FVal-force (V-ƛ t)) (ξ-force ())
det (E-FVal-force x) (E-FVal-force x₁) = refl
det E-delay· E-delay· = refl

--temporary
det (E-builtin .b) (E-builtin b) = refl
-}
```
