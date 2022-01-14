\begin{code}
{-# OPTIONS --rewriting #-}
module Algorithmic.Reduction where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to substEq)
open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Function hiding (_∋_)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_) renaming (_*_ to _**_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
open import Data.List as List using (List; _∷_; []; _++_)
open import Data.Bool using (Bool;true;false)
open import Data.Nat using (zero)
open import Data.Unit using (tt)
import Debug.Trace as Debug

open import Utils hiding (TermCon)
open import Type
import Type.RenamingSubstitution as T
open import Algorithmic.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Builtin
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *)
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Data.Maybe using (just;from-just)
open import Data.String using (String)
open import Algorithmic
open import Algorithmic.ReductionEC hiding (_—→_;_—↠_)
\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where

  ξ-·₁ : {A B : ∅ ⊢Nf⋆ *} {L L′ : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : {A B : ∅ ⊢Nf⋆ *}{V : ∅ ⊢ A ⇒ B} {M M′ : ∅ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′

  ξ-·⋆ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{L L' : ∅ ⊢ Π B}{A}
    → L —→ L'
      -----------------
    → L ·⋆ A / refl —→ L' ·⋆ A / refl

  β-ƛ : {A B : ∅ ⊢Nf⋆ *}{N : ∅ , A ⊢ B} {V : ∅ ⊢ A}
    → Value V
      -------------------
    → (ƛ N) · V —→ N [ V ]

  β-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{N : ∅ ,⋆ K ⊢ B}{A}
      -------------------
    → (Λ N) ·⋆ A / refl —→ N [ A ]⋆

  β-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : ∅ ⊢ _}
    → Value M
    → unwrap (wrap A B M) refl —→ M

  ξ-unwrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M M' : ∅ ⊢ μ A B}
    → M —→ M'
    → unwrap M refl —→ unwrap M' refl
    
  ξ-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M M' : ∅ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}
    → M —→ M'
    → wrap A B M —→ wrap A B M'

  E-·₂ : ∀{A B : ∅ ⊢Nf⋆ *}{L}{M}
    → M —→ error A
    → L · M —→ error B
  E-·₁ : ∀{A B : ∅ ⊢Nf⋆ *}{L}{M}
    → L —→ error (A ⇒ B)
    → L · M —→ error B
  E-·⋆ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{A : ∅ ⊢Nf⋆ K}
    → {M : _}
    → M —→ error (Π B)
    → M ·⋆ A / refl —→ error (B [ A ]Nf)
  E-unwrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : _}
    → M —→ error (μ A B)
    → unwrap M refl
        —→ error (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  E-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : _}
    → M —→ error _
    → wrap A B M —→ error (μ A B) 
  E-top : {A : ∅ ⊢Nf⋆ *} → error A —→ error A

  β-sbuiltin : ∀{A B}
      (b : Builtin)
    → (t : ∅ ⊢ A ⇒ B)
    → ∀{az}
    → (p : az <>> (Term ∷ []) ∈ arity b)
    → (bt : BApp b p t) -- one left
    → (u : ∅ ⊢ A)
    → (vu : Value u)
      -----------------------------
    → t · u —→ BUILTIN' b (bubble p) (BApp.step p bt vu)

  β-sbuiltin⋆ : ∀{B : ∅ ,⋆ K ⊢Nf⋆ *}{C}
      (b : Builtin)
    → (t : ∅ ⊢ Π B)
    → ∀{az}
    → (p : az <>> (Type ∷ []) ∈ arity b)
    → (bt : BApp b p t) -- one left
    → ∀ A
    → (q : C ≡ _)
      -----------------------------
    → t ·⋆ A / q —→ BUILTIN' b (bubble p) (BApp.step⋆ p bt q)
\end{code}

\begin{code}
data _—↠_ : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → ∅ ⊢ A → Set
  where

  refl—↠ : ∀{A}{M : ∅ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : ∅ ⊢Nf⋆ *}{M  M' M'' : ∅ ⊢ A}
    → M —→ M'
    → M' —↠ M''
      ---------
    → M —↠ M''
\end{code}

\begin{code}
lem—→⋆ : ∀{A}{M M' : ∅ ⊢ A} → M —→⋆ M' → M —→ M'
lem—→⋆ (β-ƛ v) = β-ƛ v
lem—→⋆ (β-Λ refl) = β-Λ
lem—→⋆ (β-wrap v refl) = β-wrap v
lem—→⋆ (β-sbuiltin b t p bt u vu) = β-sbuiltin b t p bt u vu
lem—→⋆ (β-sbuiltin⋆ b t p bt A q) = β-sbuiltin⋆ b t p bt A q

lemCS—→ : ∀{A}{M M' : ∅ ⊢ A} → M Algorithmic.ReductionEC.—→ M' → M —→ M'
lemCS—→ (ruleEC [] p refl refl) = lem—→⋆ p
lemCS—→ (ruleEC (E l· M) p refl refl) = ξ-·₁ (lemCS—→ (ruleEC E p refl refl))
lemCS—→ (ruleEC (V ·r E) p refl refl) = ξ-·₂ V (lemCS—→ (ruleEC E p refl refl))
lemCS—→ (ruleEC (E ·⋆ A / refl) p refl refl) = ξ-·⋆ (lemCS—→ (ruleEC E p refl refl))
lemCS—→ (ruleEC (wrap E) p refl refl) = ξ-wrap (lemCS—→ (ruleEC E p refl refl))
lemCS—→ (ruleEC (unwrap E / refl) p refl refl) =
  ξ-unwrap (lemCS—→ (ruleEC E p refl refl))
lemCS—→ (ruleErr [] refl) = E-top
lemCS—→ (ruleErr (E l· M) refl) = E-·₁ (lemCS—→ (ruleErr E refl))
lemCS—→ (ruleErr (V ·r E) refl) = E-·₂ (lemCS—→ (ruleErr E refl))
lemCS—→ (ruleErr (E ·⋆ A / refl) refl) = E-·⋆ (lemCS—→ (ruleErr E refl))
lemCS—→ (ruleErr (wrap E) refl) = E-wrap (lemCS—→ (ruleErr E refl))
lemCS—→ (ruleErr (unwrap E / refl) refl) = E-unwrap (lemCS—→ (ruleErr E refl))

{-
lemSC—→ : ∀{A}{M M' : ∅ ⊢ A} → M —→ M' → M Algorithmic.ReductionEC.—→ M'
lemSC—→ (ξ-·₁ X) = {!!}
lemSC—→ (ξ-·₂ x p) = {!!}
lemSC—→ (ξ-·⋆ p) with lemSC—→ p
... | ruleEC E p' refl refl = ruleEC (E ·⋆ _ / refl) p' refl refl
... | ruleErr E x = {!ruleErr!}
lemSC—→ (β-ƛ x) = ruleEC [] (β-ƛ x) refl refl 
lemSC—→ β-Λ = ruleEC [] (β-Λ refl) refl refl
lemSC—→ (β-wrap x) = ruleEC [] (β-wrap x refl) refl refl
lemSC—→ (ξ-unwrap p) = {!!}
lemSC—→ (ξ-wrap p) = {!!}
lemSC—→ (E-·₂ p) = {!!}
lemSC—→ (E-·₁ p) = {!!}
lemSC—→ (E-·⋆ p) = {!!}
lemSC—→ (E-unwrap p) = {!!}
lemSC—→ (E-wrap p) = {!!}
lemSC—→ E-top = {!!}
lemSC—→ (β-sbuiltin b t p bt u vu) = {!!}
lemSC—→ (β-sbuiltin⋆ b t p bt A q) = {!!}
-}

{-
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
\end{code}

\begin{code}
progress-·V :  {A B : ∅ ⊢Nf⋆ *}
  → {t : ∅ ⊢ A ⇒ B} → Value t
  → {u : ∅ ⊢ A} → Progress u
  → Progress (t · u)
progress-·V v       (step q)        = step (ξ-·₂ v q)
progress-·V v       (error E-error) = step (E-·₂ v)
progress-·V (V-ƛ t) (done w)        = step (β-ƛ w)
progress-·V (V-I⇒ b p q r σ base vs t) (done v) =
  step (β-sbuiltin b σ p q _ r t (deval v) vs v)
-- ^ we're done, call BUILTIN
progress-·V (V-I⇒ b p' q r σ (skip⋆ p) vs t) (done v) =
  done (V-IΠ b p' q r σ p (vs ,, deval v ,, v) (t · deval v))
progress-·V (V-I⇒ b p' q r σ (skip p)  vs t) (done v) =
  done (V-I⇒ b p' q r σ p (vs ,, deval v ,, v) (t · deval v))

progress-· :  {A B : ∅ ⊢Nf⋆ *}
  → {t : ∅ ⊢ A ⇒ B} → Progress t
  → {u : ∅ ⊢ A} → Progress u
  → Progress (t · u)
progress-· (step p)  q = step (ξ-·₁ p)
progress-· (done v)  q = progress-·V v q
progress-· (error E-error) q = step E-·₁

convValue : ∀{A A'}{t : ∅ ⊢ A}(p : A ≡ A') → Value (conv⊢ refl p t) → Value t
convValue refl v = v

ival : ∀ b → Value (builtin b / refl)
ival addInteger = V-I⇒ addInteger refl refl refl (λ()) (skip base) tt (builtin addInteger / refl)
ival subtractInteger = V-I⇒ subtractInteger refl refl refl (λ()) (skip base) tt (builtin subtractInteger / refl)
ival multiplyInteger = V-I⇒ multiplyInteger refl refl refl (λ()) (skip base) tt (builtin multiplyInteger / refl)
ival divideInteger = V-I⇒ divideInteger refl refl refl (λ()) (skip base) tt (builtin divideInteger / refl)
ival quotientInteger = V-I⇒ quotientInteger refl refl refl (λ()) (skip base) tt (builtin quotientInteger / refl)
ival remainderInteger = V-I⇒ remainderInteger refl refl refl (λ()) (skip base) tt (builtin remainderInteger / refl)
ival modInteger = V-I⇒ modInteger refl refl refl (λ()) (skip base) tt (builtin modInteger / refl)
ival lessThanInteger = V-I⇒ lessThanInteger refl refl refl (λ()) (skip base) tt (builtin lessThanInteger / refl)
ival lessThanEqualsInteger = V-I⇒ lessThanEqualsInteger refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (builtin lessThanEqualsInteger / refl)
ival equalsInteger = V-I⇒ equalsInteger refl refl refl (λ()) (skip base) tt (builtin equalsInteger / refl)
ival lessThanByteString = V-I⇒ lessThanByteString refl refl refl (λ()) (skip base) tt (builtin lessThanByteString / refl)
ival lessThanEqualsByteString = V-I⇒ lessThanEqualsByteString refl refl refl (λ()) (≤Cto≤C' (skip base)) tt (builtin lessThanEqualsByteString / refl)
ival sha2-256 = V-I⇒ sha2-256 refl refl refl (λ()) base tt (builtin sha2-256 / refl)
ival sha3-256 = V-I⇒ sha3-256 refl refl refl (λ()) base tt (builtin sha3-256 / refl)
ival verifySignature = V-I⇒ verifySignature refl refl refl (λ()) (skip (skip base)) tt (builtin verifySignature / refl)
ival equalsByteString = V-I⇒ equalsByteString refl refl refl (λ()) (skip base) tt (builtin equalsByteString / refl)
ival appendByteString = V-I⇒ appendByteString refl refl refl (λ()) (skip base) tt (builtin appendByteString / refl)
ival appendString = V-I⇒ appendString refl refl refl (λ()) (skip base) tt (builtin appendString / refl)
ival ifThenElse = V-IΠ ifThenElse refl refl refl (λ()) (skip (skip (skip base))) tt (builtin ifThenElse / refl)
ival trace = V-IΠ trace refl refl refl (λ()) (skip (skip base)) tt (builtin trace / refl)
ival equalsString = V-I⇒ equalsString refl refl refl (λ()) (skip base) tt (builtin equalsString / refl)
ival encodeUtf8 = V-I⇒ encodeUtf8 refl refl refl (λ()) base tt (builtin encodeUtf8 / refl)
ival decodeUtf8 = V-I⇒ decodeUtf8 refl refl refl (λ()) base tt (builtin decodeUtf8 / refl)
ival fstPair = V-IΠ fstPair refl refl refl (λ()) (skip⋆ (skip base)) tt (builtin fstPair / refl)
ival sndPair = V-IΠ sndPair refl refl refl (λ()) (skip⋆ (skip base)) tt (builtin sndPair / refl)
ival nullList = V-IΠ nullList refl refl refl (λ()) (skip base) tt (builtin nullList / refl)
ival headList = V-IΠ headList refl refl refl (λ()) (skip base) tt (builtin headList / refl)
ival tailList = V-IΠ tailList refl refl refl (λ()) (skip base) tt (builtin tailList / refl)
ival chooseList = V-IΠ chooseList refl refl refl (λ()) (skip⋆ (skip (skip (skip base)))) tt (builtin chooseList / refl)
ival constrData = V-I⇒ constrData refl refl refl (λ()) (skip base) tt (builtin constrData / refl)
ival mapData = V-I⇒ mapData refl refl refl (λ()) base tt (builtin mapData / refl)
ival listData = V-I⇒ listData refl refl refl (λ()) base tt (builtin listData / refl)
ival iData = V-I⇒ iData refl refl refl (λ()) base tt (builtin iData / refl)
ival bData = V-I⇒ bData refl refl refl (λ()) base tt (builtin bData / refl)
ival unConstrData = V-I⇒ unConstrData refl refl refl (λ()) base tt (builtin unConstrData / refl)
ival unMapData = V-I⇒ unMapData refl refl refl (λ()) base tt (builtin unMapData / refl) 
ival unListData = V-I⇒ unListData refl refl refl (λ()) base tt (builtin unListData / refl)
ival unIData = V-I⇒ unIData refl refl refl (λ()) base tt (builtin unIData / refl)
ival unBData = V-I⇒ unBData refl refl refl (λ()) base tt (builtin unBData / refl)
ival equalsData = V-I⇒ equalsData refl refl refl (λ()) (skip base) tt (builtin equalsData / refl)
ival chooseData = V-IΠ chooseData refl refl refl (λ()) (skip (skip (skip (skip (skip (skip base)))))) tt (builtin chooseData / refl)
ival chooseUnit = V-IΠ chooseUnit refl refl refl (λ()) (skip (skip base)) tt (builtin chooseUnit / refl)
ival mkPairData = V-I⇒ mkPairData refl refl refl (λ()) (skip base) tt (builtin mkPairData / refl)
ival mkNilData = V-I⇒ mkNilData refl refl refl (λ()) base tt (builtin mkNilData / refl)
ival mkNilPairData = V-I⇒ mkNilPairData refl refl refl (λ()) base tt (builtin mkNilPairData / refl)
ival mkCons = V-I⇒ mkCons refl refl refl (λ()) (skip base) tt (builtin mkCons / refl)
ival consByteString = V-I⇒ consByteString refl refl refl (λ()) (skip base) tt (builtin consByteString / refl)
ival sliceByteString = V-I⇒ sliceByteString refl refl refl (λ()) (skip (skip base)) tt (builtin sliceByteString / refl)
ival lengthOfByteString = V-I⇒ lengthOfByteString refl refl refl (λ()) base tt (builtin lengthOfByteString / refl)
ival indexByteString = V-I⇒ indexByteString refl refl refl (λ()) (skip base) tt (builtin indexByteString / refl)
ival blake2b-256 = V-I⇒ blake2b-256 refl refl refl (λ()) base tt (builtin blake2b-256 / refl)

progress-·⋆ : ∀{K B}{t : ∅ ⊢ Π B} → Progress t → (A : ∅ ⊢Nf⋆ K)
  → Progress (t ·⋆ A / refl)
progress-·⋆ (step p)        A = step (ξ-·⋆ p)
progress-·⋆ (done (V-Λ t))  A = step β-Λ
progress-·⋆ (error E-error) A = step E-·⋆
progress-·⋆ (done (V-IΠ b {C = C} p' q r σ (skip⋆ p) vs t)) A = done (convValue (Πlem p A C σ) (V-IΠ b {C = C} p' q r (subNf-cons σ A) p (vs ,, A) (conv⊢ refl (Πlem p A C σ) (t ·⋆ A / refl))) )
progress-·⋆ (done (V-IΠ b {C = C} p' q r σ (skip p) vs t))  A = done (convValue (⇒lem p σ C) (V-I⇒ b p' q r (subNf-cons σ A) p (vs ,, A) (conv⊢ refl (⇒lem p σ C) (t ·⋆ A / refl))))
progress-·⋆ (done (V-IΠ b p q r σ base vs t)) A = step (β-sbuiltin⋆ b σ p q _ r t vs)
-- ^ it's the last one, call BUILTIN

progress-unwrap : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}{t : ∅ ⊢ μ A B}
  → Progress t → Progress (unwrap t refl)
progress-unwrap (step q) = step (ξ-unwrap q)
progress-unwrap (done (V-wrap v)) = step (β-wrap v)
progress-unwrap {A = A} (error E-error) =
  step (E-unwrap {A = A})

progress : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M
progress-wrap : ∀{K}
   → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : ∅ ⊢Nf⋆ K}
   → {M : ∅ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}
   → Progress M → Progress (wrap A B M)
progress-wrap (step p)        = step (ξ-wrap p)
progress-wrap (done v)        = done (V-wrap v)
progress-wrap (error E-error) = step E-wrap
progress (ƛ M)                = done (V-ƛ M)
progress (M · N)              = progress-· (progress M) (progress N)
progress (Λ M)                = done (V-Λ M)
progress (M ·⋆ A / refl)             = progress-·⋆ (progress M) A
progress (wrap A B M) = progress-wrap (progress M)
progress (unwrap M refl)          = progress-unwrap (progress M)
progress (con c)              = done (V-con c)
progress (builtin b / refl) = done (ival b)
progress (error A)            = error E-error

open import Data.Nat
progressor : ℕ → ∀{A} → (t : ∅ ⊢ A) → Either RuntimeError (Maybe (∅ ⊢ A))
progressor zero t = inj₁ gasError
progressor (suc n) t with progress t
... | step {N = t'} _ = progressor n t'
... | done v = inj₂ (just (deval v))
... | error _ = inj₂ nothing -- should this be an runtime error?
-}
