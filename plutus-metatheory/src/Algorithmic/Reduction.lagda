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
import Algorithmic.ReductionEC as E
\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→V_

data _—→V_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where

  ξ-·₁ : {A B : ∅ ⊢Nf⋆ *} {L L′ : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A}
    → L —→V L′
      -----------------
    → L · M —→V L′ · M

  ξ-·₂ : {A B : ∅ ⊢Nf⋆ *}{V : ∅ ⊢ A ⇒ B} {M M′ : ∅ ⊢ A}
    → Value V
    → M —→V M′
      --------------
    → V · M —→V V · M′

  ξ-·⋆ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{L L' : ∅ ⊢ Π B}{A}
    → L —→V L'
      -----------------
    → L ·⋆ A / refl —→V L' ·⋆ A / refl

  β-ƛ : {A B : ∅ ⊢Nf⋆ *}{N : ∅ , A ⊢ B} {V : ∅ ⊢ A}
    → Value V
      -------------------
    → (ƛ N) · V —→V N [ V ]

  β-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{N : ∅ ,⋆ K ⊢ B}{A}
      -------------------
    → (Λ N) ·⋆ A / refl —→V N [ A ]⋆

  β-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : ∅ ⊢ _}
    → Value M
    → unwrap (wrap A B M) refl —→V M

  ξ-unwrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M M' : ∅ ⊢ μ A B}
    → M —→V M'
    → unwrap M refl —→V unwrap M' refl
    
  ξ-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M M' : ∅ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}
    → M —→V M'
    → wrap A B M —→V wrap A B M'

  β-sbuiltin : ∀{A B}
      (b : Builtin)
    → (t : ∅ ⊢ A ⇒ B)
    → ∀{az}
    → (p : az <>> (Term ∷ []) ∈ arity b)
    → (bt : BApp b p t) -- one left
    → (u : ∅ ⊢ A)
    → (vu : Value u)
      -----------------------------
    → t · u —→V BUILTIN' b (bubble p) (BApp.step p bt vu)

  β-sbuiltin⋆ : ∀{B : ∅ ,⋆ K ⊢Nf⋆ *}{C}
      (b : Builtin)
    → (t : ∅ ⊢ Π B)
    → ∀{az}
    → (p : az <>> (Type ∷ []) ∈ arity b)
    → (bt : BApp b p t) -- one left
    → ∀ A
    → (q : C ≡ _)
      -----------------------------
    → t ·⋆ A / q —→V BUILTIN' b (bubble p) (BApp.step⋆ p bt q)
\end{code}

\begin{code}
infix 2 _—→E_

data _—→E_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where
  E-·₂ : ∀{A B : ∅ ⊢Nf⋆ *}{L M}
    → Value L
    → M —→E error A
    → L · M —→E error B
  E-·₁ : ∀{A B : ∅ ⊢Nf⋆ *}{L M}
    → L —→E error (A ⇒ B)
    → L · M —→E error B
  E-·⋆ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{A : ∅ ⊢Nf⋆ K}{L}
    → L —→E error (Π B)
    → L ·⋆ A / refl —→E error _
  E-unwrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : _}
    → M —→E error (μ A B)
    → unwrap M refl —→E error _
  E-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : _}
    → M —→E error _
    → wrap A B M —→E error (μ A B) 
  E-top : {A : ∅ ⊢Nf⋆ *} → error A —→E error A
\end{code}


\begin{code}
infix 2 _—→_

data _—→_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where
  red : {A : ∅ ⊢Nf⋆ *}{M  M' : ∅ ⊢ A}
    → M —→V M' → M —→ M'
  err : {A : ∅ ⊢Nf⋆ *}{M : ∅ ⊢ A}
    → M —→E error A → M —→ error A

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
lem—→⋆ : ∀{A}{M M' : ∅ ⊢ A} → M —→⋆ M' → M —→V M'
lem—→⋆ (β-ƛ v) = β-ƛ v
lem—→⋆ (β-Λ refl) = β-Λ
lem—→⋆ (β-wrap v refl) = β-wrap v
lem—→⋆ (β-sbuiltin b t p bt u vu) = β-sbuiltin b t p bt u vu
lem—→⋆ (β-sbuiltin⋆ b t p bt A q) = β-sbuiltin⋆ b t p bt A q

lemCS—→V : ∀{A}
         → ∀{B}{L L' : ∅ ⊢ B}
         → (E : EC A B)
         → L —→⋆ L'
         → E [ L ]ᴱ —→V E [ L' ]ᴱ
lemCS—→V [] p = lem—→⋆ p
lemCS—→V (E l· M) p = ξ-·₁ (lemCS—→V E p)
lemCS—→V (V ·r E) p = ξ-·₂ V (lemCS—→V E p)
lemCS—→V (E ·⋆ A / refl) p = ξ-·⋆ (lemCS—→V E p)
lemCS—→V (wrap E) p = ξ-wrap (lemCS—→V E p)
lemCS—→V (unwrap E / refl) p = ξ-unwrap (lemCS—→V E p)

lemCS—→E : ∀{A B}
         → (E : EC A B)
         → E [ error B ]ᴱ —→E error A
lemCS—→E [] = E-top
lemCS—→E (E l· M) = E-·₁ (lemCS—→E E)
lemCS—→E (V ·r E) = E-·₂ V (lemCS—→E E)
lemCS—→E (E ·⋆ A / refl) = E-·⋆ (lemCS—→E E)
lemCS—→E (wrap E) = E-wrap (lemCS—→E E)
lemCS—→E (unwrap E / refl) = E-unwrap (lemCS—→E E)

lemCS—→ : ∀{A}{M M' : ∅ ⊢ A} → M E.—→ M' → M —→ M'
lemCS—→ (ruleEC E p refl refl) = red (lemCS—→V E p)
lemCS—→ (ruleErr E refl) = err (lemCS—→E E)

lemSC—→V : ∀{A}{M M' : ∅ ⊢ A}
  → M —→V M'
  → ∃ λ B 
  → ∃ λ (E : EC A B)
  → ∃ λ L
  → ∃ λ L'
  → (M ≡ E [ L ]ᴱ) × (M' ≡ E [ L' ]ᴱ) × (L —→⋆ L')
lemSC—→V (ξ-·₁ p) with lemSC—→V p
... | B ,, E ,, L ,, L' ,, refl ,, refl ,, q =
  B ,, E l· _ ,, L ,, L' ,, refl ,, refl ,, q
lemSC—→V (ξ-·₂ v p) with lemSC—→V p
... | B ,, E ,, L ,, L' ,, refl ,, refl ,, q =
  B ,, v ·r E ,, L ,, L' ,, refl ,, refl ,, q
lemSC—→V (ξ-·⋆ p) with lemSC—→V p
... | B ,, E ,, L ,, L' ,, refl ,, refl ,, q =
  B ,, E ·⋆ _ / refl ,, L ,, L' ,, refl ,, refl ,, q
lemSC—→V (β-ƛ v) = _ ,, [] ,, _ ,, _ ,, refl ,, refl ,, E.β-ƛ v
lemSC—→V β-Λ = _ ,, [] ,, _ ,, _ ,, refl ,, refl ,, E.β-Λ refl
lemSC—→V (β-wrap v) = _ ,, [] ,, _ ,, _ ,, refl ,, refl ,, E.β-wrap v refl
lemSC—→V (ξ-unwrap p) with lemSC—→V p
... | B ,, E ,, L ,, L' ,, refl ,, refl ,, q =
  B ,, unwrap E / refl ,, L ,, L' ,, refl ,, refl ,, q
lemSC—→V (ξ-wrap p) with lemSC—→V p
... | B ,, E ,, L ,, L' ,, refl ,, refl ,, q =
  B ,, wrap E ,, L ,, L' ,, refl ,, refl ,, q
lemSC—→V (β-sbuiltin b t p bt u vu) =
  _ ,, [] ,, _ ,, _ ,, refl ,, refl ,, E.β-sbuiltin b t p bt u vu
lemSC—→V (β-sbuiltin⋆ b t p bt A q) =
  _ ,, [] ,, _ ,, _ ,, refl ,, refl ,, E.β-sbuiltin⋆ b t p bt A q

lemSC—→E : ∀{A}{M : ∅ ⊢ A}
  → M —→E error A
  → ∃ λ B 
  → ∃ λ (E : EC A B)
  → (M ≡ E [ error B ]ᴱ)
lemSC—→E (E-·₂ v p) with lemSC—→E p
... | B ,, E ,, refl = B ,, v ·r E ,, refl
lemSC—→E (E-·₁ p) with lemSC—→E p
... | B ,, E ,, refl = B ,, E l· _ ,, refl
lemSC—→E (E-·⋆ p) with lemSC—→E p
... | B ,, E ,, refl = B ,, E ·⋆ _ / refl ,, refl
lemSC—→E (E-unwrap p) with lemSC—→E p
... | B ,, E ,, refl = B ,, unwrap E / refl ,, refl
lemSC—→E (E-wrap p) with lemSC—→E p
... | B ,, E ,, refl = B ,, wrap E ,, refl
lemSC—→E E-top = _ ,, [] ,, refl

lemSC—→ : ∀{A}{M M' : ∅ ⊢ A} → M —→ M' → M E.—→ M'
lemSC—→ (red p) =
  let B ,, E ,, L ,, L' ,, r ,, r' ,, q = lemSC—→V p in ruleEC E q r r'
lemSC—→ (err p) = let B ,, E ,, p = lemSC—→E p in ruleErr E p 

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

-- -}
