\begin{code}
module Untyped.Reduction where
\end{code}

\begin{code}
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
\end{code}

\begin{code}
infix 2 _—→_
\end{code}

\begin{code}
data Label : Set where
  Type : Label
  Term : Label

data Bwd (A : Set) : Set where
  [] : Bwd A
  _:<_ : Bwd A → A → Bwd A

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
  base : ∀{L} → L ≤L L
  skipType : ∀{L L'} → L :< Type ≤L L' → L ≤L L'
  skipTerm : ∀{L L'} → L :< Term ≤L L' → L ≤L L'

infix 5 _≤L_

-- for untyped reduction, error also includes thing like impossible
-- applications
data Error {n} : n ⊢ → Set where
  E-error : Error error

\end{code}

\begin{code}
ITel : Builtin → Bwd Label → Set

-- I cannot remember why there is both a FValue and a Value...
data FValue : 0 ⊢ → Set where
  V-ƛ : (t : suc 0 ⊢)
      → FValue (ƛ t)
  V-builtin : (b : Builtin)
            → ∀ {L L'}
            → L' ≡ arity b
            → L :< Term ≤L L'
            → ITel b L
            → (t : 0 ⊢)
            → FValue t

data Value  : 0 ⊢ → Set where
  V-F     : {t : 0 ⊢} → FValue t → Value t
  V-delay : {t : 0 ⊢} → Value (delay t)
  V-con   : (tcn : TermCon) → Value (con tcn)
  V-builtin⋆ : (b : Builtin)
            → ∀ {L L'}
            → L' ≡ arity b
            → L :< Type ≤L L'
            → ITel b L
            → (t : 0 ⊢)
            → Value t
  

ITel b []          = ⊤
ITel b (L :< Type) = ITel b L
ITel b (L :< Term) = ITel b L × Σ (0 ⊢) Value

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

IBUILTIN' : (b : Builtin) → ∀{L} → L ≡ arity b → ITel b L → Σ (0 ⊢) λ t → Value t ⊎ Error t
IBUILTIN' b refl vs = IBUILTIN b vs


data _—→_ : 0 ⊢ → 0 ⊢ → Set where
  ξ-·₁ : {L L' M : 0 ⊢} → L —→ L' → L · M —→ L' · M
  ξ-·₂ : {L M M' : 0 ⊢} → FValue L → M —→ M' → L · M —→ L · M'

  β-ƛ : ∀{L : suc 0 ⊢}{V : 0 ⊢} → Value V → ƛ L · V —→ L [ V ]

  ξ-force : {L L' : 0 ⊢} → L —→ L' → force L —→ force L'

  β-delay : {L : 0 ⊢} → force (delay L) —→ L

  β-builtin : (b : Builtin)
            → ∀ {L} t
            → (p : L :< Term ≡ arity b)
            → (vs : ITel b L)
            → ∀ {u} v
            → t · u —→ fst (IBUILTIN' b p (vs , u , v))

  β-builtin⋆ : (b : Builtin)
            → ∀ {L} t
            → (p : L :< Type ≡ arity b)
            → (vs : ITel b L)
            → force t —→ fst (IBUILTIN' b p vs)


  E-·₁ : {M : 0 ⊢} → error · M —→ error
  E-·₂ : {L : 0 ⊢} → FValue L → L · error —→ error

  E-force : force error —→ error


  E-builtin⋆· : (b : Builtin)
              → ∀ t u
              -- TODO: more conditions required
              → t · u —→ error

  -- these correspond to type errors encountered at runtime
  E-con· : {tcn : TermCon}{L : 0 ⊢} → con tcn · L —→ error
  E-con-force : {tcn : TermCon} → force (con tcn) —→ error
  E-FVal-force : {L : 0 ⊢} → FValue L → force L —→ error
  E-delay· : {L M : 0 ⊢} → delay L · M —→ error

  -- this is a runtime type error that ceases to be a type error after erasure
  -- E-runtime : {L : n ⊢} → L —→ error

\end{code}


\begin{code}
data _—→⋆_ : 0 ⊢ → 0 ⊢ → Set where
  refl  : {t : 0 ⊢} → t —→⋆ t
  trans—→⋆ : {t t' t'' : 0 ⊢} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
data Progress (M : 0 ⊢) : Set where
  step : ∀{N}
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

progress-·V :
    {t : 0 ⊢} → Value t
  → {u : 0 ⊢} → Progress u
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

progress-· :
    {t : 0 ⊢} → Progress t
  → {u : 0 ⊢} → Progress u
  → Progress (t · u)
progress-· (done v)        q = progress-·V v q
progress-· (step p)        q = step (ξ-·₁ p)
progress-· (error E-error) q = step E-·₁

progress-forceV :
    {t : 0 ⊢} → Value t
  → Progress (force t)
progress-forceV (V-F V)     = step (E-FVal-force V)
progress-forceV V-delay     = step β-delay
progress-forceV (V-con tcn) = step E-con-force
progress-forceV (V-builtin⋆ b p base vs t) =
  step (β-builtin⋆ b t p vs)
progress-forceV (V-builtin⋆ b p (skipTerm q) vs t) =
  done (V-F (V-builtin b p q vs (force t)))
progress-forceV (V-builtin⋆ b p (skipType q) vs t) =
  done (V-builtin⋆ b p q vs (force t))

progress-force :
    {t : 0 ⊢} → Progress t
  → Progress (force t)
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
\end{code}

\begin{code}
run : ∀(t : 0 ⊢) → ℕ
  → Σ (0 ⊢) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')
run t 0       = t , refl , inl nothing
run t (suc n) with progress t
run t (suc n) | done vt = t , refl , inl (just vt)
run t (suc n) | error et = t , refl , inr et
run t (suc n) | step {N = t'} p with run t' n
run t (suc n) | step p | t'' , q , mvt'' = t'' , trans—→⋆ p q , mvt''
\end{code}

\begin{code}
deval : ∀{t} → Value t → 0 ⊢
deval {t} _ = t

progressor : ℕ → (t : 0 ⊢) → Either RuntimeError (Maybe (0 ⊢))
progressor 0       t = inj₁ gasError
progressor (suc n) t with progress t
... | step {N = t'} p  = progressor n t'
... | done v  = inj₂ $ just (deval v)
... | error e = inj₁ userError
\end{code}

\begin{code}
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
\end{code}
