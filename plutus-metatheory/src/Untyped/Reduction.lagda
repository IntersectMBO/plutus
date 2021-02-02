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
import Data.List as List
open import Data.Vec using (Vec;[];_∷_;_++_)
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
import Debug.Trace as Debug
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utils
open import Data.Fin using ()
\end{code}

\begin{code}
infix 2 _—→_
\end{code}

\begin{code}
subst∷ : ∀{n n'}{A : Set}(a : A)(as : Vec A n)(p : n ≡ n')(q : suc n ≡ suc n')
  → a ∷ subst (Vec A) p as ≡ subst (Vec A) q (a ∷ as)
subst∷ a as refl refl = refl
\end{code}


\begin{code}
-- for untyped reduction, error also includes thing like impossible
-- applications
data Error {n} : n ⊢ → Set where
  E-error : Error error

\end{code}

\begin{code}
-- I cannot remember why there is both a FValue and a Value...
data FValue {n} : n ⊢ → Set where
  V-ƛ : (t : suc n ⊢) → FValue (ƛ t)
--  V-builtin : (b : Builtin) → FValue (builtin b)


data Value {n} : n ⊢ → Set where
  V-F     : {t : n ⊢} → FValue t → Value t
  V-delay : {t : n ⊢} → Value (delay t)
  V-con   : (tcn : TermCon) → Value (con {n} tcn)


data _—→_ {n} : n ⊢ → n ⊢ → Set where
  ξ-·₁ : {L L' M : n ⊢} → L —→ L' → L · M —→ L' · M
  ξ-·₂ : {L M M' : n ⊢} → FValue L → M —→ M' → L · M —→ L · M'

  β-ƛ : ∀{L : suc n ⊢}{V : n ⊢} → Value V → ƛ L · V —→ L [ V ]

  ξ-force : {L L' : n ⊢} → L —→ L' → force L —→ force L'

  β-delay : {L : n ⊢} → force (delay L) —→ L

{-
  ξ-builtin : (b : Builtin)
              {ts ts' : Tel (arity b) n}
            → ts —→T ts'
            → builtin b ≤‴-refl ts —→ builtin b ≤‴-refl ts'

  β-builtin : {b : Builtin}
              (ts : Tel (arity b) n)
            → (vs : VTel (arity b) n ts)
            → builtin b ≤‴-refl ts —→ BUILTIN b ts vs

  sat-builtin : {b : Builtin}
              → ∀{l}
                {ts : Tel l n}
                {t : n ⊢}
              → Value t
              → (p : l <‴ arity b)
              → builtin b (≤‴-step p) ts · t —→ builtin b p (ts :< t)
-}
  E-·₁ : {M : n ⊢} → error · M —→ error
  E-·₂ : {L : n ⊢} → FValue L → L · error —→ error

  E-force : force error —→ error


  E-builtin : (b : Builtin)
            → builtin b —→ error

  -- these correspond to type errors encountered at runtime
  E-con· : {tcn : TermCon}{L : n ⊢} → con tcn · L —→ error
  E-con-force : {tcn : TermCon} → force (con tcn) —→ error
  E-FVal-force : {L : n ⊢} → FValue L → force L —→ error
  E-delay· : {L M : n ⊢} → delay L · M —→ error

  -- this is a runtime type error that ceases to be a type error after erasure
  -- E-runtime : {L : n ⊢} → L —→ error

\end{code}


\begin{code}
data _—→⋆_ {n} : n ⊢ → n ⊢ → Set where
  refl  : {t : n ⊢} → t —→⋆ t
  trans—→⋆ : {t t' t'' : n ⊢} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
VERIFYSIG : ∀{n} → Maybe Bool → n ⊢
VERIFYSIG (just Bool.false) = con (bool false)
VERIFYSIG (just Bool.true)  = con (bool true)
VERIFYSIG nothing           = error

{-
BUILTIN addInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , _)
  = con (integer (i + j))
BUILTIN subtractInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , _)
  = con (integer (i - j))
BUILTIN multiplyInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , _)
  = con (integer (i * j))
BUILTIN divideInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , _)
  = decIf (∣ j ∣ Data.Nat.≟ zero) error (con (integer (div i j)))
BUILTIN quotientInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , _)
  = decIf (∣ j ∣ Data.Nat.≟ zero) error (con (integer (quot i j)))
BUILTIN remainderInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , _)
  = decIf (∣ j ∣ Data.Nat.≟ zero) error (con (integer (rem i j)))
BUILTIN modInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , _)
  = decIf (∣ j ∣ Data.Nat.≟ zero) error (con (integer (mod i j)))
BUILTIN lessThanInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i <? j) (con (bool true)) (con (bool false))
BUILTIN lessThanEqualsInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i ≤? j) (con (bool true)) (con (bool false))
BUILTIN greaterThanInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i I>? j) (con (bool true)) (con (bool false))
BUILTIN greaterThanEqualsInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i I≥? j) (con (bool true)) (con (bool false))
BUILTIN equalsInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i ≟ j) (con (bool true)) (con (bool false))
BUILTIN concatenate (_ ∷ _ ∷ []) (V-con (bytestring b) , V-con (bytestring b') , tt) =
  con (bytestring (concat b b'))
BUILTIN takeByteString (_ ∷ _ ∷ []) (V-con (integer i) , V-con (bytestring b) , tt) =
  con (bytestring (take i b))
BUILTIN dropByteString (_ ∷ _ ∷ []) (V-con (integer i) , V-con (bytestring b) , tt) =
  con (bytestring (drop i b))
BUILTIN sha2-256 (_ ∷ []) (V-con (bytestring b) , tt) = con (bytestring (SHA2-256 b))
BUILTIN sha3-256 (_ ∷ []) (V-con (bytestring b) , tt) = con (bytestring (SHA3-256 b))
BUILTIN verifySignature (_ ∷ _ ∷ _ ∷ []) (V-con (bytestring k) , V-con (bytestring d) , V-con (bytestring c) , tt) = VERIFYSIG (verifySig k d c)
BUILTIN equalsByteString (_ ∷ _ ∷ []) (V-con (bytestring b) , V-con (bytestring b') , tt) =
  con (bool (equals b b'))
BUILTIN ifThenElse (_ ∷ _ ∷ t ∷ _ ∷ []) (_ , V-con (bool true)  , vt , _ , tt) = t
BUILTIN ifThenElse (_ ∷ _ ∷ _ ∷ u ∷ []) (_ , V-con (bool false) , _ , vu , tt) = u
BUILTIN charToString (_ ∷ []) (V-con (char c) , tt) = con (string (primStringFromList List.[ c ]))
BUILTIN append (_ ∷ _ ∷ []) (V-con (string s) , V-con (string t) , tt) =
  con (string (primStringAppend s t))
BUILTIN trace (_ ∷ []) (V-con (string s) , tt) = con (Debug.trace s unit)
BUILTIN _ _ _ = error
-}

data Progress {n}(M : n ⊢) : Set where
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

progress-·V : ∀{n}
  → {t : n ⊢} → Value t
  → {u : n ⊢} → Progress u
  → Progress (t · u)
progress-·V (V-con tcn)              v               = step E-con·
progress-·V (V-F v)                  (step q)        = step (ξ-·₂ v q)
progress-·V (V-F v)                  (error E-error) = step (E-·₂ v)
progress-·V (V-F (V-ƛ t))            (done v)        = step (β-ƛ v)
progress-·V V-delay                  v               = step E-delay·
--progress-·V (V-F (V-builtin b ts p)) (done v)        = step (sat-builtin v p)

progress-· : ∀{n}
  → {t : n ⊢} → Progress t
  → {u : n ⊢} → Progress u
  → Progress (t · u)
progress-· (done v)        q = progress-·V v q
progress-· (step p)        q = step (ξ-·₁ p)
progress-· (error E-error) q = step E-·₁

progress-forceV : ∀{n}
  → {t : n ⊢} → Value t
  → Progress (force t)
progress-forceV (V-F V)     = step (E-FVal-force V)
progress-forceV V-delay     = step β-delay
progress-forceV (V-con tcn) = step E-con-force

progress-force : ∀{n}
  → {t : n ⊢} → Progress t
  → Progress (force t)
progress-force (done v)        = progress-forceV v
progress-force (step p)        = step (ξ-force p)
progress-force (error E-error) = step E-force


progress : (t : 0 ⊢) → Progress t
progress (` ())
progress (ƛ t)        = done (V-F (V-ƛ t))
progress (t · u)      = progress-· (progress t) (progress u)
progress (force t)    = progress-force (progress t)
progress (delay t)    = done V-delay
progress (builtin b)  = step (E-builtin b)
progress (con tcn)    = done (V-con tcn)
{-
progress (builtin b ≤‴-refl ts) with progressTel ts
progress (builtin b ≤‴-refl ts) | done vs = step (β-builtin ts vs)
progress (builtin b ≤‴-refl ts) | step p = step (ξ-builtin b p)
progress (builtin b ≤‴-refl ts) | error p = step (E-builtin b ts p)
progress (builtin b (≤‴-step p) ts) = done (V-F (V-builtin b ts p))
-}
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
open import Data.Empty
open import Relation.Nullary

-- a value cannot make progress
val-red : ∀{n}{t : n ⊢} → Value t → ¬ (Σ (n ⊢)  (t —→_))
val-red (V-F (V-ƛ t)) (t' , ())
--val-red (V-F (V-builtin b ts p)) (t' , ())
val-red (V-con tcn) (t' , ())

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

\end{code}
