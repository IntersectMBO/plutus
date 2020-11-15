\begin{code}
module Untyped.Reduction where
\end{code}

\begin{code}
open import Untyped
open import Untyped.RenamingSubstitution
open import Builtin
open import Builtin.Constant.Type hiding (length)

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
data FValue {n} : n ⊢ → Set where
  V-ƛ : (t : suc n ⊢) → FValue (ƛ t)
  V-builtin : (b : Builtin)
              → ∀{l}
              → (ts : Tel l n)
              → (p : l <‴ arity b)
              → FValue (builtin b (≤‴-step p) ts)

data Value {n} : n ⊢ → Set where
  V-F   : {t : n ⊢} → FValue t → Value t
  V-con : (tcn : TermCon) → Value (con {n} tcn)


-- membership of a (partially evaluated) telescope:

{-
data Any {p} (P : A → Set p) : ∀ {n} → Vec A n → Set (a ⊔ p) where
  here  : ∀ {n x} {xs : Vec A n} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {n x} {xs : Vec A n} (pxs : Any P xs) → Any P (x ∷ xs)
-}

-- as well as being like `Any` for `Vec`, this also ensures that the
-- prefix of the telescope is made of values

data Any {n : ℕ}(P : n ⊢ → Set) : ∀{m} → Tel m n → Set where
  here  : ∀{m t}{ts : Tel m n} → P t → Any P (t ∷ ts)
  there : ∀{m t}{ts : Tel m n} → Value t → Any P ts → Any P (t ∷ ts)

-- this also goes beyond membership of `Vec` by ensuring the prefix is
-- made of values

_∈_ : {m n : ℕ} → n ⊢ → Tel m n → Set
t ∈ ts = Any (_≡ t) ts

VTel : ∀ l n → Tel l n → Set
VTel 0       n []       = ⊤
VTel (suc l) n (t ∷ ts) = Value {n} t × VTel l n ts

BUILTIN : ∀{n}
    → (b : Builtin)
    → (tel : Tel (arity b) n)
    → VTel (arity b) n tel
      --------------
    → n ⊢

data _—→T_ {n} : ∀{m} → Tel m n → Tel m n → Set

data _—→_ {n} : n ⊢ → n ⊢ → Set where
  ξ-·₁ : {L L' M : n ⊢} → L —→ L' → L · M —→ L' · M
  ξ-·₂ : {L M M' : n ⊢} → FValue L → M —→ M' → L · M —→ L · M'

  β-ƛ : ∀{L : suc n ⊢}{V : n ⊢} → Value V → ƛ L · V —→ L [ V ]

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

  E-·₁ : {M : n ⊢} → error · M —→ error
  E-·₂ : {L : n ⊢} → FValue L → L · error —→ error

  E-builtin : (b : Builtin)
              (ts : Tel (arity b) n)
            → Any Error ts
            → builtin b ≤‴-refl ts —→ error

  -- these correspond to type errors encountered at runtime
  E-con : {tcn : TermCon}{L : n ⊢} → con tcn · L —→ error

  -- this is a runtime type error that ceases to be a type error after erasure
  -- E-runtime : {L : n ⊢} → L —→ error

data _—→T_ {n} where
  here  : ∀{m t t'}{ts : Tel m n} → t —→ t' → (t ∷ ts) —→T (t' ∷ ts)
  there : ∀{m t}{ts ts' : Tel m n}
    → Value t → ts —→T ts' → (t ∷ ts) —→T (t ∷ ts')
\end{code}


\begin{code}
data _—→⋆_ {n} : n ⊢ → n ⊢ → Set where
  refl  : {t : n ⊢} → t —→⋆ t
  trans—→⋆ : {t t' t'' : n ⊢} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
VERIFYSIG : ∀{n} → Maybe Bool → n ⊢
VERIFYSIG (just Bool.false) = plc_false
VERIFYSIG (just Bool.true)  = plc_true
VERIFYSIG nothing           = error

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
  decIf (i <? j) plc_true plc_false
BUILTIN lessThanEqualsInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i ≤? j) plc_true plc_false
BUILTIN greaterThanInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i Builtin.Constant.Type.>? j) plc_true plc_false
BUILTIN greaterThanEqualsInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i Builtin.Constant.Type.≥? j) plc_true plc_false
BUILTIN equalsInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i ≟ j) plc_true plc_false
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

data ProgTel {l n}(tel : Tel l n) : Set where
  done : VTel l n tel → ProgTel tel
  step : ∀{tel'} → tel —→T tel' → ProgTel tel
  error : Any Error tel → ProgTel tel

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
progress-·V (V-con tcn)              v               = step E-con
progress-·V (V-F v)                  (step q)        = step (ξ-·₂ v q)
progress-·V (V-F v)                  (error E-error) = step (E-·₂ v)
progress-·V (V-F (V-ƛ t))            (done v)        = step (β-ƛ v)
progress-·V (V-F (V-builtin b ts p)) (done v)        = step (sat-builtin v p)

progress-· : ∀{n}
  → {t : n ⊢} → Progress t
  → {u : n ⊢} → Progress u
  → Progress (t · u)
progress-· (done v)        q = progress-·V v q
progress-· (step p)        q = step (ξ-·₁ p)
progress-· (error E-error) q = step E-·₁

progress : (t : 0 ⊢) → Progress t

progressTel : ∀{l}(tel : Tel l 0) → ProgTel tel

progressTel []       = done tt
progressTel (t ∷ ts) with progress t
progressTel (t ∷ ts) | step p  = step (here p)
progressTel (t ∷ ts) | done v  with progressTel ts
progressTel (t ∷ ts) | done v | done vs = done (v , vs)
progressTel (t ∷ ts) | done v | step p  = step (there v p)
progressTel (t ∷ ts) | done v | error e = error (there v e)
progressTel (t ∷ ts) | error e = error (here e)

progress (` ())
progress (ƛ t)        = done (V-F (V-ƛ t))
progress (t · u)      = progress-· (progress t) (progress u)
progress (con tcn)    = done (V-con tcn)
progress (builtin b ≤‴-refl ts) with progressTel ts
progress (builtin b ≤‴-refl ts) | done vs = step (β-builtin ts vs)
progress (builtin b ≤‴-refl ts) | step p = step (ξ-builtin b p)
progress (builtin b ≤‴-refl ts) | error p = step (E-builtin b ts p)
progress (builtin b (≤‴-step p) ts) = done (V-F (V-builtin b ts p))
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
val-red (V-F (V-builtin b ts p)) (t' , ())
val-red (V-con tcn) (t' , ())

val-err : ∀{n}{t : n ⊢} → Value t → ¬ (Error t)
val-err (V-con tcn) ()
val-err (V-F (V-ƛ t)) ()
val-err (V-F (V-builtin b ts p)) ()

err-red : ∀{n}{t : n ⊢} → Error t → ¬ (Σ (n ⊢)  (t —→_))
err-red E-error (_ , ())

errT-redT : ∀{m n}{ts : Tel m n} → Any Error ts → ¬ (Σ (Tel m n)  (ts —→T_))
errT-redT (here p)    (.(_ ∷ _) , here q)    = err-red p (_ , q)
errT-redT (here p)    (.(_ ∷ _) , there v q) = val-err v p
errT-redT (there v p) (.(_ ∷ _) , here q)    = val-red v (_ , q)
errT-redT (there v p) (.(_ ∷ _) , there w q) = errT-redT p (_ , q)

valT-errT : ∀{m n}{ts : Tel m n} → VTel m n ts → ¬ (Any Error ts)
valT-errT {ts = t ∷ ts} (v , vs) (here p)    = val-err v p
valT-errT {ts = t ∷ ts} (v , vs) (there w p) = valT-errT vs p

valT-redT : ∀{m n}{ts : Tel m n} → VTel m n ts → ¬ (Σ (Tel m n)  (ts —→T_))
valT-redT {ts = []} _ (ts' , ())
valT-redT {ts = t ∷ ts} (v , vs) (._ , here p)     = val-red v (_ , p)
valT-redT {ts = t ∷ ts} (v , vs) (._ , there v' p) = valT-redT vs (_ , p)

valUniq : ∀{n}{t : n ⊢}(v v' : Value t) → v ≡ v'
valUniq (V-F (V-ƛ t)) (V-F (V-ƛ .t)) = refl
valUniq (V-F (V-builtin b ts p)) (V-F (V-builtin .b .ts .p)) = refl
valUniq (V-con tcn) (V-con .tcn) = refl

valTUniq : ∀{m n}{ts : Tel m n}(vs vs' : VTel m n ts) → vs ≡ vs'
valTUniq {ts = []}     _        _          = refl
valTUniq {ts = x ∷ ts} (v , vs) (v' , vs') =
  cong₂ _,_ (valUniq v v') (valTUniq vs vs')

detT : ∀{m n}{ts ts' ts'' : Tel m n}
  → (p : ts —→T ts')(q : ts —→T ts'') → ts' ≡ ts''

det : ∀{n}{t t' t'' : n ⊢}(p : t —→ t')(q : t —→ t'') → t' ≡ t''

det (ξ-·₁ p) (ξ-·₁ q) = cong (_· _) (det p q)
det (ξ-·₁ p) (ξ-·₂ v q) = ⊥-elim (val-red (V-F v) (_ , p))
det (ξ-·₁ p) (E-·₂ v) = ⊥-elim (val-red (V-F v) (_ , p))
det (ξ-·₂ v p) (ξ-·₁ q) = ⊥-elim (val-red (V-F v) (_ , q))
det (ξ-·₂ v p) (ξ-·₂ w q) = cong (_ ·_) (det p q)
det (ξ-·₂ v p) (β-ƛ w) = ⊥-elim (val-red w (_ , p))
det (ξ-·₂ v p) (sat-builtin w q) = ⊥-elim (val-red w (_ , p))
det (ξ-·₂ () p) E-con
det (β-ƛ v) (ξ-·₂ w q) = ⊥-elim (val-red v (_ , q))
det (β-ƛ v) (β-ƛ w) = refl
det (β-ƛ (V-F ())) (E-·₂ v)
det (E-·₂ v) (β-ƛ (V-F ()))
det (ξ-builtin b p) (ξ-builtin .b q) = cong (builtin b ≤‴-refl) (detT p q)
det (ξ-builtin b p) (β-builtin ts vs) = ⊥-elim (valT-redT vs (_ , p))
det (ξ-builtin b p) (E-builtin .b e q) = ⊥-elim (errT-redT q (_ , p))
det (β-builtin ts vs) (ξ-builtin b q) = ⊥-elim (valT-redT vs (_ , q))
det (β-builtin ts vs) (β-builtin .ts ws) = cong (BUILTIN _ ts) (valTUniq vs ws)
det (β-builtin ts vs) (E-builtin b v q) = ⊥-elim (valT-errT vs q)
det (sat-builtin v p) (ξ-·₂ w q) = ⊥-elim (val-red v (_ , q))
det (sat-builtin v p) (sat-builtin w .p) = refl
det (sat-builtin (V-F ()) p) (E-·₂ w)
det E-·₁ E-·₁ = refl
det (E-·₂ v) (ξ-·₁ q) = ⊥-elim (val-red (V-F v) (_ , q))
det (E-·₂ v) (sat-builtin (V-F ()) p)
det (E-·₂ v) (E-·₂ w) = refl
det (E-·₂ ()) E-con
det (E-builtin b ts p) (ξ-builtin .b q) = ⊥-elim (errT-redT p (_ , q))
det (E-builtin b ts p) (β-builtin ts vs) = ⊥-elim (valT-errT vs p)
det (E-builtin b ts p) (E-builtin .b w q) = refl
det E-con (ξ-·₂ () q)
det E-con (E-·₂ ())
det E-con E-con = refl

detT (here p) (here q) = cong (_∷ _) (det p q)
detT (here p) (there v q) = ⊥-elim (val-red v (_ , p))
detT (there v p) (here q) = ⊥-elim (val-red v (_ , q))
detT (there v p) (there w q) = cong (_ ∷_) (detT p q)

-- auxiliary functions

vTel:< : ∀{l n}
  → (ts : Tel l n)
  → VTel l n ts → (t : n ⊢)
  → Value t
  → VTel (suc l) n (ts :< t)
vTel:< []        vs        t v = v , tt
vTel:< (t' ∷ ts) (v' , vs) t v = v' , (vTel:< ts vs t v)


vTel++ : ∀{l l' n}
  → (ts : Tel l n)
  → VTel l n ts
  → (ts' : Tel l' n)
  → VTel l' n ts'
  → VTel (l Data.Nat.+ l') n (ts ++ ts')
vTel++ []       vs        ts' vs' = vs'
vTel++ (t ∷ ts) (v' , vs) ts' vs' = v' , vTel++ ts vs ts' vs'

anyErr++ : ∀{l l' n}{ts : Tel l n} → Any Error ts → (ts' : Tel l' n) → VTel l' n ts' → Any Error (ts' ++ ts)
anyErr++ p []         _           = p
anyErr++ p (t' ∷ ts') (v' , vs') = there v' (anyErr++ p ts' vs')

—→T++ : ∀{l l' n}{ts' ts'' : Tel l n} → ts' —→T ts'' → (ts : Tel l' n) → VTel l' n ts → (ts ++ ts') —→T (ts ++ ts'')
—→T++ p []       vs = p
—→T++ p (t ∷ ts) (v , vs) = there v (—→T++ p ts vs)
\end{code}
