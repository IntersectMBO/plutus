\begin{code}
module Untyped.Reduction where
\end{code}

\begin{code}
open import Untyped
open import Untyped.RenamingSubstitution
open import Builtin
open import Builtin.Constant.Type hiding (length)

open import Data.Bool using (Bool;true;false)
open import Data.Nat using (ℕ;suc;zero;_<‴_;_≤‴_;≤‴-refl;≤‴-step)
open import Data.Integer using (_+_;_-_;_*_;∣_∣;_<?_;_≤?_;_≟_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Vec using (Vec;[];_∷_;_++_)
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
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


VTel : ∀ l n → Tel l n → Set
VTel 0       n []       = ⊤
VTel (suc l) n (t ∷ ts) = Value {n} t × VTel l n ts

BUILTIN : ∀{n}
    → (b : Builtin)
    → (tel : Tel (arity b) n)
    → VTel (arity b) n tel
      --------------
    → n ⊢

data _—→_ {n} : n ⊢ → n ⊢ → Set where
  ξ-·₁ : {L L' M : n ⊢} → L —→ L' → L · M —→ L' · M
  ξ-·₂ : {L M M' : n ⊢} → FValue L → M —→ M' → L · M —→ L · M'

  β-ƛ : ∀{L : suc n ⊢}{V : n ⊢} → Value V → ƛ L · V —→ L [ V ]

  ξ-builtin : (b : Builtin)
            → ∀ {l' l''}
              (ts : Tel (arity b) n)
              {ts' : Tel l' n}
              (vs : VTel l' n ts')
              {t t' : n ⊢}
            → t —→ t'
            → (ts'' : Tel l'' n)
           → (p : l' Data.Nat.+ suc l'' ≡ arity b)
            → ts ≡ subst (Vec (n ⊢)) p (ts' ++ Data.Vec.[ t ] ++ ts'')
            → (r : l' Data.Nat.+ suc l'' ≤‴ arity b)
            → builtin b ≤‴-refl ts
              —→
              builtin b r (ts' ++ Data.Vec.[ t' ] ++ ts'')

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
              -- backwards vectors would be better for this...
              → builtin b (≤‴-step p) ts · t —→ builtin b p (t ∷ ts)


  E-·₁ : {M : n ⊢} → error · M —→ error
  E-·₂ : {L : n ⊢} → FValue L → L · error —→ error

  E-builtin : (b : Builtin)
            →  ∀{l' l''}
              (ts : Tel (arity b) n)
              {ts' : Tel l' n}
              (vs : VTel l' n ts')
              {t : n ⊢}
            → Error t
            → (ts'' : Tel l'' n)
            → (p : l' Data.Nat.+ suc l'' ≡ arity b)
            → ts ≡ subst (Vec (n ⊢)) p (ts' ++ Data.Vec.[ t ] ++ ts'')
            → builtin b ≤‴-refl ts —→ error

  -- these correspond to type errors encountered at runtime
  E-con : {tcn : TermCon}{L : n ⊢} → con tcn · L —→ error

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
  con (bytestring (append b b'))
BUILTIN takeByteString (_ ∷ _ ∷ []) (V-con (integer i) , V-con (bytestring b) , tt) =
  con (bytestring (take i b))
BUILTIN dropByteString (_ ∷ _ ∷ []) (V-con (integer i) , V-con (bytestring b) , tt) =
  con (bytestring (drop i b))
BUILTIN sha2-256 (_ ∷ []) (V-con (bytestring b) , tt) = con (bytestring (SHA2-256 b))
BUILTIN sha3-256 (_ ∷ []) (V-con (bytestring b) , tt) = con (bytestring (SHA3-256 b))
BUILTIN verifySignature (_ ∷ _ ∷ _ ∷ []) (V-con (bytestring k) , V-con (bytestring d) , V-con (bytestring c) , tt) = VERIFYSIG (verifySig k d c)
BUILTIN equalsByteString (_ ∷ _ ∷ []) (V-con (bytestring b) , V-con (bytestring b') , tt) =
  con (bool (equals b b'))
BUILTIN ifThenElse (_ ∷ t ∷ _ ∷ []) (V-con (bool true)  , vt , _ , tt) = t
BUILTIN ifThenElse (_ ∷ _ ∷ u ∷ []) (V-con (bool false) , _ , vu , tt) = u
BUILTIN _ _ _ = error

data ProgTel {l n}(tel : Tel l n) : Set where
  done : VTel l n tel → ProgTel tel
  step : ∀{l' l''} → (tel' : Tel l' n) → VTel l' n tel' → {t t' : n ⊢} → t —→ t'
    → (tel'' : Tel l'' n)
    → (p : l' Data.Nat.+ suc l'' ≡ l)
    → tel ≡ subst (Vec (n ⊢)) p (tel' ++ Data.Vec.[ t ] ++ tel'') 
    → ProgTel tel
  error : ∀{l' l''}(tel' : Tel l' n) → VTel l' n tel' → (tel'' : Tel l'' n)
    → (p : l' Data.Nat.+ suc l'' ≡ l)
    → tel ≡ subst (Vec (n ⊢)) p (tel' ++ Data.Vec.[ error ] ++ tel'')
    → ProgTel tel

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

progressTel []       = done _
progressTel (t ∷ ts) with progress t
progressTel (.error ∷ ts) | error E-error = error [] _ ts refl refl
progressTel (t ∷ ts) | step p = step [] _ p ts refl refl
progressTel (t ∷ ts) | done vt with progressTel ts
progressTel (t ∷ ts) | done vt | done vs   = done (vt , vs)
progressTel (t ∷ ts) | done vt | step  ts' vs p ts'' q r =
  step (t ∷ ts') (vt , vs) p ts'' (cong suc q)
    (trans (cong (t ∷_) r) (subst∷ t _ q (cong suc q)))
progressTel (t ∷ ts) | done vt | error ts' vs ts'' p q =
  error (t ∷ ts') (vt , vs) ts'' (cong suc p)
    (trans (cong (t ∷_) q) (subst∷ t _ p (cong suc p)))

progress (` ())
progress (ƛ t)        = done (V-F (V-ƛ t))
progress (t · u)      = progress-· (progress t) (progress u)
progress (con tcn)    = done (V-con tcn)
progress (builtin b ≤‴-refl ts) with progressTel ts
progress (builtin b ≤‴-refl ts) | done vs = step (β-builtin ts vs)
progress (builtin b ≤‴-refl ts) | step ts' vts' p ts'' q r =
  step (ξ-builtin b ts vts' p ts'' q r (subst (_≤‴ arity b) (sym q) ≤‴-refl))
progress (builtin b ≤‴-refl ts) | error ts' vts' ts'' p q =
  step (E-builtin b ts vts' E-error ts'' p q)
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
det (ξ-builtin b ts vs p ts'' p₁ x r) (ξ-builtin .b .ts vs₁ q ts''' p₂ x₁ r₁) = {!!}
det (ξ-builtin b ts vs p ts'' p₁ x r) (β-builtin .ts vs₁) = {!!}
det (ξ-builtin b ts vs p ts'' p₁ x r) (E-builtin .b .ts vs₁ x₁ ts''' p₂ x₂) = {!!}
det (β-builtin ts vs) (ξ-builtin b .ts vs₁ q ts'' p x r) = {!!}
det (β-builtin ts vs) (β-builtin .ts vs₁) = {!!}
det (β-builtin ts vs) (E-builtin b .ts vs₁ x ts'' p x₁) = {!!}
det (sat-builtin v p) (ξ-·₂ w q) = ⊥-elim (val-red v (_ , q)) 
det (sat-builtin v p) (sat-builtin w .p) = refl
det (sat-builtin (V-F ()) p) (E-·₂ w)
det E-·₁ E-·₁ = refl
det (E-·₂ v) (ξ-·₁ q) = ⊥-elim (val-red (V-F v) (_ , q)) 
det (E-·₂ v) (sat-builtin (V-F ()) p)
det (E-·₂ v) (E-·₂ w) = refl
det (E-·₂ ()) E-con
det (E-builtin b ts vs x ts'' p x₁) (ξ-builtin .b .ts vs₁ q ts''' p₁ x₂ r) = {!!}
det (E-builtin b ts vs x ts'' p x₁) (β-builtin .ts vs₁) = {!!}
det (E-builtin b ts vs x ts'' p x₁) (E-builtin .b .ts vs₁ x₂ ts''' p₁ x₃) = {!!}
det E-con (ξ-·₂ () q)
det E-con (E-·₂ ())
det E-con E-con = refl
\end{code}
