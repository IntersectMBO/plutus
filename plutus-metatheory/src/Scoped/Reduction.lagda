\begin{code}
module Scoped.Reduction where
\end{code}

\begin{code}
open import Scoped
open import Scoped.RenamingSubstitution
open import Builtin
open import Builtin.Constant.Type

open import Utils

open import Agda.Builtin.String using (primStringFromList; primStringAppend)
import Data.List as List
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Vec using ([];_∷_;_++_)
open import Data.Product
open import Function
open import Data.Integer as I
open import Data.Nat as N hiding (_<?_;_>?_;_≥?_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_];trans)
open import Data.Bool using (Bool;true;false)
import Debug.Trace as Debug
\end{code}

\begin{code}
infix 2 _—→_
\end{code}

\begin{code}
data Value {n}{w : Weirdℕ n} : ScopedTm w → Set where
  V-ƛ : ∀ (A : ScopedTy n)(t : ScopedTm (S w)) → Value (ƛ A t)
  V-Λ : ∀ {K}(t : ScopedTm (T w)) → Value (Λ K t)
  V-con : (tcn : TermCon) → Value (con {n} tcn)
  V-wrap : (A B : ScopedTy n){t : ScopedTm w} → Value t → Value (wrap A B t)
  V-builtin : (b : Builtin)
            → (As : Tel⋆ n (arity⋆ b))
            → ∀{o}
            → (q : o <‴ arity b)
            → (ts : Tel w o)
            → Value (builtin b (inr (refl , ≤‴-step q)) As ts)
  V-builtin⋆ : (b : Builtin)
            → ∀{o}
            → (p : o <‴ arity⋆ b)
            → (As : Tel⋆ n o)
            → Value (builtin b (inl (≤‴-step p , refl)) As [])

voidVal : ∀ {n}(w : Weirdℕ n) → Value {w = w} (con unit)
voidVal w = V-con {w = w} unit

open import Data.Unit
VTel : ∀{n} m (w : Weirdℕ n) → Tel w m → Set
VTel 0       w []       = ⊤
VTel (suc m) w (t ∷ ts) = Value t × VTel m w ts

-- a term that satisfies this predicate has an error term in it somewhere
-- or we encountered a rumtime type error
data Error {n}{w : Weirdℕ n} : ScopedTm w → Set where
   -- a genuine runtime error returned from a builtin
   E-error : (A : ScopedTy n) → Error (error A)

data Any {n : ℕ}{w : Weirdℕ n}(P : ScopedTm w → Set) : ∀{m} → Tel w m → Set
  where
  here  : ∀{m t}{ts : Tel w m} → P t → Any P (t ∷ ts)
  there : ∀{m t}{ts : Tel w m} → Value t → Any P ts → Any P (t ∷ ts)

VERIFYSIG : ∀{n}{w : Weirdℕ n} → Maybe Bool → ScopedTm w
VERIFYSIG (just false) = con (bool false)
VERIFYSIG (just true)  = con (bool true)
VERIFYSIG nothing      = error (con bool)

-- this is currently in reverse order...
BUILTIN : ∀{n}{w : Weirdℕ n}
  → (b : Builtin)
  → Tel⋆ n (arity⋆ b) → (ts : Tel w (arity b)) → VTel (arity b) w ts → ScopedTm w
BUILTIN addInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  con (integer (i I.+ i'))
BUILTIN addInteger _ _ _ = error (con integer)
BUILTIN subtractInteger  _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  con (integer (i I.- i'))
BUILTIN subtractInteger _ _ _ = error (con integer)
BUILTIN multiplyInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  con (integer (i I.* i'))
BUILTIN multiplyInteger _ _ _ = error (con integer)
BUILTIN divideInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  decIf (∣ i' ∣ N.≟ 0) (error (con integer)) (con (integer (div i i')))
BUILTIN divideInteger _ _ _ = error (con integer)
BUILTIN quotientInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  decIf (∣ i' ∣ N.≟ 0) (error (con integer)) (con (integer (quot i i')))
BUILTIN quotientInteger _ _ _ = error (con integer)
BUILTIN remainderInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
    decIf (∣ i' ∣ N.≟ 0) (error (con integer)) (con (integer (rem i i')))
BUILTIN remainderInteger _ _ _ = error (con integer)
BUILTIN modInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
    decIf (∣ i' ∣ N.≟ 0) (error (con integer)) (con (integer (mod i i')))
BUILTIN modInteger _ _ _ = error (con integer)
-- Int -> Int -> Bool
BUILTIN lessThanInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  decIf (i <? i') (con (bool true)) (con (bool false))
BUILTIN lessThanInteger _ _ _ = error (con bool)
BUILTIN lessThanEqualsInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  decIf (i I.≤? i') (con (bool true)) (con (bool false))
BUILTIN lessThanEqualsInteger _ _ _ = error (con bool)
BUILTIN greaterThanInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  decIf (i >? i') (con (bool true)) (con (bool false))
BUILTIN greaterThanInteger _ _ _ = error (con bool)
BUILTIN greaterThanEqualsInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  decIf (i ≥? i') (con (bool true)) (con (bool false))
BUILTIN greaterThanEqualsInteger _ _ _ = error (con bool)
BUILTIN equalsInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  decIf (i I.≟ i') (con (bool true)) (con (bool false))
BUILTIN equalsInteger _ _ _ = error (con bool)
-- BS -> BS -> BS
BUILTIN concatenate _ (_ ∷ _ ∷ []) (V-con (bytestring b) , V-con (bytestring b') , tt) = con (bytestring (concat b b'))
BUILTIN concatenate _ _ _ = error (con bytestring)
-- Int -> BS -> BS
BUILTIN takeByteString _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (bytestring b) , tt) = con (bytestring (take i b))
BUILTIN takeByteString _ _ _ = error (con bytestring)
BUILTIN dropByteString _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (bytestring b) , tt) = con (bytestring (drop i b))
BUILTIN dropByteString _ _ _ = error (con bytestring)
-- BS -> BS
BUILTIN sha2-256 _ (_ ∷ []) (V-con (bytestring b) , tt) = con (bytestring (SHA2-256 b))
BUILTIN sha2-256 _ _ _ = error (con bytestring)
BUILTIN sha3-256 _ (_ ∷ []) (V-con (bytestring b) , tt) = con (bytestring (SHA3-256 b))
BUILTIN sha3-256 _ _ _ = error (con bytestring)
BUILTIN verifySignature _ (_ ∷ _ ∷ _ ∷ []) (V-con (bytestring k) , V-con (bytestring d) , V-con (bytestring c) , tt) = VERIFYSIG (verifySig k d c)
BUILTIN verifySignature _ _ _ = error (con bytestring)
-- Int -> Int
BUILTIN equalsByteString _ (_ ∷ _ ∷ []) (V-con (bytestring b) , V-con (bytestring b') , tt) =
  con (bool (equals b b'))
BUILTIN equalsByteString _ _ _ = error (con bool)
BUILTIN ifThenElse (A ∷ []) (.(con (bool true)) ∷ t ∷ u ∷ []) (V-con (bool true) , vt , vu , tt) = t
BUILTIN ifThenElse (A ∷ []) (.(con (bool false)) ∷ t ∷ u ∷ []) (V-con (bool false) , vt , vu , tt) = u
BUILTIN ifThenElse (A ∷ []) _ _ = error A
BUILTIN charToString _ (_ ∷ []) (V-con (char c) , tt) = con (string (primStringFromList List.[ c ]))
BUILTIN charToString _ _ _ = error (con string)
BUILTIN append _ (_ ∷ _ ∷ []) (V-con (string s) , V-con (string t) , tt) =
  con (string (primStringAppend s t))
BUILTIN append _ _ _ = error (con string)
BUILTIN trace _ (_ ∷ []) (V-con (string s) , tt) = con (Debug.trace s unit)
BUILTIN trace _ _ _ = error (con unit)

data _—→T_ {n}{w : Weirdℕ n} : ∀{m} → Tel w m → Tel w m → Set

data _—→_ {n}{w : Weirdℕ n} : ScopedTm w → ScopedTm w → Set where
  ξ-·₁ : {L L' M : ScopedTm w} → L —→ L' → L · M —→ L' · M
  ξ-·₂ : {L M M' : ScopedTm w} → Value L → M —→ M' → L · M —→ L · M'
  ξ-·⋆ : {L L' : ScopedTm w}{A : ScopedTy n} → L —→ L' → L ·⋆ A —→ L' ·⋆ A
  ξ-wrap : {A B : ScopedTy n}{L L' : ScopedTm w}
    → L —→ L' → wrap A B L —→ wrap A B L'
  β-ƛ : ∀{A : ScopedTy n}{L : ScopedTm (S w)}{M : ScopedTm w} → Value M
      → (ƛ A L) · M —→ (L [ M ])
  β-Λ : ∀{K}{L : ScopedTm (T w)}{A : ScopedTy n}
      → (Λ K L) ·⋆ A —→ (L [ A ]⋆)
  ξ-builtin : {b : Builtin}
            → {As : Tel⋆ n (arity⋆ b)}
              {ts ts' : Tel w (arity b)}
            → ts —→T ts'
            → builtin b (inr (refl , ≤‴-refl)) As ts
              —→ builtin b (inr (refl , ≤‴-refl)) As ts'
  β-builtin : {b : Builtin}
              {As : Tel⋆ n (arity⋆ b) }
              {ts : Tel w (arity b)}
              (vs : VTel (arity b) w ts)
            → builtin b (inr (refl , ≤‴-refl)) As ts —→ BUILTIN b As ts vs
  sat-builtin : {b : Builtin}
            → {As : Tel⋆ n (arity⋆ b)}
            → ∀{o'}{q : o' <‴ arity b}
            → {ts : Tel w o'}
            → {t : ScopedTm w}
            → builtin b (inr (refl , ≤‴-step q)) As ts · t
              —→ builtin b (inr (refl , q)) As (ts :< t)
  sat⋆-builtin : {b : Builtin}
            → ∀{o}{p : o <‴ arity⋆ b}
            → {As : Tel⋆ n o}
            → {A : ScopedTy n}
            → builtin b (inl (≤‴-step p , refl)) As [] ·⋆ A
              —→ builtin b (inl (p , refl)) (As :< A) []
  tick-builtin : {b : Builtin}
            → {As : Tel⋆ n (arity⋆ b)}
            → builtin b (inl (≤‴-refl , refl)) As []
              —→ builtin b (inr (refl , z≤‴n)) As []
  ξ-unwrap : {t t' : ScopedTm w} → t —→ t' → unwrap t —→ unwrap t'
  β-wrap : {A B : ScopedTy n}{t : ScopedTm w}
    → Value t → unwrap (wrap A B t) —→ t

  E-·₁ : {A : ScopedTy n}{M : ScopedTm w} → error A · M —→ error missing
  E-·₂ : {A : ScopedTy n}{L : ScopedTm w} → Value L → L · error A —→ error missing

  -- error inside somewhere

  E-·⋆ : {A B : ScopedTy n} → error A ·⋆ B —→ error missing
--  E-Λ : ∀{K}{A : ScopedTy (N.suc n)} → Λ K (error A) —→ error missing

  E-unwrap : {A : ScopedTy n}
    → unwrap (error A) —→ error missing
  E-wrap : {A B C : ScopedTy n}
    → wrap A B (error C) —→ error missing

  -- runtime type errors
  -- these couldn't happen in the intrinsically typed version
  E-Λ·    : ∀{K}{L : ScopedTm (T w)}{M : ScopedTm w}
    → Λ K L · M —→ error missing
  E-ƛ·⋆   : ∀{B : ScopedTy n}{L : ScopedTm (S w)}{A : ScopedTy n}
    → ƛ B L ·⋆ A —→ error missing
  E-con·  : ∀{tcn}{M : ScopedTm w} → con tcn · M —→ error missing
  E-con·⋆ : ∀{tcn}{A : ScopedTy n} → con tcn ·⋆ A —→ error missing
  E-wrap· : {A B : ScopedTy n}{t M : ScopedTm w}
    → wrap A B t · M —→ error missing
  E-wrap·⋆ : {A' B A : ScopedTy n}{t : ScopedTm w}
    → wrap A' B t ·⋆ A —→ error missing
  E-ƛunwrap : {A : ScopedTy n}{t : ScopedTm (S w)}
    → unwrap (ƛ A t) —→ error missing
  E-Λunwrap : ∀{K}{t : ScopedTm (T w)} → unwrap (Λ K t) —→ error missing
  E-conunwrap : ∀{tcn} → unwrap (con tcn) —→ error missing
  E-builtin·⋆ : {b : Builtin}
              → {As : Tel⋆ n (arity⋆ b)}
              → ∀{o}{p : o <‴ arity b}
              → {ts : Tel w o}
              → {A : ScopedTy n}
              → builtin b (inr (refl , ≤‴-step p)) As ts ·⋆ A —→ error missing
  E-builtin⋆· : (b : Builtin)
              → ∀{o}(p : o <‴ arity⋆ b)
              → (As : Tel⋆ n o)
              → (t : ScopedTm w)
              → builtin b (inl (≤‴-step p , refl)) As [] · t —→ error missing
  E-builtinunwrap : {b : Builtin}
                  → {As : Tel⋆ n (arity⋆ b)}
                  → ∀{o'}{q : o' ≤‴ arity b}
                  → {ts : Tel w o'}
                  → unwrap (builtin b (inr (refl , q)) As ts) —→ error missing
  E-builtin⋆unwrap : {b : Builtin}
                   → ∀{o}{p : o <‴ arity⋆ b}
                   → {As : Tel⋆ n o}
                   → unwrap (builtin b (inl (≤‴-step p , refl)) As [])
                     —→ error missing
{-
E-builtin⋆ : (b : Builtin)
             → (As : Vec (ScopedTy n) (arity b))
             → ∀{o'}(q : o' ≤‴ arity b)
             → (ts : Vec (ScopedTm w) o')

             → builtin b As ts {!!} —→ error missing
-}
  E-builtin : (b : Builtin)
            → (As : Tel⋆ n (arity⋆ b))
            → (ts : Tel w (arity b))
            → Any Error ts
            → builtin b (inr (refl , ≤‴-refl)) As ts —→ error missing

data _—→T_ {n}{w} where
  here  : ∀{m t t'}{ts : Tel w m} → t —→ t' → (t ∷ ts) —→T (t' ∷ ts)
  there : ∀{m t}{ts ts' : Tel w m}
    → Value t → ts —→T ts' → (t ∷ ts) —→T (t ∷ ts')
\end{code}

\begin{code}
data _—→⋆_ {n}{w : Weirdℕ n} : ScopedTm w → ScopedTm w → Set where
  refl  : {t : ScopedTm w} → t —→⋆ t
  trans : {t t' t'' : ScopedTm w} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
data Progress {n}{i : Weirdℕ n}(t : ScopedTm i) : Set where
  step : ∀{t'} → t —→ t' → Progress t
  done : Value t → Progress t
  error : Error t → Progress t

data TelProgress {m}{n}{w : Weirdℕ n} : Tel w m → Set where
  done : {tel : Tel w m}(vtel : VTel m w tel) → TelProgress tel
  step : {ts ts' : Tel w m} → ts —→T ts' → TelProgress ts
  error : {ts : Tel w m} → Any Error ts → TelProgress ts

\end{code}

\begin{code}
progress·V : ∀{n}{i : Weirdℕ n}
  → {t : ScopedTm i} → Value t
  → {u : ScopedTm i} → Progress u
  → Progress (t · u)
progress·V v                     (step q)            = step (ξ-·₂ v q)
progress·V v                     (error (E-error A)) = step (E-·₂ v)
progress·V (V-ƛ A t)             (done v)            = step (β-ƛ v)
progress·V (V-Λ p)               (done v)            = step E-Λ·
progress·V (V-con tcn)           (done v)            = step E-con·
progress·V (V-wrap A B t)        (done v)            = step E-wrap·
progress·V (V-builtin⋆ b As q)   (done v)            =
  step (E-builtin⋆· b As q _)
progress·V (V-builtin b As p ts) (done v)            = step sat-builtin

progress· : ∀{n}{i : Weirdℕ n}
  → {t : ScopedTm i} → Progress t
  → {u : ScopedTm i} → Progress u
  → Progress (t · u)
progress· (done v)            q = progress·V v q
progress· (step p)            q = step (ξ-·₁ p)
progress· (error (E-error A)) q = step E-·₁

progress·⋆ : ∀{n}{i : Weirdℕ n}{t : ScopedTm i}
  → Progress t → (A : ScopedTy n) → Progress (t ·⋆ A)
progress·⋆ (step p)                     A = step (ξ-·⋆ p)
progress·⋆ (done (V-ƛ B t))             A = step E-ƛ·⋆
progress·⋆ (done (V-Λ p))               A = step β-Λ
progress·⋆ (done (V-con tcn))           A = step E-con·⋆
progress·⋆ (done (V-wrap pat arg t))    A = step E-wrap·⋆
progress·⋆ (done (V-builtin⋆ b As p))   A = step sat⋆-builtin
progress·⋆ (done (V-builtin b As p ts)) A = step E-builtin·⋆

progress·⋆ (error (E-error A))          B = step E-·⋆

progress-unwrap : ∀{n}{i : Weirdℕ n}{t : ScopedTm i}
  → Progress t → Progress (unwrap t)
progress-unwrap (step p)                     = step (ξ-unwrap p)
progress-unwrap (done (V-ƛ A t))             = step E-ƛunwrap
progress-unwrap (done (V-Λ p))               = step E-Λunwrap
progress-unwrap (done (V-con tcn))           = step E-conunwrap
progress-unwrap (done (V-wrap A B v))        = step (β-wrap v)
progress-unwrap (done (V-builtin b As p ts)) = step E-builtinunwrap
progress-unwrap (done (V-builtin⋆ b As p))   = step E-builtin⋆unwrap
progress-unwrap (error (E-error A))          = step E-unwrap

progress-builtin : ∀ {n}{i : Weirdℕ n} bn
  → (As : Tel⋆ n (arity⋆ bn)) (tel : Tel i (arity bn))
  → TelProgress tel → Progress (builtin bn (inr (refl , ≤‴-refl)) As tel)
progress-builtin bn As ts (done vs) = step (β-builtin vs)
progress-builtin bn As ts (step p)  = step (ξ-builtin p)
progress-builtin bn As ts (error p) = step (E-builtin bn As ts p)

progressTelCons : ∀{m n}{i : Weirdℕ n}{t : ScopedTm i}
  → {ts : Tel i m} → Progress t → TelProgress ts → TelProgress (t ∷ ts)
progressTelCons (step p)  q         = step (here p)
progressTelCons (done v)  (done vs) = done (v , vs)
progressTelCons (done v)  (step q)  = step (there v q)
progressTelCons (done v)  (error p) = error (there v p)
progressTelCons (error p) q         = error (here p)

progress : (t : ScopedTm Z) → Progress t
progressTel : ∀{m}(tel : Tel Z m) → TelProgress tel
progressTel []       = done tt
progressTel (t ∷ ts) = progressTelCons (progress t) (progressTel ts)

progress (Λ K t)           = done (V-Λ t)
progress (t ·⋆ A)          = progress·⋆ (progress t) A
progress (ƛ A t)           = done (V-ƛ A t)
progress (t · u)           = progress· (progress t) (progress u)
progress (con c)           = done (V-con c)
progress (error A)         = error (E-error A)
-- type telescope is full
progress (builtin b (inl (≤‴-refl , refl)) As []) = step tick-builtin
-- type telescope is not full yet
progress (builtin b (inl (≤‴-step q , refl)) As []) = done (V-builtin⋆ b q As)
-- term telescope is full
progress (builtin b (inr (refl , ≤‴-refl)) As ts) =
  progress-builtin b As ts (progressTel ts)
-- term telescope is not full yet
progress (builtin b (inr (refl , ≤‴-step snd)) As ts) = done (V-builtin b As snd ts)

progress (wrap A B t) with progress t
progress (wrap A B t)          | step  q           = step (ξ-wrap q)
progress (wrap A B t)          | done  q           = done (V-wrap A B q)
progress (wrap A B .(error C)) | error (E-error C) = step E-wrap
progress (unwrap t)        = progress-unwrap (progress t)
\end{code}

\begin{code}
open import Data.Nat

Steps : ScopedTm Z → Set
Steps t = Σ (ScopedTm Z) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')

run—→ : {t t' : ScopedTm Z} → t —→ t' → Steps t' → Steps t
run—→ p (t' , ps , q) = _ , ((trans p ps) , q)

run : (t : ScopedTm Z) → ℕ → Steps t
runProg : ℕ → {t : ScopedTm Z} → Progress t → Steps t

run t 0       = t , (refl , inl nothing) -- out of fuel
run t (suc n) = runProg n (progress t)

runProg n (step {t' = t'} p)  = run—→ p (run t' n)
runProg n (done V)  = _ , refl , inl (just V)
runProg n (error e) = _ , refl , inr e
\end{code}
