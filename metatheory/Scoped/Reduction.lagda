\begin{code}
module Scoped.Reduction where
\end{code}

\begin{code}
open import Scoped
open import Scoped.RenamingSubstitution
open import Builtin
open import Builtin.Constant.Type

open import Utils

open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Product
open import Data.List hiding ([_]; drop; take)
open import Function
open import Data.Integer as I
open import Data.Nat as N hiding (_<?_;_>?_;_≥?_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_];trans)
import Agda.Builtin.Bool as B
\end{code}

\begin{code}
infix 2 _—→_
\end{code}

\begin{code}
data Value {n}{w : Weirdℕ n} : ScopedTm w → Set where
  V-ƛ : ∀ x (A : ScopedTy n)(t : ScopedTm (S w)) → Value (ƛ x A t)
  V-Λ : ∀ x K (t : ScopedTm (T w)) → Value (Λ x K t)
  V-con : (tcn : TermCon) → Value (con {n} tcn)
  V-wrap : (A B : ScopedTy n)(t : ScopedTm w) → Value (wrap A B t)
  V-builtin : (b : Builtin)
              (As : List (ScopedTy n))
              (ts : List (ScopedTm w))
              → Value (builtin b As ts)

Tel : ∀{n} → Weirdℕ n → Set
Tel w = List (ScopedTm w)

open import Data.Unit
VTel : ∀{n}(w : Weirdℕ n) → Tel w → Set
VTel w []       = ⊤
VTel w (t ∷ ts) = Value t × VTel w ts


-- a term that satisfies this predicate has an error term in it somewhere
-- or we encountered a rumtime type error
data Error {n}{w : Weirdℕ n} : ScopedTm w → Set where
   -- a genuine runtime error returned from a builtin
   E-error : (A : ScopedTy n) → Error (error A)

   -- error inside somewhere
   E-·₁ : {L M : ScopedTm w} → Error L → Error (L · M)
   E-·₂ : {L M : ScopedTm w} → Error M → Error (L · M)
   E-·⋆ : {L : ScopedTm w}{A : ScopedTy n} → Error L → Error (L ·⋆ A)
   E-unwrap : {L : ScopedTm w} → Error L → Error (unwrap L)

   -- runtime type errors
   -- these couldn't happen in the intrinsically typed version
   E-Λ·    : ∀{x K}{L : ScopedTm (T w)}{M : ScopedTm w} → Error (Λ x K L · M)
   E-ƛ·⋆   : ∀{x}{B : ScopedTy n}{L : ScopedTm (S w)}{A : ScopedTy n}
     → Error (ƛ x B L ·⋆ A)
   E-con·  : ∀{tcn}{M : ScopedTm w} → Error (con tcn · M)
   E-con·⋆ : ∀{tcn}{A : ScopedTy n} → Error (con tcn ·⋆ A)
   E-wrap· : {A B : ScopedTy n}{t M : ScopedTm w} → Error (wrap A B t · M)
   E-wrap·⋆ : {A' B A : ScopedTy n}{t : ScopedTm w}
     → Error (wrap A' B t ·⋆ A)
   E-ƛunwrap : ∀{x}{A : ScopedTy n}{t : ScopedTm (S w)}
     → Error (unwrap (ƛ x A t) )
   E-Λunwrap : ∀{x K}{t : ScopedTm (T w)} → Error (unwrap (Λ x K t))
   E-conunwrap : ∀{tcn} → Error (unwrap (con tcn))

   -- this stuff is required due to unsaturated builtins in term args only
   E-builtin·⋆ : {b : Builtin}
              {As : List (ScopedTy n)}
              {ts : List (ScopedTm w)}
              {A : ScopedTy n}
              → Error (builtin b As ts ·⋆ A)

   E-builtinunwrap : {b : Builtin}
              {As : List (ScopedTy n)}
              {ts : List (ScopedTm w)}
              → Error (unwrap (builtin b As ts))

   -- an error occured in one of reducing an argument
   E-builtin : {b : Builtin}
              {As : List (ScopedTy n)}
              {ts : List (ScopedTm w)}
              {t : ScopedTm w}
              → Error t
              → Error (builtin b As ts)

BUILTIN : ∀{n}{w : Weirdℕ n} → Builtin
  → List (ScopedTy n) → (ts : Tel w) → VTel w ts → ScopedTm w

BUILTIN addInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  con (integer (i I.+ i'))
BUILTIN addInteger _ _ _ = error (con integer)
BUILTIN subtractInteger  _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  con (integer (i I.- i'))
BUILTIN subtractInteger _ _ _ = error (con integer)
BUILTIN multiplyInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) =
  con (integer (i I.* i'))
BUILTIN multiplyInteger _ _ _ = error (con integer)
BUILTIN divideInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) with ∣ i' ∣ N.≟ zero
... | yes p = error (con integer)
... | no ¬p = con (integer (div i i'))
BUILTIN divideInteger _ _ _ = error (con integer)
BUILTIN quotientInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) with ∣ i' ∣ N.≟ zero
... | yes p = error (con integer)
... | no ¬p = con (integer (quot i i'))
BUILTIN quotientInteger _ _ _ = error (con integer)
BUILTIN remainderInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) with ∣ i' ∣ N.≟ zero
... | yes p = error (con integer)
... | no ¬p = con (integer (rem i i'))
BUILTIN remainderInteger _ _ _ = error (con integer)
BUILTIN modInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) with ∣ i' ∣ N.≟ zero
... | yes p = error (con integer)
... | no ¬p = con (integer (mod i i'))
BUILTIN modInteger _ _ _ = error (con integer)
-- Int -> Int -> Bool
BUILTIN lessThanInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i'), tt) with i <? i'
... | yes q = true
... | no ¬p = false
BUILTIN lessThanInteger _ _ _ = error boolean
BUILTIN lessThanEqualsInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) with i I.≤? i'
... | yes q = true
... | no ¬p = false
BUILTIN lessThanEqualsInteger _ _ _ = error boolean
BUILTIN greaterThanInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) with i >? i'
... | yes q = true
... | no ¬p = false
BUILTIN greaterThanInteger _ _ _ = error boolean
BUILTIN greaterThanEqualsInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) with i ≥? i'
... | yes q = true
... | no ¬p = false
BUILTIN greaterThanEqualsInteger _ _ _ = error boolean
BUILTIN equalsInteger _ (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer i') , tt) with i I.≟ i'
... | yes q = true
... | no ¬p = false
BUILTIN equalsInteger _ _ _ = error boolean
-- BS -> BS -> BS
BUILTIN concatenate _ (_ ∷ _ ∷ []) (V-con (bytestring b) , V-con (bytestring b') , tt) = con (bytestring (append b b'))
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
BUILTIN verifySignature _ (_ ∷ _ ∷ _ ∷ []) (V-con (bytestring k) , V-con (bytestring d) , V-con (bytestring c) , tt) with verifySig k d c
... | just B.false = false
... | just B.true = true
... | nothing = error boolean
BUILTIN verifySignature _ _ _ = error (con bytestring)
-- Int -> Int
BUILTIN equalsByteString _ (_ ∷ _ ∷ []) (V-con (bytestring b) , V-con (bytestring b') , tt) with equals b b'
... | B.true  = true
... | B.false = false
BUILTIN equalsByteString _ _ _ = error boolean

data _—→_ {n}{w : Weirdℕ n} : ScopedTm w → ScopedTm w → Set where
  ξ-·₁ : {L L' M : ScopedTm w} → L —→ L' → L · M —→ L' · M
  ξ-·₂ : {L M M' : ScopedTm w} → Value L → M —→ M' → L · M —→ L · M'
  ξ-·⋆ : {L L' : ScopedTm w}{A : ScopedTy n} → L —→ L' → L ·⋆ A —→ L' ·⋆ A
  β-ƛ : ∀{x}{A : ScopedTy n}{L : ScopedTm (S w)}{M : ScopedTm w}
      → (ƛ x A L) · M —→ (L [ M ])
  β-Λ : ∀{x K}{L : ScopedTm (T w)}{A : ScopedTy n}
      → (Λ x K L) ·⋆ A —→ (L [ A ]⋆)
  ξ-builtin : {b : Builtin}
              {As : List (ScopedTy n)}
              {tel : Tel w}
              {telA : Tel w}
              (vs : VTel w telA)
              {t t' : ScopedTm w}
            → t —→ t'
            → (telB : List (ScopedTm w))
--          a proof that tel = telA ++ t ++ telB
            → builtin b As tel
              —→
              builtin b As (telA ++ Data.List.[ t' ] ++ telB)
  β-builtin : {b : Builtin}
              {As : List (ScopedTy n)}
              {ts : Tel w}
              (vs : VTel w ts)
            → builtin b As ts —→ BUILTIN b As ts vs
  sat-builtin : {b : Builtin}
              {As : List (ScopedTy n)}
              {ts : List (ScopedTm w)}
              {t : ScopedTm w}
            → builtin b As ts · t —→ builtin b As (ts ++ Data.List.[ t ])

  ξ-unwrap : {t t' : ScopedTm w} → t —→ t' → unwrap t —→ unwrap t'
  β-wrap : {A B : ScopedTy n}{t : ScopedTm w} → unwrap (wrap A B t) —→ t
\end{code}

\begin{code}
data _—→⋆_ {n}{w : Weirdℕ n} : ScopedTm w → ScopedTm w → Set where
  refl  : {t : ScopedTm w} → t —→⋆ t
  trans : {t t' t'' : ScopedTm w} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
data Progress (t : ScopedTm Z) : Set where
  step : ∀{t'} → t —→ t' → Progress t
  done : Value t → Progress t
  error : Error t → Progress t
  
data TelProgress {n}{w : Weirdℕ n} : Tel w → Set where
  done : (tel : Tel w)(vtel : VTel w tel) → TelProgress tel
  step : (tel : Tel w)(telA : Tel w)(vtelA : VTel w telA)
   → {t t' : ScopedTm w} → t —→ t' → (telB : Tel w) → TelProgress tel
  error : (tel : Tel w)(telA : Tel w)(vtelA : VTel w telA){t : ScopedTm w}
    → Error t → (telB : Tel w) → TelProgress tel
\end{code}

\begin{code}
progress· : ∀{t : ScopedTm Z} → Progress t → (u : ScopedTm Z) → Progress (t · u)
progress· (step p)                   u = step (ξ-·₁ p)
progress· (done (V-ƛ x A t))         u = step β-ƛ
progress· (done (V-Λ x K t))         u = error E-Λ·
progress· (done (V-con tcn))         u = error E-con·
progress· (done (V-wrap A B t))      u = error E-wrap·
progress· (done (V-builtin b As ts)) u = step sat-builtin -- TODO
progress· (error e)                  u = error (E-·₁ e)

progress·⋆ : ∀{t : ScopedTm Z} → Progress t → (A : ScopedTy 0)
  → Progress (t ·⋆ A)
progress·⋆ (step p)                   A = step (ξ-·⋆ p)
progress·⋆ (done (V-ƛ x B t))         A = error E-ƛ·⋆
progress·⋆ (done (V-Λ x K t))         A = step β-Λ
progress·⋆ (done (V-con tcn))         A = error E-con·⋆
progress·⋆ (done (V-wrap pat arg t))  A = error E-wrap·⋆
progress·⋆ (done (V-builtin b As ts)) A = error E-builtin·⋆ -- TODO
progress·⋆ (error e)                  A = error (E-·⋆ e)

progress-unwrap : ∀{t : ScopedTm Z} → Progress t → Progress (unwrap t)
progress-unwrap (step p) = step (ξ-unwrap p)
progress-unwrap (done (V-ƛ x A t)) = error E-ƛunwrap
progress-unwrap (done (V-Λ x K t)) = error E-Λunwrap
progress-unwrap (done (V-con tcn)) = error E-conunwrap
progress-unwrap (done (V-wrap A B t)) = step β-wrap
progress-unwrap (done (V-builtin b As ts)) = error E-builtinunwrap -- TODO
progress-unwrap (error e) = error (E-unwrap e)

progress-builtin : ∀ bn → (As : List (ScopedTy 0)) (tel : Tel Z)
  → TelProgress tel → Progress (builtin bn As tel)
progress-builtin bn As tel p with arity bn N.≟ Data.List.length tel
progress-builtin bn As tel (done .tel vtel)               | yes p =
  step (β-builtin vtel)
progress-builtin bn As tel (step .tel telA vtelA x telB)  | yes p =
  step (ξ-builtin vtelA x telB)
progress-builtin bn As tel (error .tel telA vtelA x telB) | yes p =
  error (E-builtin x)
progress-builtin bn As tel p | no ¬p = done (V-builtin bn As tel)

progressTelCons : {t : ScopedTm Z} → Progress t → {tel : Tel Z}
  → TelProgress tel → TelProgress (t ∷ tel)
progressTelCons {t}(step p){tel}  q = step (t ∷ tel) [] tt p tel
progressTelCons (done v) (done tel vtel) = done (_ ∷ tel) (v , vtel)
progressTelCons (done v) (step tel telA vtelA p telB) =
  step (_ ∷ tel) (_ ∷ telA) (v , vtelA) p telB
progressTelCons (done v) (error tel telA vtelA p telB) =
  error (_ ∷ tel) (_ ∷ telA) (v , vtelA) p telB
progressTelCons {t}(error e){tel} q = error (t ∷ tel) [] tt e tel

progress : (t : ScopedTm Z) → Progress t

progressTel : (tel : Tel Z) → TelProgress {w = Z} tel
progressTel [] = done [] tt
progressTel (t ∷ tel) = progressTelCons (progress t) (progressTel tel)

progress (` ())
progress (Λ x K t)         = done (V-Λ x K t)
progress (t ·⋆ A)          = progress·⋆ (progress t) A
progress (ƛ x A t)         = done (V-ƛ x A t)
progress (t · u)           = progress· (progress t) u
progress (con c)           = done (V-con c)
progress (error A)         = error (E-error A)
progress (builtin b As ts) = progress-builtin b As ts (progressTel ts)
progress (wrap A B t)      = done (V-wrap A B t)
progress (unwrap t)        = progress-unwrap (progress t)
\end{code}

\begin{code}
open import Data.Nat
run : (t : ScopedTm Z) → ℕ
    → Σ (ScopedTm Z) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')
run t 0       = t , (refl , inl nothing) -- out of fuel
run t (suc n) with progress t
run t (suc n) | done vt = t , refl , inl (just vt)
run t (suc n) | error et = t , refl , inr et
run t (suc n) | step {t' = t'} p with run t' n
run t (suc n) | step {t' = t'} p | t'' , q , mvt'' = t'' , trans p q , mvt''
\end{code}
