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
data Value {n} : ScopedTm n → Set where
  V-ƛ : ∀ x (A : ScopedTy ∥ n ∥)(t : ScopedTm (S n)) → Value (ƛ x A t)
  V-Λ : ∀ x K (t : ScopedTm (T n)) → Value (Λ x K t)
  V-con : (tcn : TermCon) → Value (con {n} tcn)
  V-wrap : (A B : ScopedTy ∥ n ∥)(t : ScopedTm n) → Value (wrap A B t)
  V-builtin : (b : Builtin)
              (As : List (ScopedTy ∥ n ∥))
              (ts : List (ScopedTm n))
              → Value (builtin b As ts)

-- a term that satisfies this predicate has an error term in it somewhere
-- or we encountered a rumtime type error
data Error {n} : ScopedTm n → Set where
   -- a genuine runtime error returned from a builtin
   E-error : (A : ScopedTy ∥ n ∥) → Error (error A)

   -- error inside somewhere
   E-·₁ : {L M : ScopedTm n} → Error L → Error (L · M)
   E-·₂ : {L M : ScopedTm n} → Error M → Error (L · M)
   E-·⋆ : {L : ScopedTm n}{A : ScopedTy ∥ n ∥} → Error L → Error (L ·⋆ A)
   E-unwrap : {L : ScopedTm n} → Error L → Error (unwrap L)

   -- runtime type errors
   -- these couldn't happen in the intrinsically typed version
   E-Λ·    : ∀{x K}{L : ScopedTm (T n)}{M : ScopedTm n} → Error (Λ x K L · M)
   E-ƛ·⋆   : ∀{x}{B : ScopedTy ∥ n ∥}{L : ScopedTm (S n)}{A : ScopedTy ∥ n ∥}
     → Error (ƛ x B L ·⋆ A)
   E-con·  : ∀{tcn}{M : ScopedTm n} → Error (con tcn · M)
   E-con·⋆ : ∀{tcn}{A : ScopedTy ∥ n ∥} → Error (con tcn ·⋆ A)
   E-wrap· : {A B : ScopedTy ∥ n ∥}{t M : ScopedTm n} → Error (wrap A B t · M)
   E-wrap·⋆ : {A' B A : ScopedTy ∥ n ∥}{t : ScopedTm n}
     → Error (wrap A' B t ·⋆ A)
   E-ƛunwrap : ∀{x}{A : ScopedTy ∥ n ∥}{t : ScopedTm (S n)}
     → Error (unwrap (ƛ x A t) )
   E-Λunwrap : ∀{x K}{t : ScopedTm (T n)} → Error (unwrap (Λ x K t))
   E-conunwrap : ∀{tcn} → Error (unwrap (con tcn))

   -- this stuff is required due to unsaturated builtins in term args only
   E-builtin·⋆ : {b : Builtin}
              {As : List (ScopedTy ∥ n ∥)}
              {ts : List (ScopedTm n)}
              {A : ScopedTy ∥ n ∥}
              → Error (builtin b As ts ·⋆ A)

   E-builtinunwrap : {b : Builtin}
              {As : List (ScopedTy ∥ n ∥)}
              {ts : List (ScopedTm n)}
              → Error (unwrap (builtin b As ts))

   -- an error occured in one of reducing an argument
   E-builtin : {b : Builtin}
              {As : List (ScopedTy ∥ n ∥)}
              {ts : List (ScopedTm n)}
              {t : ScopedTm n}
              → Error t
              → Error (builtin b As ts)

-- doing minimal size checking


BUILTIN : ∀{n} → Builtin
  → List (ScopedTy ∥ n ∥) → List (Σ (ScopedTm n) (Value {n})) → ScopedTm n
-- Int -> Int -> Int
BUILTIN addInteger       _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) = con (integer (i I.+ i'))
BUILTIN addInteger _ _ = error (con integer)
BUILTIN subtractInteger  _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) = con (integer (i I.- i'))
BUILTIN subtractInteger _ _ = error (con integer)
BUILTIN multiplyInteger  _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) = con (integer (i I.* i'))
BUILTIN multiplyInteger _ _ = error (con integer)
BUILTIN divideInteger    _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) with ∣ i' ∣ N.≟ zero
... | yes p = error (con integer)
... | no ¬p = con (integer (div i i'))
BUILTIN divideInteger _ _ = error (con integer)
BUILTIN quotientInteger  _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) with ∣ i' ∣ N.≟ zero
... | yes p = error (con integer)
... | no ¬p = con (integer (quot i i'))
BUILTIN quotientInteger _ _ = error (con integer)
BUILTIN remainderInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) with ∣ i' ∣ N.≟ zero
... | yes p = error (con integer)
... | no ¬p = con (integer (rem i i'))
BUILTIN remainderInteger _ _ = error (con integer)
BUILTIN modInteger       _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) with ∣ i' ∣ N.≟ zero
... | yes p = error (con integer)
... | no ¬p = con (integer (mod i i'))
BUILTIN modInteger _ _ = error (con integer)
-- Int -> Int -> Bool
BUILTIN lessThanInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) with i <? i'
BUILTIN lessThanInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) | yes q = true
BUILTIN lessThanInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) | no ¬p = false
BUILTIN lessThanInteger _ _ = error boolean
BUILTIN lessThanEqualsInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) with i I.≤? i'
BUILTIN lessThanEqualsInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) | yes q = true
BUILTIN lessThanEqualsInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) | no ¬p = false
BUILTIN lessThanEqualsInteger _ _ = error boolean
BUILTIN greaterThanInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) with i >? i'
BUILTIN greaterThanInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) | yes q = true
BUILTIN greaterThanInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) | no ¬p = false
BUILTIN greaterThanInteger _ _ = error boolean
BUILTIN greaterThanEqualsInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) with i ≥? i'
BUILTIN greaterThanEqualsInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) | yes q = true
BUILTIN greaterThanEqualsInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) | no ¬p = false
BUILTIN greaterThanEqualsInteger _ _ = error boolean
BUILTIN equalsInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) with i I.≟ i'
BUILTIN equalsInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) | yes q = true
BUILTIN equalsInteger _ ((_ , V-con (integer i)) ∷ (_ , V-con (integer i')) ∷ []) | no ¬p = false
BUILTIN equalsInteger _ _ = error boolean
-- BS -> BS -> BS
BUILTIN concatenate _ ((_ , V-con (bytestring b)) ∷ (_ , V-con (bytestring b')) ∷ []) = con (bytestring (append b b'))
BUILTIN concatenate _ _ = error (con bytestring)
-- Int -> BS -> BS
BUILTIN takeByteString _ ((_ , V-con (integer i)) ∷ (_ , V-con (bytestring b)) ∷ []) = con (bytestring (take i b))
BUILTIN takeByteString _ _ = error (con bytestring)
BUILTIN dropByteString _ ((_ , V-con (integer i)) ∷ (_ , V-con (bytestring b)) ∷ []) = con (bytestring (drop i b))
BUILTIN dropByteString _ _ = error (con bytestring)
-- BS -> BS
BUILTIN sha2-256 _ ((_ , V-con (bytestring b)) ∷ []) = con (bytestring (SHA2-256 b))
BUILTIN sha2-256 _ _ = error (con bytestring)
BUILTIN sha3-256 _ ((_ , V-con (bytestring b)) ∷ []) = con (bytestring (SHA3-256 b))
BUILTIN sha3-256 _ _ = error (con bytestring)
BUILTIN verifySignature _ ((_ , V-con (bytestring k)) ∷ (_ , V-con (bytestring d)) ∷ (_ , V-con (bytestring c)) ∷ []) with verifySig k d c
... | just B.false = false
... | just B.true = true
... | nothing = error boolean
BUILTIN verifySignature _ _ = error (con bytestring)
-- Int -> Int
BUILTIN equalsByteString _ ((_ , V-con (bytestring b)) ∷ (_ , V-con (bytestring b')) ∷ []) with equals b b'
... | B.true  = true
... | B.false = false
BUILTIN equalsByteString _ _ = error boolean




data _—→_ {n} : ScopedTm n → ScopedTm n → Set where
  ξ-·₁ : {L L' M : ScopedTm n} → L —→ L' → L · M —→ L' · M
  ξ-·₂ : {L M M' : ScopedTm n} → Value L → M —→ M' → L · M —→ L · M'
  ξ-·⋆ : {L L' : ScopedTm n}{A : ScopedTy ∥ n ∥} → L —→ L' → L ·⋆ A —→ L' ·⋆ A
  β-ƛ : ∀{x}{A : ScopedTy ∥ n ∥}{L : ScopedTm (S n)}{M : ScopedTm n}
      → (ƛ x A L) · M —→ (L [ M ])
  β-Λ : ∀{x K}{L : ScopedTm (T n)}{A : ScopedTy ∥ n ∥}
      → (Λ x K L) ·⋆ A —→ (L [ A ]⋆)
  ξ-builtin : {b : Builtin}
              {As : List (ScopedTy ∥ n ∥)}
              {ts : List (ScopedTm n)}
              (vs : List (Σ (ScopedTm n) (Value {n})))
              {t t' : ScopedTm n}
            → t —→ t'
            → (ts' : List (ScopedTm n))
            → builtin b As ts —→
              builtin b As (Data.List.map proj₁ vs ++ Data.List.[ t' ] ++ ts')
  β-builtin : {b : Builtin}
              {As : List (ScopedTy ∥ n ∥)}
              {ts : List (ScopedTm n)}
              (vs : List (Σ (ScopedTm n) (Value {n})))
            → builtin b As ts —→ BUILTIN b As vs
  sat-builtin : {b : Builtin}
              {As : List (ScopedTy ∥ n ∥)}
              {ts : List (ScopedTm n)}
              {t : ScopedTm n}
            → builtin b As ts · t —→ builtin b As (ts ++ Data.List.[ t ])

  ξ-unwrap : {t t' : ScopedTm n} → t —→ t' → unwrap t —→ unwrap t'
  β-wrap : {A B : ScopedTy ∥ n ∥}{t : ScopedTm n} → unwrap (wrap A B t) —→ t
\end{code}

\begin{code}
data _—→⋆_ {n} : ScopedTm n → ScopedTm n → Set where
  refl  : {t : ScopedTm n} → t —→⋆ t
  trans : {t t' t'' : ScopedTm n} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
data ProgList {n} : Set where
  done : List (Σ (ScopedTm n) (Value {n})) → ProgList
  step : (vs : List (Σ (ScopedTm n) (Value {n}))){t t' : ScopedTm n} → t —→ t' → List (ScopedTm n)
       → ProgList
  error : (vs : List (Σ (ScopedTm n) (Value {n}))){t : ScopedTm n} → Error t → List (ScopedTm n)
        → ProgList
\end{code}



\begin{code}
progress : (t : ScopedTm Z)
         → (Value {Z} t ⊎ Error t) ⊎ Σ (ScopedTm Z) λ t' → t —→ t'
progressList : List (ScopedTm Z) → ProgList {Z}
progressList []       = done []
progressList (t ∷ ts) with progress t
progressList (t ∷ ts) | inl (inl vt) with progressList ts
progressList (t ∷ ts) | inl (inl vt) | done  vs       = done ((t , vt) ∷ vs)
progressList (t ∷ ts) | inl (inl vt) | step  vs p ts' =
  step ((t , vt) ∷ vs) p ts'
progressList (t ∷ ts) | inl (inl vt) | error vs e ts' =
  error ((t , vt) ∷ vs) e ts'
progressList (t ∷ ts) | inl (inr e) = error [] e ts
progressList (t ∷ ts) | inr (t' , p) = step [] p ts

progress (` ())
progress (Λ x K t) = inl (inl (V-Λ x K t))
progress (t ·⋆ A) with progress t
progress (.(ƛ x B t) ·⋆ A) | inl (inl (V-ƛ x B t)) = inl (inr E-ƛ·⋆)
progress (.(Λ x K t) ·⋆ A) | inl (inl (V-Λ x K t)) = inr (t [ A ]⋆ , β-Λ)
progress (.(con tcn) ·⋆ A) | inl (inl (V-con tcn)) = inl (inr E-con·⋆)
progress (.(wrap A' B t) ·⋆ A) | inl (inl (V-wrap A' B t)) = inl (inr E-wrap·⋆)
progress (.(builtin b As ts) ·⋆ A) | inl (inl (V-builtin b As ts)) = inl (inr E-builtin·⋆)
progress (t ·⋆ A) | inl (inr p) = inl (inr (E-·⋆ p))
progress (t ·⋆ A) | inr (t' , p) = inr (t' ·⋆ A , ξ-·⋆ p)

progress (ƛ x A t) = inl (inl (V-ƛ x A t))
progress (t · u) with progress t
progress (.(ƛ x A t) · u) | inl (inl (V-ƛ x A t)) = inr (t [ u ] , β-ƛ)
progress (.(Λ x K t) · u) | inl (inl (V-Λ x K t)) = inl (inr E-Λ·)
progress (.(con tcn) · u) | inl (inl (V-con tcn)) = inl (inr E-con·)
progress (.(wrap A B t) · u) | inl (inl (V-wrap A B t)) = inl (inr E-wrap·)
progress (.(builtin b As ts) · t) | inl (inl (V-builtin b As ts)) = inr (builtin b As (ts ++ Data.List.[ t ]) , sat-builtin)
progress (t · u) | inl (inr p) = inl (inr (E-·₁ p))
progress (t · u) | inr (t' , p) = inr (t' · u , ξ-·₁ p)
progress (con c) = inl (inl (V-con c))
progress (error A) = inl (inr (E-error A))
progress (builtin b As ts) with arity b N.≟ Data.List.length ts
progress (builtin b As ts) | yes p with progressList ts
progress (builtin b As ts) | yes p | done vs = inr (BUILTIN b As vs , β-builtin vs)
progress (builtin b As ts) | yes p | step vs q ts' = inr (builtin b As _ , ξ-builtin vs q ts')
progress (builtin b As ts) | yes p | error vs e ts' = inl (inr (E-builtin e))
progress (builtin b As ts) | no ¬p = inl (inl (V-builtin b As ts))
progress (wrap A B t) = inl (inl (V-wrap A B t))
progress (unwrap  t) with progress t
progress (unwrap .(ƛ x A t)) | inl (inl (V-ƛ x A t)) = inl (inr E-ƛunwrap)
progress (unwrap .(Λ x K t)) | inl (inl (V-Λ x K t)) = inl (inr E-Λunwrap)
progress (unwrap .(con tcn)) | inl (inl (V-con tcn)) = inl (inr E-conunwrap)
progress (unwrap .(wrap A B t)) | inl (inl (V-wrap A B t)) = inr (t , β-wrap)
progress (unwrap .(builtin b As ts)) | inl (inl (V-builtin b As ts)) = inl (inr E-builtinunwrap)
progress (unwrap t) | inl (inr e) = inl (inr (E-unwrap e))
progress (unwrap t) | inr (t' , p) = inr (unwrap t' , ξ-unwrap p)
\end{code}

\begin{code}
open import Data.Nat

run : (t : ScopedTm Z) → ℕ
    → Σ (ScopedTm Z) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')
run t 0       = t , (refl , inl nothing) -- out of fuel
run t (suc n) with progress t
run t (suc n) | inl (inl vt) = t , refl , inl (just vt)
run t (suc n) | inl (inr et) = t , refl , inr et
run t (suc n) | inr (t' , p) with run t' n
run t (suc n) | inr (t' , p) | t'' , q , mvt'' = t'' , trans p q , mvt''
\end{code}
