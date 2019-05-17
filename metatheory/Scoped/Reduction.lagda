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

-- doing minimal size checking


BUILTIN : ∀{n}{w : Weirdℕ n} → Builtin
  → List (ScopedTy n) → List (Σ (ScopedTm w) (Value {n})) → ScopedTm w
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
              {ts : List (ScopedTm w)}
              (vs : List (Σ (ScopedTm w) (Value {n})))
              {t t' : ScopedTm w}
            → t —→ t'
            → (ts' : List (ScopedTm w))
            → builtin b As ts —→
              builtin b As (Data.List.map proj₁ vs ++ Data.List.[ t' ] ++ ts')
  β-builtin : {b : Builtin}
              {As : List (ScopedTy n)} -- this is the sub???
              {ts : List (ScopedTm w)}
              (vs : List (Σ (ScopedTm w) (Value {n})))
            → builtin b As ts —→ BUILTIN b As vs
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
data ProgList {n}{w : Weirdℕ n} : Set where
  done : List (Σ (ScopedTm w) (Value {n})) → ProgList
  step : (vs : List (Σ (ScopedTm w) (Value {n}))){t t' : ScopedTm w} → t —→ t' → List (ScopedTm w)
       → ProgList
  error : (vs : List (Σ (ScopedTm w) (Value {n}))){t : ScopedTm w} → Error t → List (ScopedTm w)
        → ProgList
\end{code}



\begin{code}
progress : (t : ScopedTm Z)
         → Value {w = Z} t ⊎ Error t ⊎ Σ (ScopedTm Z) λ t' → t —→ t'
progressList : List (ScopedTm Z) → ProgList {w = Z}
progressList []       = done []
progressList (t ∷ ts) with progress t
progressList (t ∷ ts) | inl vt with progressList ts
progressList (t ∷ ts) | inl vt | done  vs       = done ((t , vt) ∷ vs)
progressList (t ∷ ts) | inl vt | step  vs p ts' =
  step ((t , vt) ∷ vs) p ts'
progressList (t ∷ ts) | inl vt | error vs e ts' =
  error ((t , vt) ∷ vs) e ts'
progressList (t ∷ ts) | inr (inl e) = error [] e ts
progressList (t ∷ ts) | inr (inr (t' , p)) = step [] p ts

progress (` ())
progress (Λ x K t) = inl (V-Λ x K t)
progress (t ·⋆ A) with progress t
progress (.(ƛ x B t) ·⋆ A) | inl (V-ƛ x B t) = inr (inl E-ƛ·⋆)
progress (.(Λ x K t) ·⋆ A) | inl (V-Λ x K t) = inr (inr (t [ A ]⋆ , β-Λ))
progress (.(con tcn) ·⋆ A) | inl (V-con tcn) = inr (inl E-con·⋆)
progress (.(wrap A' B t) ·⋆ A) | inl (V-wrap A' B t) = inr (inl E-wrap·⋆)
progress (.(builtin b As ts) ·⋆ A) | inl (V-builtin b As ts) = inr (inl E-builtin·⋆)
progress (t ·⋆ A) | inr (inl p) = inr (inl (E-·⋆ p))
progress (t ·⋆ A) | inr (inr (t' , p)) = inr (inr (t' ·⋆ A , ξ-·⋆ p))

progress (ƛ x A t) = inl (V-ƛ x A t)
progress (t · u) with progress t
progress (.(ƛ x A t) · u) | inl (V-ƛ x A t) = inr (inr (t [ u ] , β-ƛ))
progress (.(Λ x K t) · u) | inl (V-Λ x K t) = inr (inl E-Λ·)
progress (.(con tcn) · u) | inl (V-con tcn) = inr (inl E-con·)
progress (.(wrap A B t) · u) | inl (V-wrap A B t) = inr (inl E-wrap·)
progress (.(builtin b As ts) · t) | inl (V-builtin b As ts) = inr (inr (builtin b As (ts ++ Data.List.[ t ]) , sat-builtin))
progress (t · u) | inr (inl p) = inr (inl (E-·₁ p))
progress (t · u) | inr (inr (t' , p)) = inr (inr (t' · u , ξ-·₁ p))
progress (con c) = inl (V-con c)
progress (error A) = inr (inl (E-error A))
progress (builtin b As ts) with arity b N.≟ Data.List.length ts
progress (builtin b As ts) | yes p with progressList ts
progress (builtin b As ts) | yes p | done vs = inr (inr (BUILTIN b As vs , β-builtin vs))
progress (builtin b As ts) | yes p | step vs q ts' = inr (inr (builtin b As _ , ξ-builtin vs q ts'))
progress (builtin b As ts) | yes p | error vs e ts' = inr (inl (E-builtin e))
progress (builtin b As ts) | no ¬p = inl (V-builtin b As ts)
progress (wrap A B t) = inl (V-wrap A B t)
progress (unwrap  t) with progress t
progress (unwrap .(ƛ x A t)) | inl (V-ƛ x A t) = inr (inl E-ƛunwrap)
progress (unwrap .(Λ x K t)) | inl (V-Λ x K t) = inr (inl E-Λunwrap)
progress (unwrap .(con tcn)) | inl (V-con tcn) = inr (inl E-conunwrap)
progress (unwrap .(wrap A B t)) | inl (V-wrap A B t) = inr (inr (t , β-wrap))
progress (unwrap .(builtin b As ts)) | inl (V-builtin b As ts) = inr (inl E-builtinunwrap)
progress (unwrap t) | inr (inl e) = inr (inl (E-unwrap e))
progress (unwrap t) | inr (inr (t' , p)) = inr (inr (unwrap t' , ξ-unwrap p))
\end{code}

\begin{code}
open import Data.Nat

run : (t : ScopedTm Z) → ℕ
    → Σ (ScopedTm Z) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')
run t 0       = t , (refl , inl nothing) -- out of fuel
run t (suc n) with progress t
run t (suc n) | inl vt = t , refl , inl (just vt)
run t (suc n) | inr (inl et) = t , refl , inr et
run t (suc n) | inr (inr (t' , p)) with run t' n
run t (suc n) | inr (inr (t' , p)) | t'' , q , mvt'' = t'' , trans p q , mvt''
\end{code}
