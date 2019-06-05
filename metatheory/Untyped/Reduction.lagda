\begin{code}
module Untyped.Reduction where
\end{code}

\begin{code}
open import Untyped
open import Untyped.RenamingSubstitution
open import Builtin

open import Data.Nat hiding (_+_; _*_)
open import Data.Integer hiding (suc)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Maybe
open import Data.List hiding ([_])
open import Function
\end{code}

\begin{code}
infix 2 _—→_
\end{code}


\begin{code}
-- for untyped reduction, error also includes thing like impossible
-- applications
data Error {n} : n ⊢ → Set where
  E-error : Error error

  E-todo : ∀{t} → Error t

\end{code}

\begin{code}


data Value {n} : n ⊢ → Set where
  V-ƛ : ∀{x}(t : suc n ⊢) → Value (ƛ x t)
  V-con : (tcn : TermCon) → Value (con {n} tcn)

BUILTIN : ∀{n}
    → (bn : Builtin)
    → (vs : List (Σ (n ⊢) (Value {n})))
      -----------------------------
    → Maybe (n ⊢)

data _—→_ {n} : n ⊢ → n ⊢ → Set where
  ξ-·₁ : {L L' M : n ⊢} → L —→ L' → L · M —→ L' · M
  ξ-·₂ : {L M M' : n ⊢} → Value L → M —→ M' → L · M —→ L · M'

  E-· : {L : n ⊢}{M : n ⊢} → Error L → L · M —→ error
  E-con : {tcn : TermCon}{L : n ⊢} → con tcn · L —→ error
  β-ƛ : ∀{x}{L : suc n ⊢}{M : n ⊢} → ƛ x L · M —→ L [ M ]

  ξ-builtin : {b : Builtin}
              {ts : List (n ⊢)}
              (vs : List (Σ (n ⊢) (Value {n})))
              {t t' : n ⊢}
            → t —→ t'
            → (ts' : List (n ⊢))
            → builtin b ts —→
                builtin b (Data.List.map fst vs ++ Data.List.[ t' ] ++ ts')
  E-builtin : {b : Builtin}
              {ts : List (n ⊢)}
              (vs : List (Σ (n ⊢) (Value {n})))
              {t : n ⊢}
            → Error t
            → (ts' : List (n ⊢))
            → builtin b ts —→ error
  β-builtin : {b : Builtin}
              {ts : List (n ⊢)}
              (vs : List (Σ (n ⊢) (Value {n})))
            → builtin b ts —→ maybe id error (BUILTIN b vs)

open import Data.Unit

\end{code}


\begin{code}
data _—→⋆_ {n} : n ⊢ → n ⊢ → Set where
  refl  : {t : n ⊢} → t —→⋆ t
  trans : {t t' t'' : n ⊢} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
BUILTIN addInteger      ((_ , V-con (integer x)) ∷ (_ , V-con (integer y)) ∷ []) =
  just (con (integer (x + y)))
BUILTIN subtractInteger ((_ , V-con (integer x)) ∷ (_ , V-con (integer y)) ∷ []) =
  just (con (integer (x - y)))
BUILTIN multiplyInteger ((_ , V-con (integer x)) ∷ (_ , V-con (integer y)) ∷ []) =
  just (con (integer (x * y)))
{-
BUILTIN divideInteger vs = {!!}
BUILTIN quotientInteger vs = {!!}
BUILTIN remainderInteger vs = {!!}
BUILTIN modInteger vs = {!!}
BUILTIN lessThanInteger vs = {!!}
BUILTIN lessThanEqualsInteger vs = {!!}
BUILTIN greaterThanInteger vs = {!!}
BUILTIN greaterThanEqualsInteger vs = {!!}
BUILTIN equalsInteger vs = {!!}
BUILTIN resizeInteger vs = {!!}
BUILTIN sizeOfInteger vs = {!!}
BUILTIN concatenate vs = {!!}
BUILTIN takeByteString vs = {!!}
BUILTIN dropByteString vs = {!!}
BUILTIN sha2-256 vs = {!!}
BUILTIN sha3-256 vs = {!!}
BUILTIN verifySignature vs = {!!}
BUILTIN resizeByteString vs = {!!}
BUILTIN equalsByteString vs = {!!}
BUILTIN txh vs = {!!}
BUILTIN blocknum vs = {!!}
-}
BUILTIN _ _ = nothing -- wrong number or type of arguments...

data ProgList {n} : Set where
  done : List (Σ (n ⊢) (Value {n})) → ProgList
  step : (vs : List (Σ (n ⊢) (Value {n}))){t t' : n ⊢} → t —→ t' → List (n ⊢)
       → ProgList
  error : (vs : List (Σ (n ⊢) (Value {n}))){t : n ⊢} → Error t → List (n ⊢)
        → ProgList

progress : (t : 0 ⊢) → (Value {0} t ⊎ Error t) ⊎ Σ (0 ⊢) λ t' → t —→ t'
progressList : List (0 ⊢) → ProgList {0}
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
progress (ƛ x t)      = inl (inl (V-ƛ t))
progress (t · u)      with progress t
progress (.(ƛ _ t) · u)   | inl (inl (V-ƛ t))     = inr (t [ u ] , β-ƛ)
progress (.(con tcn) · u) | inl (inl (V-con tcn)) = inr (error , E-con)
progress (t · u)          | inl (inr e)  = inr (error , E-· e)
progress (t · u)          | inr (t' , p) = inr (t' · u  , ξ-·₁ p)
progress (con tcn)    = inl (inl (V-con tcn))
progress (builtin b ts) with progressList ts
progress (builtin b ts) | done  vs       =
  inr (maybe id error (BUILTIN b vs) , β-builtin vs)
progress (builtin b ts) | step  vs p ts' =
  inr (builtin b _ , ξ-builtin vs p ts')
progress (builtin b ts) | error vs e ts' =
  inr (error     , E-builtin vs e ts')
progress error        = inl (inr E-error)
\end{code}

\begin{code}
run : (t : 0 ⊢) → ℕ → Σ (0 ⊢) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')
run t 0       = t , (refl , inl nothing)
run t (suc n) with progress t
run t (suc n) | inl (inl vt) = t , refl , inl (just vt)
run t (suc n) | inl (inr et) = t , refl , inr et
run t (suc n) | inr (t' , p) with run t' n
run t (suc n) | inr (t' , p) | t'' , q , mvt'' = t'' , trans p q , mvt''
\end{code}
