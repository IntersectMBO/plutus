\begin{code}
module Untyped.Reduction where
\end{code}

\begin{code}
open import Untyped
open import Untyped.RenamingSubstitution
open import Builtin
open import Builtin.Constant.Type

import Data.Bool as Bool
open import Data.Nat hiding (_<_; _≤?_; _^_; _+_; _≟_; _*_)
open import Data.Integer hiding (suc)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.List hiding ([_]; take; drop)
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_];trans)
open import Utils
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

VTel : ∀ n → Tel n → Set
VTel n []       = ⊤
VTel n (t ∷ ts) = Value {n} t × VTel n ts

BUILTIN : ∀{n}
    → (bn : Builtin)
    → (tel : Tel n)
    → VTel n tel
      --------------
    → n ⊢

data _—→_ {n} : n ⊢ → n ⊢ → Set where
  ξ-·₁ : {L L' M : n ⊢} → L —→ L' → L · M —→ L' · M
  ξ-·₂ : {L M M' : n ⊢} → Value L → M —→ M' → L · M —→ L · M'

  E-· : {L : n ⊢}{M : n ⊢} → Error L → L · M —→ error
  E-con : {tcn : TermCon}{L : n ⊢} → con tcn · L —→ error
  β-ƛ : ∀{x}{L : suc n ⊢}{M : n ⊢} → ƛ x L · M —→ L [ M ]

  ξ-builtin : (b : Builtin)
              (ts : Tel n)
              {ts' : Tel n}
              (vs : VTel n ts')
              {t t' : n ⊢}
            → t —→ t'
            → (ts'' : Tel n)
            → (ts''' : Tel n)
            → ts''' ≡ ts' ++ Data.List.[ t' ] ++ ts''
            → builtin b ts —→
                builtin b ts'''
  E-builtin : {b : Builtin}
              {ts : List (n ⊢)}
              {ts' : List (n ⊢)}
              (vs : VTel n ts')
              {t : n ⊢}
            → Error t
            → (ts'' : Tel n)
            → builtin b ts —→ error
  β-builtin : {b : Builtin}
              (ts : Tel n)
              (vs : VTel n ts)
            → builtin b ts —→ BUILTIN b ts vs
\end{code}


\begin{code}
data _—→⋆_ {n} : n ⊢ → n ⊢ → Set where
  refl  : {t : n ⊢} → t —→⋆ t
  trans : {t t' t'' : n ⊢} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
VERIFYSIG : ∀{n} → Maybe Bool.Bool → n ⊢
VERIFYSIG (just Bool.false) = false 
VERIFYSIG (just Bool.true)  = true 
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
  decIf (i Builtin.Constant.Type.<? j) true false 
BUILTIN lessThanEqualsInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i ≤? j) true false 
BUILTIN greaterThanInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i Builtin.Constant.Type.>? j) true false 
BUILTIN greaterThanEqualsInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i Builtin.Constant.Type.≥? j) true false 
BUILTIN equalsInteger (_ ∷ _ ∷ []) (V-con (integer i) , V-con (integer j) , tt) =
  decIf (i ≟ j) true false 
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
  Bool.if (equals b b') then true else false 
BUILTIN _ _ _ = error

data ProgList {n} (tel : Tel n) : Set where
  done : VTel n tel → ProgList tel
  step : (tel' : Tel n) → VTel n tel' → {t t' : n ⊢} → t —→ t' → Tel n
    → ProgList tel 
  error : (tel' : Tel n) → VTel n tel' → {t : n ⊢} → Error t → Tel n
    → ProgList tel

progress : (t : 0 ⊢) → (Value {0} t ⊎ Error t) ⊎ Σ (0 ⊢) λ t' → t —→ t'
progressList : (tel : Tel 0) → ProgList {0} tel
progressList []       = done _
progressList (t ∷ ts) with progress t
progressList (t ∷ ts) | inl (inl vt) with progressList ts
progressList (t ∷ ts) | inl (inl vt) | done vs   = done (vt , vs)
progressList (t ∷ ts) | inl (inl vt) | step  ts' vs p ts'' =
  step (t ∷ ts') (vt , vs) p ts''
progressList (t ∷ ts) | inl (inl vt) | error ts' vs e ts'' =
  error (t ∷ ts') (vt , vs) e ts''
progressList (t ∷ ts) | inl (inr e) = error [] _ e ts
progressList (t ∷ ts) | inr (t' , p) = step [] _ p ts

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
  inr (BUILTIN b ts vs ,  β-builtin ts vs)
progress (builtin b ts) | step  ts' vs p ts'' =
  inr (builtin b _ ,  ξ-builtin b ts vs p ts'' (ts' ++ _ ∷ ts'') refl)
progress (builtin b ts) | error ts' vs e ts'' =
  inr (error     , E-builtin vs e ts')
progress error       = inl (inr E-error)
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
