\begin{code}
module Scoped.Reduction where
\end{code}

\begin{code}
open import Scoped
open import Scoped.RenamingSubstitution
open import Builtin
open import Builtin.Constant.Type

open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Product
open import Data.List hiding ([_])
open import Data.Maybe
open import Function
open import Data.Integer as I
open import Data.Nat as N
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_];trans)
\end{code}

\begin{code}
infix 2 _—→_
\end{code}

\begin{code}
data Value {n} : ScopedTm n → Set where
  V-ƛ : (A : ScopedTy ∥ n ∥)(t : ScopedTm (S n)) → Value (ƛ A t)
  V-Λ : ∀ K (t : ScopedTm (T n)) → Value (Λ K t)
  V-con : (tcn : SizedTermCon) → Value (con {n} tcn)
  V-wrap : (A B : ScopedTy ∥ n ∥)(t : ScopedTm n) → Value (wrap A B t)

-- a term that satisfies this predicate has an error term in it somewhere
-- or we encountered a rumtime type error
data Error {n} : ScopedTm n → Set where
   E-error : (A : ScopedTy ∥ n ∥) → Error (error A)

   -- error inside somewhere
   E-·     : {L M : ScopedTm n} → Error L → Error (L · M)
   E-·⋆    : {L : ScopedTm n}{A : ScopedTy ∥ n ∥} → Error L → Error (L ·⋆ A)
   E-unwrap : {L : ScopedTm n} → Error L → Error (unwrap L)
   
   -- runtime type errors
   E-Λ·    : ∀{K}{L : ScopedTm (T n)}{M : ScopedTm n} → Error (Λ K L · M)
   E-ƛ·⋆   : ∀{B : ScopedTy ∥ n ∥}{L : ScopedTm (S n)}{A : ScopedTy ∥ n ∥}
     → Error (ƛ B L ·⋆ A)
   E-con·  : ∀{tcn}{M : ScopedTm n} → Error (con tcn · M)
   E-con·⋆ : ∀{tcn}{A : ScopedTy ∥ n ∥} → Error (con tcn ·⋆ A)
   E-wrap· : {A B : ScopedTy ∥ n ∥}{t M : ScopedTm n} → Error (wrap A B t · M)
   E-wrap·⋆ : {A' B A : ScopedTy ∥ n ∥}{t : ScopedTm n}
     → Error (wrap A' B t ·⋆ A)
   E-ƛunwrap : {A : ScopedTy ∥ n ∥}{t : ScopedTm (S n)}
     → Error (unwrap (ƛ A t) )
   E-Λunwrap : ∀{K}{t : ScopedTm (T n)} → Error (unwrap (Λ K t))
   E-conunwrap : ∀{tcn} → Error (unwrap (con tcn))

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
BUILTIN addInteger _ ((_ , V-con (integer  s  i p)) ∷ (_ , V-con (integer s' i' p')) ∷ []) with s N.≟ s'
BUILTIN addInteger _ ((_ , V-con (integer .s i p)) ∷ (_ , V-con (integer s i' p')) ∷ []) | yes refl with boundedI? s (i I.+ i')
BUILTIN addInteger _ ((_ , V-con (integer .s i p)) ∷ (_ , V-con (integer s i' p')) ∷ []) | yes refl | yes r = con (integer s (i I.+ i') r)
BUILTIN addInteger _ ((_ , V-con (integer .s i p)) ∷ (_ , V-con (integer s i' p')) ∷ []) | yes refl | no ¬r = error (con integer)
BUILTIN addInteger _ ((_ , V-con (integer  s  i p)) ∷ (_ , V-con (integer s' i' p')) ∷ []) | no ¬q
  = error (con integer)
BUILTIN addInteger _ _ = error (con integer)
  -- this covers a multitude of sins
BUILTIN subtractInteger _ ((_ , V-con (integer  s  i p)) ∷ (_ , V-con (integer s' i' p')) ∷ []) with s N.≟ s'
BUILTIN subtractInteger _ ((_ , V-con (integer .s i p)) ∷ (_ , V-con (integer s i' p')) ∷ []) | yes refl with boundedI? s (i I.- i')
BUILTIN subtractInteger _ ((_ , V-con (integer .s i p)) ∷ (_ , V-con (integer s i' p')) ∷ []) | yes refl | yes r = con (integer s (i I.- i') r)
BUILTIN subtractInteger _ ((_ , V-con (integer .s i p)) ∷ (_ , V-con (integer s i' p')) ∷ []) | yes refl | no ¬r = error (con integer)
BUILTIN subtractInteger _ ((_ , V-con (integer  s  i p)) ∷ (_ , V-con (integer s' i' p')) ∷ []) | no ¬q = error (con integer)
BUILTIN subtractInteger _ _ = error (con integer)
BUILTIN _ _ _ = error (con integer)


data _—→_ {n} : ScopedTm n → ScopedTm n → Set where
  ξ-· : {L L' M : ScopedTm n} → L —→ L' → L · M —→ L' · M
  ξ-·⋆ : {L L' : ScopedTm n}{A : ScopedTy ∥ n ∥} → L —→ L' → L ·⋆ A —→ L' ·⋆ A
  β-ƛ : {A : ScopedTy ∥ n ∥}{L : ScopedTm (S n)}{M : ScopedTm n}
      → (ƛ A L) · M —→ (L [ M ])
  β-Λ : ∀{K}{L : ScopedTm (T n)}{A : ScopedTy ∥ n ∥}
      → (Λ K L) ·⋆ A —→ (L [ A ]⋆)
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
progress (Λ K t) = inl (inl (V-Λ K t))
progress (t ·⋆ A) with progress t
progress (.(ƛ B t) ·⋆ A) | inl (inl (V-ƛ B t)) = inl (inr E-ƛ·⋆)
progress (.(Λ K t) ·⋆ A) | inl (inl (V-Λ K t)) = inr (t [ A ]⋆ , β-Λ)
progress (.(con tcn) ·⋆ A) | inl (inl (V-con tcn)) = inl (inr E-con·⋆)
progress (.(wrap A' B t) ·⋆ A) | inl (inl (V-wrap A' B t)) = inl (inr E-wrap·⋆)
progress (t ·⋆ A) | inl (inr p) = inl (inr (E-·⋆ p))
progress (t ·⋆ A) | inr (t' , p) = inr (t' ·⋆ A , ξ-·⋆ p)
progress (ƛ A t) = inl (inl (V-ƛ A t))
progress (t · u) with progress t
progress (.(ƛ A t) · u) | inl (inl (V-ƛ A t)) = inr (t [ u ] , β-ƛ)
progress (.(Λ K t) · u) | inl (inl (V-Λ K t)) = inl (inr E-Λ·)
progress (.(con tcn) · u) | inl (inl (V-con tcn)) = inl (inr E-con·)
progress (.(wrap A B t) · u) | inl (inl (V-wrap A B t)) = inl (inr E-wrap·)
progress (t · u) | inl (inr p) = inl (inr (E-· p))
progress (t · u) | inr (t' , p) = inr (t' · u , ξ-· p)
progress (con c) = inl (inl (V-con c))
progress (error A) = inl (inr (E-error A))
progress (builtin b As ts) with progressList ts
progress (builtin b As ts) | done  vs       = inr (BUILTIN b As vs , β-builtin vs)
progress (builtin b As ts) | step  vs p ts' = inr (builtin b As _ , ξ-builtin vs p ts')
progress (builtin b As ts) | error vs e ts' = inl (inr (E-builtin e))
progress (wrap A B t) = inl (inl (V-wrap A B t))
progress (unwrap  t) with progress t
progress (unwrap .(ƛ A t)) | inl (inl (V-ƛ A t)) = inl (inr E-ƛunwrap)
progress (unwrap .(Λ K t)) | inl (inl (V-Λ K t)) = inl (inr E-Λunwrap)
progress (unwrap .(con tcn)) | inl (inl (V-con tcn)) = inl (inr E-conunwrap)
progress (unwrap .(wrap A B t)) | inl (inl (V-wrap A B t)) = inr (t , β-wrap)
progress (unwrap t) | inl (inr e) = inl (inr (E-unwrap e))
progress (unwrap t) | inr (t' , p) = inr (unwrap t' , ξ-unwrap p)
\end{code}

\begin{code}
open import Data.Nat
open import Data.Maybe

run : (t : ScopedTm Z) → ℕ
    → Σ (ScopedTm Z) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')
run t 0       = t , (refl , inl nothing) -- out of fuel
run t (suc n) with progress t
run t (suc n) | inl (inl vt) = t , refl , inl (just vt)
run t (suc n) | inl (inr et) = t , refl , inr et
run t (suc n) | inr (t' , p) with run t' n
run t (suc n) | inr (t' , p) | t'' , q , mvt'' = t'' , trans p q , mvt''
\end{code}
