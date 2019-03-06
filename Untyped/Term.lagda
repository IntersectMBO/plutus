\begin{code}
module Untyped.Term where
\end{code}

\begin{code}
open import Data.Nat hiding (erase)
open import Data.Fin
open import Data.Integer hiding (suc)
open import Data.List

open import Builtin.Constant.Type -- perhaps the postulates should be elsewhere
open import Builtin
\end{code}


\begin{code}
data TermCon : Set where
  integer : ℤ → TermCon
  bytestring : ByteString → TermCon
  size : TermCon
\end{code}

\begin{code}
data _⊢ : ℕ → Set where
  `       : ∀{n} → Fin n → n ⊢
  ƛ       : ∀{n} → suc n ⊢ → n ⊢
  _·_     : ∀{n} → n ⊢ → n ⊢ → n ⊢
  con     : ∀{n} → TermCon → n ⊢
  builtin : ∀{n} → Builtin → List (n ⊢) → n ⊢
  error   : ∀{n} → n ⊢
\end{code}

\begin{code}
open import Type
open import Declarative.Term
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆ renaming (TermCon to TyTermCon)

len : Ctx → ℕ
len ∅ = 0
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = suc (len Γ)

eraseVar : ∀{Γ K}{A : ∥ Γ ∥ ⊢⋆ K} → Γ ∋ A → Fin (len Γ)
eraseVar Z     = zero
eraseVar (S α) = suc (eraseVar α) 
eraseVar (T α) = eraseVar α

eraseTC : ∀{Γ}{A : ∥ Γ ∥ ⊢⋆ *} → TyTermCon A → TermCon
eraseTC (integer s i p)    = integer i
eraseTC (bytestring s b p) = bytestring b
eraseTC (size s)           = size

open import Type.RenamingSubstitution

eraseTel : ∀{Γ Δ}{σ : Sub Δ ∥ Γ ∥}{As : List (Δ ⊢⋆ *)}
  → Tel Γ Δ σ As
  → List (len Γ ⊢)
erase : ∀{Γ K}{A : ∥ Γ ∥ ⊢⋆ K} → Γ ⊢ A → len Γ ⊢

erase (` α)             = ` (eraseVar α)
erase (ƛ t)             = ƛ (erase t) 
erase (t · u)           = erase t · erase u
erase (Λ t)             = erase t
erase (t ·⋆ A)          = erase t
erase (wrap1 pat arg t) = erase t
erase (unwrap1 t)       = erase t
erase (conv p t)        = erase t
erase {Γ} (con t)       = con (eraseTC {Γ} t)
erase (builtin bn σ ts) = builtin bn (eraseTel ts)
erase (error A)         = error

open import Data.Product renaming (_,_ to _,,_)

eraseTel {As = []}     _          = []
eraseTel {As = x ∷ As} (t ,, tel) = erase t ∷ eraseTel tel

-- conversion for scoped to untyped

open import Scoped

eraseℕ : Weirdℕ → ℕ
eraseℕ Z     = zero
eraseℕ (S n) = suc (eraseℕ n)
eraseℕ (T n) = eraseℕ n

eraseFin : ∀{n} → WeirdFin n → Fin (eraseℕ n)
eraseFin Z     = zero
eraseFin (S x) = suc (eraseFin x)
eraseFin (T x) = eraseFin x

eraseCon : SizedTermCon → TermCon
eraseCon (integer s i x) = integer i
eraseCon (bytestring s b x) = bytestring b
eraseCon (size x) = size
eraseCon (string x) = size -- this is wrong

erase⊢ : ∀{n} → ScopedTm n → eraseℕ n ⊢
erase⊢ (` x)    = ` (eraseFin x)
erase⊢ (Λ K t)  = erase⊢ t
erase⊢ (t ·⋆ A) = erase⊢ t
erase⊢ (ƛ A t)  = ƛ (erase⊢ t)

-- could add a special case for all builtins
erase⊢ (builtin addInteger · u · u') = 
  builtin addInteger (erase⊢ u ∷ erase⊢ u' ∷ []) 

erase⊢ (t · u) = erase⊢ t · erase⊢ u
erase⊢ (con c) = con (eraseCon c)
erase⊢ (error A) = error
erase⊢ (builtin b) = builtin b []

\end{code}
