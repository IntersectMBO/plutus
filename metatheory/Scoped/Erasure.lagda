\begin{code}
module Scoped.Erasure where
\end{code}

\begin{code}
open import Scoped
open import Untyped

open import Data.Nat
open import Data.Fin
open import Data.List
\end{code}

\begin{code}
len : ∀{n} → Weirdℕ n → ℕ
len Z     = 0
len (S i) = suc (len i)
len (T i) = len i
\end{code}

\begin{code}
eraseVar : ∀{n}{i : Weirdℕ n} → WeirdFin i → Fin (len i)
eraseVar Z     = zero
eraseVar (S x) = suc (eraseVar x)
eraseVar (T x) = eraseVar x

eraseTC : Scoped.TermCon → Untyped.TermCon
eraseTC (integer i)    = integer i
eraseTC (bytestring b) = bytestring b
eraseTC (string s)     = string s

eraseTm : ∀{n}{i : Weirdℕ n} → ScopedTm i → len i ⊢ 
eraseList : ∀{n}{i : Weirdℕ n} → List (ScopedTm i) → List (len i ⊢)

eraseList []       = []
eraseList (t ∷ ts) = eraseTm t ∷ eraseList ts

eraseTm (` x)              = ` (eraseVar x)
eraseTm (Λ K t)            = eraseTm t
eraseTm (t ·⋆ A)           = eraseTm t
eraseTm (ƛ A t)            = ƛ {!!} (eraseTm t)
eraseTm (t · u)            = eraseTm t · eraseTm u
eraseTm (con c)            = con (eraseTC c)
eraseTm (error A)          = error
eraseTm (builtin bn As ts) = builtin bn (eraseList ts)
eraseTm (wrap pat arg t)   = eraseTm t
eraseTm (unwrap t)         = eraseTm t
\end{code}
