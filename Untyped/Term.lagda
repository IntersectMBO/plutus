\begin{code}
module Untyped.Term where
\end{code}

\begin{code}
open import Data.Nat
open import Data.Fin
open import Data.Integer hiding (suc)
open import Data.List

open import Builtin.Constant.Type -- perhaps the postulates should be elsewhere
\end{code}


\begin{code}
data TermCon : Set where
  integer : ℤ → TermCon
  bytestring : ByteString → TermCon
\end{code}

\begin{code}
data _⊢ : ℕ → Set where
  `       : ∀{n} → Fin n → n ⊢
  ƛ       : ∀{n} → suc n ⊢ → n ⊢
  _·_     : ∀{n} → n ⊢ → n ⊢ → n ⊢
  con     : ∀{n} → TermCon → n ⊢
  builtin : ∀{n} → List (n ⊢) → n ⊢
  error   : ∀{n} → n ⊢
\end{code}
