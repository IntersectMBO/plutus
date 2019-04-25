\begin{code}
open import Builtin.Constant.Type
open import Data.Nat
\end{code}

\begin{code}
module Builtin.Constant.Term
  (Ctx⋆ Kind : Set)
  (* : Kind)
  (_⊢⋆_ : Ctx⋆ → Kind → Set)
  (con : ∀{φ} → TyCon → φ ⊢⋆ *)
  where

open import Data.Integer
\end{code}

## Term Constants

\begin{code}
data TermCon {Φ} : Φ ⊢⋆ * → Set where
  integer    :
      (i : ℤ)
    → TermCon (con integer)
  bytestring :
      (b : ByteString)
    → TermCon (con bytestring)
\end{code}
