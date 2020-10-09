\begin{code}
open import Builtin.Constant.Type
\end{code}

\begin{code}
module Builtin.Constant.Term
  (Ctx⋆ Kind : Set)
  (* : Kind)
  (_⊢⋆_ : Ctx⋆ → Kind → Set)
  (con : ∀{φ} → TyCon → φ ⊢⋆ *)
  where

open import Data.Integer
open import Data.String
open import Data.Char
open import Data.Bool
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
  string     :
      (s : String)
    → TermCon (con string)
  bool       :
      (b : Bool)
    → TermCon (con bool)
  char       :
      (c : Char)
    → TermCon (con char)
  unit       : TermCon (con unit)
\end{code}
