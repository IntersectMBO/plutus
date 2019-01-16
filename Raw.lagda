\begin{code}
module Raw where
\end{code}

\begin{code}
open import Agda.Builtin.String
\end{code}

The raw un-scope-checked and un-type-checked syntax

\begin{code}

data RawKind : Set where
  *   : RawKind
  _⇒_ : RawKind → RawKind → RawKind
    
data RawTy : Set where
  `   : String → RawTy
  _⇒_ : RawTy → RawTy → RawTy
  Π   : String → RawKind → RawTy → RawTy
  ƛ   : String → RawKind → RawTy → RawTy
  _·_ : RawTy → RawTy → RawTy

data RawTm : Set where
  `    : String → RawTm
  Λ    : String → RawKind → RawTm → RawTm
  _·⋆_ : RawTm → RawTy → RawTm
  ƛ    : String → RawTy → RawTm → RawTm
  _·_  : RawTm → RawTm → RawTm
\end{code}
