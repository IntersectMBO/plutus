\begin{code}
module Builtin.Constant.Type where
\end{code}

## Type constants

We have three base types referred to as type constants, integer,
bytestring, and size, size is used to limit the size of integers and
bytestrings

\begin{code}
data TyCon : Set where
  integer    : TyCon
  bytestring : TyCon
  size       : TyCon
\end{code}
