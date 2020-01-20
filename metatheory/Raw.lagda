\begin{code}
module Raw where
\end{code}

\begin{code}
open import Data.String
open import Data.Nat

open import Builtin.Constant.Type
open import Builtin
\end{code}

The raw un-scope-checked and un-type-checked syntax

\begin{code}

data RawKind : Set where
  *   : RawKind
  _⇒_ : RawKind → RawKind → RawKind

data RawTy : Set where
  `   : ℕ → RawTy
  _⇒_ : RawTy → RawTy → RawTy
  Π   : RawKind → RawTy → RawTy
  ƛ   : RawKind → RawTy → RawTy
  _·_ : RawTy → RawTy → RawTy
  con : TyCon → RawTy
  μ    : RawTy → RawTy → RawTy

open import Data.Nat
open import Data.Integer

data RawTermCon : Set where
  integer : ℤ → RawTermCon
  bytestring : ByteString → RawTermCon
  string : String → RawTermCon

data RawTm : Set where
  `       : ℕ → RawTm
  Λ       : RawKind → RawTm → RawTm
  _·⋆_    : RawTm → RawTy → RawTm
  ƛ       : RawTy → RawTm → RawTm
  _·_     : RawTm → RawTm → RawTm
  con     : RawTermCon → RawTm
  error   : RawTy → RawTm
  builtin : Builtin → RawTm
  wrap    : RawTy → RawTy → RawTm → RawTm
  unwrap  : RawTm → RawTm

{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC RawTermCon = data RConstant (RConInt | RConBS | RConStr) #-}
{-# COMPILE GHC RawTm = data RTerm (RVar | RTLambda  | RTApp | RLambda  | RApp | RCon | RError | RBuiltin | RWrap | RUnWrap) #-}
{-# COMPILE GHC RawTy = data RType (RTyVar | RTyFun | RTyPi | RTyLambda | RTyApp | RTyCon | RTyMu) #-}
{-# COMPILE GHC RawKind = data RKind (RKiStar | RKiFun) #-}

-- We have to different approaches to de Bruijn terms.
-- one counts type and term binders separately the other counts them together

rawTyPrinter : RawTy → String
rawTyPrinter (` x)   = Data.Integer.show (ℤ.pos x)
rawTyPrinter (A ⇒ B) = "(" ++ rawTyPrinter A ++ "⇒" ++ rawTyPrinter B ++ ")"
rawTyPrinter (Π K A) = "(Π" ++ "kind" ++ rawTyPrinter A ++ ")"
rawTyPrinter (ƛ K A) = "(ƛ" ++ "kind" ++ rawTyPrinter A ++ ")"
rawTyPrinter (A · B) = "(" ++ rawTyPrinter A ++ "·" ++ rawTyPrinter B ++ ")"
rawTyPrinter (con c) = "(con)"
rawTyPrinter (μ A B) = "(μ" ++ rawTyPrinter A ++ rawTyPrinter B ++ ")"

rawPrinter : RawTm → String
rawPrinter (` x) = Data.Integer.show (ℤ.pos x)
rawPrinter (Λ K t) = "(" ++ "Λ" ++ "kind" ++ rawPrinter t ++ ")"
rawPrinter (t ·⋆ A) = "(" ++ rawPrinter t ++ "·⋆" ++ rawTyPrinter A ++ ")"
rawPrinter (ƛ A t) = "(" ++ "ƛ" ++ rawTyPrinter A ++ rawPrinter t ++ ")"
rawPrinter (t · u) = "(" ++ rawPrinter t ++ "·" ++ rawPrinter u ++ ")"
rawPrinter (con c) = "(con)" 
rawPrinter (error A) = "(error" ++ rawTyPrinter A ++ ")"
rawPrinter (builtin b) = "(builtin)"
rawPrinter (wrap pat arg t) = "(wrap" ++ ")"
rawPrinter (unwrap t) = "(unwrap" ++ rawPrinter t ++ ")"
\end{code}
