\begin{code}
module Untyped where
\end{code}

\begin{code}
open import Data.Nat
open import Data.Fin hiding (_≤_)
open import Data.Bool using (Bool;true;false)
open import Data.Integer hiding (suc;_≤_)
open import Data.Vec
open import Data.String using (String) renaming (_++_ to _+++_)
open import Data.Char

open import Builtin
\end{code}


\begin{code}
data TermCon : Set where
  integer    : ℤ → TermCon
  bytestring : ByteString → TermCon
  string     : String → TermCon
  bool       : Bool → TermCon
  char       : Char → TermCon
  unit       : TermCon
\end{code}

\begin{code}
data _⊢ n : Set where
  `       : Fin n → n ⊢
  ƛ       : suc n ⊢ → n ⊢
  _·_     : n ⊢ → n ⊢ → n ⊢
  force   : n ⊢ → n ⊢
  delay   : n ⊢ → n ⊢
  con     : TermCon → n ⊢
  builtin : (b : Builtin) → n ⊢
  error   : n ⊢
\end{code}


\begin{code}
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Nullary
\end{code}

\begin{code}
open import Data.String

uglyFin : ∀{n} → Fin n → String
uglyFin zero = "0"
uglyFin (suc x) = "(S " +++ uglyFin x +++ ")"


uglyTermCon : TermCon → String
uglyTermCon (integer x) = "(integer " +++ Data.Integer.show x +++ ")"
uglyTermCon (bytestring x) = "bytestring"
uglyTermCon unit = "()"
uglyTermCon (string s) = "(string " +++ s +++ ")"
uglyTermCon (bool false) = "(bool " +++ "false" +++ ")"
uglyTermCon (bool true) = "(bool " +++ "true" +++ ")"
uglyTermCon (char c) = "(char)"

{-# FOREIGN GHC import qualified Data.Text as T #-}

postulate showNat : ℕ → String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC showNat = T.pack . show #-}

uglyBuiltin : Builtin → String
uglyBuiltin addInteger = "addInteger"
uglyBuiltin _ = "other"
ugly : ∀{n} → n  ⊢ → String
ugly (` x) = "(` " +++ uglyFin x +++ ")"
ugly (ƛ t) = "(ƛ " +++ ugly t +++ ")"
ugly (t · u) = "( " +++ ugly t +++ " · " +++ ugly u +++ ")"
ugly (con c) = "(con " +++ uglyTermCon c +++ ")"
ugly (force t) = "(f0rce " +++ ugly t +++ ")"
ugly (delay t) = "(delay " +++ ugly t +++ ")"
ugly (builtin b) = "(builtin " +++ uglyBuiltin b +++ ")"
ugly error = "error"
\end{code}
