\begin{code}
module Untyped where
\end{code}

\begin{code}
open import Data.Nat
open import Data.Fin
open import Data.Bool using (true;false)
open import Data.Integer hiding (suc)
open import Data.List hiding (_++_)
open import Data.String

open import Builtin.Constant.Type -- perhaps the postulates should be elsewhere
open import Builtin
\end{code}


\begin{code}
data TermCon : Set where
  integer : ℤ → TermCon
  bytestring : ByteString → TermCon
  string : String → TermCon
\end{code}

\begin{code}
Tel : ℕ → Set

data _⊢ : ℕ → Set where
  `       : ∀{n} → Fin n → n ⊢
  ƛ       : ∀{n} → String → suc n ⊢ → n ⊢
  _·_     : ∀{n} → n ⊢ → n ⊢ → n ⊢
  con     : ∀{n} → TermCon → n ⊢
  builtin : ∀{n} → Builtin → Tel n → n ⊢
  error   : ∀{n} → n ⊢

Tel n = List (n ⊢)
\end{code}


\begin{code}
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)

-- should do this when de Bruijnifying so it can be shared
builtinMatcher : ∀{n} → n ⊢ → (Builtin × List (n ⊢)) ⊎ n ⊢
builtinMatcher (` x) = inj₂ (` x)
builtinMatcher (ƛ x t) = inj₂ (ƛ x t)
builtinMatcher (t · u) = inj₂ (t · u)
builtinMatcher (con c) = inj₂ (con c)
builtinMatcher (builtin b ts) = inj₁ (b ,, ts)
builtinMatcher error = inj₂ error

arity : Builtin → ℕ
arity _ = 2

open import Relation.Nullary

builtinEater : ∀{n} → Builtin → List (n ⊢) → n ⊢ → n ⊢
builtinEater b ts u with Data.List.length ts Data.Nat.+ 1 Data.Nat.≤? arity b
builtinEater b ts u | true because ofʸ p   = builtin b (ts Data.List.++ [ u ])
builtinEater b ts u | false because ofⁿ ¬p = builtin b ts · u
\end{code}

\begin{code}
open import Data.String

uglyFin : ∀{n} → Fin n → String
uglyFin zero = "0"
uglyFin (suc x) = "(S " ++ uglyFin x ++ ")"


uglyTermCon : TermCon → String
uglyTermCon (integer x) = "(integer " ++ Data.Integer.show x ++ ")"
uglyTermCon (bytestring x) = "bytestring"
uglyTermCon size = "size"

{-# FOREIGN GHC import qualified Data.Text as T #-}

postulate showNat : ℕ → String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC showNat = T.pack . show #-}

uglyBuiltin : Builtin → String
uglyBuiltin addInteger = "addInteger"
uglyBuiltin _ = "other"
ugly : ∀{n} → n  ⊢ → String
ugly (` x) = "(` " ++ uglyFin x ++ ")"
ugly (ƛ x t) = "(ƛ " ++ x ++  ugly t ++ ")"
ugly (t · u) = "( " ++ ugly t ++ " · " ++ ugly u ++ ")"
ugly (con c) = "(con " ++ uglyTermCon c ++ ")"
ugly (builtin b ts) = "(builtin " ++ uglyBuiltin b ++ " " ++ showNat (Data.List.length ts) ++ ")"
ugly error = "error"
\end{code}

\begin{code}
plc_true : ∀{n} → n ⊢
plc_true = ƛ "t" (ƛ "f" (` (suc zero)))

plc_false : ∀{n} → n ⊢
plc_false = ƛ "t" (ƛ "f" (` zero))
\end{code}
