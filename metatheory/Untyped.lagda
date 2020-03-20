\begin{code}
module Untyped where
\end{code}

\begin{code}
open import Data.Nat
open import Data.Fin
open import Data.Bool using (Bool;true;false)
open import Data.Integer hiding (suc)
open import Data.List hiding (_++_)
open import Data.String
open import Data.Char

open import Builtin.Constant.Type -- perhaps the postulates should be elsewhere
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
Tel : ℕ → Set

data _⊢ : ℕ → Set where
  `       : ∀{n} → Fin n → n ⊢
  ƛ       : ∀{n} → suc n ⊢ → n ⊢
  _·_     : ∀{n} → n ⊢ → n ⊢ → n ⊢
  con     : ∀{n} → TermCon → n ⊢
  builtin : ∀{n} → Builtin → Tel n → n ⊢
  error   : ∀{n} → n ⊢
  if_then_else_ : ∀{n} → n ⊢ → n ⊢ → n ⊢ → n ⊢

Tel n = List (n ⊢)
\end{code}


\begin{code}
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)

-- should do this when de Bruijnifying so it can be shared
builtinMatcher : ∀{n} → n ⊢ → (Builtin × List (n ⊢)) ⊎ n ⊢
builtinMatcher (` x) = inj₂ (` x)
builtinMatcher (ƛ t) = inj₂ (ƛ t)
builtinMatcher (t · u) = inj₂ (t · u)
builtinMatcher (con c) = inj₂ (con c)
builtinMatcher (builtin b ts) = inj₁ (b ,, ts)
builtinMatcher error = inj₂ error
builtinMatcher (if b then t else f) = inj₂ error

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
ugly (ƛ t) = "(ƛ " ++ ugly t ++ ")"
ugly (t · u) = "( " ++ ugly t ++ " · " ++ ugly u ++ ")"
ugly (con c) = "(con " ++ uglyTermCon c ++ ")"
ugly (builtin b ts) = "(builtin " ++ uglyBuiltin b ++ " " ++ showNat (Data.List.length ts) ++ ")"
ugly error = "error"
ugly (if b then t else f) = "ifthenelse"
\end{code}

\begin{code}
plc_true : ∀{n} → n ⊢
plc_true = con (bool true) -- ƛ (ƛ (ƛ (` (suc zero))))

plc_false : ∀{n} → n ⊢
plc_false = con (bool false) -- ƛ (ƛ (ƛ (` zero)))

plc_dummy : ∀{n} → n ⊢
plc_dummy = ƛ (ƛ (` zero)) -- the erasure of unitval
\end{code}
