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

open import Builtin.Constant.Type hiding (length)
  -- perhaps the postulates should be elsewhere
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
arity : Builtin → ℕ
arity addInteger               = 2
arity subtractInteger          = 2
arity multiplyInteger          = 2
arity divideInteger            = 2
arity quotientInteger          = 2
arity remainderInteger         = 2
arity modInteger               = 2
arity lessThanInteger          = 2
arity lessThanEqualsInteger    = 2
arity greaterThanInteger       = 2
arity greaterThanEqualsInteger = 2
arity equalsInteger            = 2
arity concatenate              = 2
arity takeByteString           = 2
arity dropByteString           = 2
arity sha2-256                 = 1
arity sha3-256                 = 1
arity verifySignature          = 3
arity equalsByteString         = 2
arity ifThenElse               = 4

data _⊢ (n : ℕ) : Set
Tel : ℕ → ℕ → Set
Tel m n = Vec (n ⊢) m

data _⊢ n where
  `       : Fin n → n ⊢
  ƛ       : suc n ⊢ → n ⊢
  _·_     : n ⊢ → n ⊢ → n ⊢
  con     : TermCon → n ⊢
  builtin : (b : Builtin){m : ℕ} → m ≤‴ arity b → (ts : Tel m n) → n ⊢
  error   : n ⊢

\end{code}


\begin{code}
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)

-- should do this when de Bruijnifying so it can be shared
{-
builtinMatcher : ∀{n} → n ⊢ → (Builtin × List (n ⊢)) ⊎ n ⊢
builtinMatcher (` x) = inj₂ (` x)
builtinMatcher (ƛ t) = inj₂ (ƛ t)
builtinMatcher (t · u) = inj₂ (t · u)
builtinMatcher (con c) = inj₂ (con c)
builtinMatcher (builtin b ts p) = inj₁ (b ,, ts)
builtinMatcher error = inj₂ error
-}
open import Relation.Nullary
{-
builtinEater : ∀{n} → Builtin → List (n ⊢) → n ⊢ → n ⊢
builtinEater b ts u with Data.List.length (ts ++ [ u ]) Data.Nat.≤? arity b
builtinEater b ts u | true because ofʸ p   = builtin b (ts Data.List.++ [ u ]) p
builtinEater b ts u | false because ofⁿ ¬p = (builtin b ts {!!}) · u
-}
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
ugly (builtin b {m} p ts) = "(builtin " +++ uglyBuiltin b +++ " " +++ showNat m +++ ")"
ugly error = "error"
\end{code}

\begin{code}
plc_true : ∀{n} → n ⊢
plc_true = con (bool true) -- ƛ (ƛ (ƛ (` (suc zero))))

plc_false : ∀{n} → n ⊢
plc_false = con (bool false) -- ƛ (ƛ (ƛ (` zero)))

plc_dummy : ∀{n} → n ⊢
plc_dummy = con unit -- ƛ (ƛ (` zero)) -- the erasure of unitval
\end{code}
