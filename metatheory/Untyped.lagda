\begin{code}
module Untyped where
\end{code}

\begin{code}
open import Data.Nat
open import Data.Fin
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
  size : TermCon
\end{code}

\begin{code}
data _⊢ : ℕ → Set where
  `       : ∀{n} → Fin n → n ⊢
  ƛ       : ∀{n} → String → suc n ⊢ → n ⊢
  _·_     : ∀{n} → n ⊢ → n ⊢ → n ⊢
  con     : ∀{n} → TermCon → n ⊢
  builtin : ∀{n} → Builtin → List (n ⊢) → n ⊢
  error   : ∀{n} → n ⊢
  wrap    : ∀{n} → n ⊢ → n ⊢
  unwrap  : ∀{n} → n ⊢ → n ⊢
\end{code}

-- conversion for scoped to untyped


\begin{code}
import Scoped as S
open import Data.Product renaming (_,_ to _,,_)

eraseℕ : ∀{n} → S.Weirdℕ n → ℕ
eraseℕ S.Z     = zero
eraseℕ (S.S n) = suc (eraseℕ n)
eraseℕ (S.T n) = eraseℕ n

eraseFin : ∀{n}{w : S.Weirdℕ n} → S.WeirdFin w → Fin (eraseℕ w)
eraseFin S.Z     = zero
eraseFin (S.S x) = suc (eraseFin x)
eraseFin (S.T x) = eraseFin x

eraseCon : S.TermCon → TermCon
eraseCon (S.integer i) = integer i
eraseCon (S.bytestring b) = bytestring b
eraseCon (S.string x) = size -- this is wrong 

open import Data.Sum

-- should do this when de Bruijnifying so it can be shared
builtinMatcher : ∀{n} → n ⊢ → (Builtin × List (n ⊢)) ⊎ n ⊢
builtinMatcher (` x) = inj₂ (` x)
builtinMatcher (ƛ x t) = inj₂ (ƛ x t)
builtinMatcher (t · u) = inj₂ (t · u)
builtinMatcher (con c) = inj₂ (con c)
builtinMatcher (builtin b ts) = inj₁ (b ,, ts)
builtinMatcher error = inj₂ error
builtinMatcher (wrap t)   = inj₂ (wrap t)
builtinMatcher (unwrap t) = inj₂ (unwrap t)

arity : Builtin → ℕ
arity _ = 2

open import Relation.Nullary

builtinEater : ∀{n} → Builtin → List (n ⊢) → n ⊢ → n ⊢
builtinEater b ts u with Data.List.length ts Data.Nat.+ 1 Data.Nat.≤? arity b
builtinEater b ts u | Dec.yes p = builtin b (ts Data.List.++ [ u ])
builtinEater b ts u | Dec.no ¬p = builtin b ts · u


erase⊢ : ∀{n}{w : S.Weirdℕ n} → S.ScopedTm w → eraseℕ w ⊢
eraseL : ∀{n}{w : S.Weirdℕ n} → List (S.ScopedTm w) → List (eraseℕ w ⊢)

erase⊢ (S.` x)    = ` (eraseFin x)
erase⊢ (S.Λ x K t)  = erase⊢ t
erase⊢ (t S.·⋆ A) = erase⊢ t
erase⊢ (S.ƛ x A t)  = ƛ x (erase⊢ t)
erase⊢ (t S.· u) with builtinMatcher (erase⊢ t)
erase⊢ (t S.· u) | inj₁ (b ,, ts) = builtinEater b ts (erase⊢ u)
erase⊢ (t S.· u) | inj₂ t' = t' · erase⊢ u
erase⊢ (S.con c) = con (eraseCon c)
erase⊢ (S.error A) = error
erase⊢ (S.builtin b _ ts) = builtin b (eraseL ts)
erase⊢ (S.wrap A B t) = wrap (erase⊢ t)
erase⊢ (S.unwrap t)   = unwrap (erase⊢ t)

eraseL [] = []
eraseL (t ∷ ts) = erase⊢ t ∷ eraseL ts
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
ugly (wrap t) = "(wrap " ++ ugly t ++ ")"
ugly (unwrap t) = "(unwrap " ++ ugly t ++ ")"
\end{code}
