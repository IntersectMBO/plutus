module test.IntegerOverflow where

open import Type
open import Declarative
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆
open import Agda.Builtin.Sigma
open import Data.Integer
open import Data.Nat
open import Data.Empty

-- plutus/language-plutus-core/test/data/integerOverflow.plc

-- This term is impossible as terms are intrinsically sized

-- completeting this definition requires an element of the empty type
{-
intOverflow : ∀{Γ} → Γ ⊢ con integer (size⋆ 1)
intOverflow = con (integer 1 (ℤ.pos 128) (-≤+ Σ., +≤+ (gen _ _ {!!})))
-}

