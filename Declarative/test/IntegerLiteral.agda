module Declarative.test.IntegerLiteral where

open import Type
open import Declarative.Term
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆
open import Agda.Builtin.Sigma
open import Data.Integer
open import Data.Nat

-- plutus/language-plutus-core/test/data/integerLiteral.plc

intLit : ∀{Γ} → Γ ⊢ con integer (size⋆ 100)
intLit = con (integer 100 (ℤ.pos 102341) (-≤+ Σ., +≤+ (gen _ _ _)))
