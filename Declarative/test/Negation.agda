module Declarative.test.Negation where

open import Type
open import Declarative.Term
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆

-- plutus/language-plutus-core/test/data/negation.plc

open import Declarative.StdLib.Bool

negate : ∀{Γ} → Γ ⊢ boolean ⇒ boolean
negate {Γ} = ƛ (if ·⋆ boolean · ` Z · false · true)
