module test.AddInteger where

open import Type
open import Declarative.Term
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆
open import Agda.Builtin.Sigma

-- plutus/language-plutus-core/test/data/addInteger.plc

addI : ∀{Γ} →
  Γ ⊢ con integer (size⋆ 8) ⇒ con integer (size⋆ 8) ⇒ con integer (size⋆ 8)
addI =
  ƛ (ƛ (builtin addInteger (λ { Z → size⋆ 8 ; (S ())}) (` (S Z) Σ., ` Z Σ., _)))
