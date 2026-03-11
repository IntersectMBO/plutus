module Ast1 where

open import VerifiedCompilation
open import VerifiedCompilation.Certificate
open import Untyped
open import RawU
open import Builtin
open import Data.Unit
open import Data.Nat
open import Data.Integer
open import Utils
import Agda.Builtin.Bool
import Relation.Nullary
import VerifiedCompilation.UntypedTranslation
open import Agda.Builtin.Maybe
open import Data.Empty using (⊥)
open import Data.Bool.Base using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

ast1 : Untyped

ast1 = (UApp (ULambda (UForce (UDelay (UVar 0)))) (ULambda (UApp (ULambda (UApp (UApp (UApp (UForce (UApp (ULambda (UForce (UDelay (UVar 0)))) (UDelay (ULambda (UVar 0))))) (UApp (ULambda (UApp (ULambda (UApp (ULambda (UForce (UVar 0))) (UDelay (UForce (UDelay (UVar 0)))))) (ULambda (UApp (ULambda (ULambda (UApp (ULambda (UApp (UApp (UVar 4) (UVar 2)) (UVar 0))) (UVar 0)))) (UVar 0))))) (UBuiltin addInteger))) (UCon (tagCon integer (ℤ.pos 1)))) (UVar 0))) (UVar 0))))
