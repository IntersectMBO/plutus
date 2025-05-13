module Ast9 where

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

ast9 : Untyped

ast9 = (UApp (ULambda (ULambda (UCase (UApp (ULambda (UConstr 0 ((UApp (UForce (UBuiltin headList)) (UVar 0)) ∷ []))) (UApp (UForce (UForce (UBuiltin sndPair))) (UApp (UBuiltin unConstrData) (UVar 0)))) ((ULambda (UForce (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin equalsInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UApp (UApp (UBuiltin modInteger) (UApp (UVar 2) (UApp (ULambda (UApp (UBuiltin unListData) (UApp (UForce (UBuiltin headList)) (UVar 0)))) (UApp (UForce (UBuiltin tailList)) (UApp (UForce (UBuiltin tailList)) (UApp (UForce (UForce (UBuiltin sndPair))) (UApp (UBuiltin unConstrData) (UVar 0)))))))) (UCon (tagCon integer (ℤ.pos 2)))))) (UDelay (UConstr 0 ([])))) (UDelay (UApp (ULambda UError) (UApp (UApp (UForce (UBuiltin trace)) (UCon (tagCon string "Odd number of outputs"))) (UConstr 0 ([])))))))) ∷ [])))) (UApp (ULambda (UApp (UVar 0) (UVar 0))) (ULambda (ULambda (UForce (UApp (UApp (UApp (UForce (UForce (UBuiltin chooseList))) (UVar 0)) (UDelay (UCon (tagCon integer (ℤ.pos 0))))) (UDelay (UApp (ULambda (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UApp (ULambda (UApp (UApp (UVar 3) (UVar 3)) (UVar 0))) (UApp (UForce (UBuiltin tailList)) (UVar 1))))) (UApp (UForce (UBuiltin headList)) (UVar 0))))))))))
