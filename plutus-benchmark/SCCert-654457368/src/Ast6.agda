module Ast6 where

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

ast6 : Untyped

ast6 = (ULambda (ULambda (UForce (UForce (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin equalsData) (UVar 0)) (UVar 0))) (UDelay (UDelay (UConstr 0 ([]))))) (UDelay (UDelay (UApp (ULambda UError) (UApp (UApp (UForce (UBuiltin trace)) (UCon (tagCon string "The argument is not equal to itself"))) (UConstr 0 ([])))))))))))
