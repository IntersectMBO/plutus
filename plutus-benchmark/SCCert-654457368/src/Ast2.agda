module Ast2 where

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

ast2 : Untyped

ast2 = (ULambda (ULambda (UForce (UApp (UApp (UForce (UApp (ULambda (UDelay (ULambda (ULambda (UCase (UVar 2) ((UVar 1) ∷ (UVar 0) ∷ [])))))) (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin equalsData) (UVar 0)) (UVar 0))) (UConstr 0 ([]))) (UConstr 1 ([]))))) (UDelay (UConstr 0 ([])))) (UDelay (UApp (ULambda UError) (UApp (UApp (UForce (UBuiltin trace)) (UCon (tagCon string "The argument is not equal to itself"))) (UConstr 0 ([])))))))))
