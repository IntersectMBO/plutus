module Ast3 where

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

ast3 : Untyped

ast3 = (ULambda (UApp (UApp (UApp (UForce (UDelay (ULambda (UVar 0)))) (UForce (UDelay (ULambda (ULambda (UApp (UApp (UBuiltin addInteger) (UVar 1)) (UVar 0))))))) (UCon (tagCon integer (ℤ.pos 1)))) (UVar 0)))
