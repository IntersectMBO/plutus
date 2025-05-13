module Ast0 where

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

ast0 : Untyped

ast0 = (ULambda (UApp (UApp (UApp (UForce (UDelay (ULambda (ULambda (ULambda (UApp (UApp (UForce (UDelay (ULambda (ULambda (UVar 1))))) (UConstr 0 ([]))) (ULambda (UDelay (ULambda (UCase (UVar 1) ((UVar 0) ∷ []))))))))))) (UConstr 0 ([]))) (UConstr 1 ([]))) (ULambda (UDelay (ULambda (ULambda (UCase (UVar 2) ((UVar 1) ∷ (UVar 0) ∷ []))))))))
