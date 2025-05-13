module SCCert where

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
open import Ast0
open import Ast1
open import Ast2



asts : List (SimplifierTag × Untyped × Untyped)
asts = ((floatDelayT , (ast0 , ast0)) ∷ (forceDelayT , (ast0 , ast1)) ∷ (caseOfCaseT , (ast1 , ast1)) ∷ (caseReduceT , (ast1 , ast1)) ∷ (inlineT , (ast1 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (cseT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (cseT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (cseT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ (cseT , (ast2 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast2)) ∷ [])

certificate : passed? (runCertifier asts) ≡ true
certificate = refl
