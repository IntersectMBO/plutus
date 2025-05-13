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
open import Ast3
open import Ast4
open import Ast5
open import Ast6
open import Ast7



asts : List (SimplifierTag × Untyped × Untyped)
asts = ((floatDelayT , (ast0 , ast0)) ∷ (forceDelayT , (ast0 , ast1)) ∷ (caseOfCaseT , (ast1 , ast1)) ∷ (caseReduceT , (ast1 , ast1)) ∷ (inlineT , (ast1 , ast2)) ∷ (floatDelayT , (ast2 , ast2)) ∷ (forceDelayT , (ast2 , ast3)) ∷ (caseOfCaseT , (ast3 , ast3)) ∷ (caseReduceT , (ast3 , ast3)) ∷ (inlineT , (ast3 , ast4)) ∷ (floatDelayT , (ast4 , ast4)) ∷ (forceDelayT , (ast4 , ast4)) ∷ (caseOfCaseT , (ast4 , ast5)) ∷ (caseReduceT , (ast5 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (cseT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (cseT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (cseT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (cseT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ [])

certificate : passed? (runCertifier asts) ≡ true
certificate = refl
