module Inc where

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



asts : List (SimplifierTag × Untyped × Untyped)
asts = ((floatDelayT , (ast0 , ast1)) ∷ (forceDelayT , (ast1 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast3)) ∷ (floatDelayT , (ast3 , ast3)) ∷ (forceDelayT , (ast3 , ast4)) ∷ (caseOfCaseT , (ast4 , ast4)) ∷ (caseReduceT , (ast4 , ast4)) ∷ (inlineT , (ast4 , ast5)) ∷ (floatDelayT , (ast5 , ast5)) ∷ (forceDelayT , (ast5 , ast5)) ∷ (caseOfCaseT , (ast5 , ast5)) ∷ (caseReduceT , (ast5 , ast5)) ∷ (inlineT , (ast5 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (cseT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (cseT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (cseT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ (cseT , (ast6 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast6)) ∷ [])

certificate : passed? (runCertifier asts) ≡ true
certificate = refl
