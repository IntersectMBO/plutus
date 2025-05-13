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
open import Ast8
open import Ast9
open import Ast10
open import Ast11
open import Ast12



asts : List (SimplifierTag × Untyped × Untyped)
asts = ((floatDelayT , (ast0 , ast1)) ∷ (forceDelayT , (ast1 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast3)) ∷ (floatDelayT , (ast3 , ast3)) ∷ (forceDelayT , (ast3 , ast4)) ∷ (caseOfCaseT , (ast4 , ast4)) ∷ (caseReduceT , (ast4 , ast4)) ∷ (inlineT , (ast4 , ast5)) ∷ (floatDelayT , (ast5 , ast5)) ∷ (forceDelayT , (ast5 , ast5)) ∷ (caseOfCaseT , (ast5 , ast6)) ∷ (caseReduceT , (ast6 , ast7)) ∷ (inlineT , (ast7 , ast8)) ∷ (floatDelayT , (ast8 , ast8)) ∷ (forceDelayT , (ast8 , ast9)) ∷ (caseOfCaseT , (ast9 , ast9)) ∷ (caseReduceT , (ast9 , ast9)) ∷ (inlineT , (ast9 , ast10)) ∷ (floatDelayT , (ast10 , ast10)) ∷ (forceDelayT , (ast10 , ast10)) ∷ (caseOfCaseT , (ast10 , ast10)) ∷ (caseReduceT , (ast10 , ast11)) ∷ (inlineT , (ast11 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ (cseT , (ast12 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ (cseT , (ast12 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ (cseT , (ast12 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ (cseT , (ast12 , ast12)) ∷ (floatDelayT , (ast12 , ast12)) ∷ (forceDelayT , (ast12 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast12)) ∷ [])

certificate : passed? (runCertifier asts) ≡ true
certificate = refl
