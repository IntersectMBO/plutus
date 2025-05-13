module AuctionMPCert where

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



asts : List (SimplifierTag × Untyped × Untyped)
asts = ((floatDelayT , (ast0 , ast1)) ∷ (forceDelayT , (ast1 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast3)) ∷ (floatDelayT , (ast3 , ast4)) ∷ (forceDelayT , (ast4 , ast5)) ∷ (caseOfCaseT , (ast5 , ast5)) ∷ (caseReduceT , (ast5 , ast5)) ∷ (inlineT , (ast5 , ast6)) ∷ (floatDelayT , (ast6 , ast6)) ∷ (forceDelayT , (ast6 , ast6)) ∷ (caseOfCaseT , (ast6 , ast6)) ∷ (caseReduceT , (ast6 , ast6)) ∷ (inlineT , (ast6 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (floatDelayT , (ast7 , ast7)) ∷ (forceDelayT , (ast7 , ast7)) ∷ (caseOfCaseT , (ast7 , ast7)) ∷ (caseReduceT , (ast7 , ast7)) ∷ (inlineT , (ast7 , ast7)) ∷ (cseT , (ast7 , ast8)) ∷ (floatDelayT , (ast8 , ast8)) ∷ (forceDelayT , (ast8 , ast8)) ∷ (caseOfCaseT , (ast8 , ast8)) ∷ (caseReduceT , (ast8 , ast8)) ∷ (inlineT , (ast8 , ast9)) ∷ (cseT , (ast9 , ast9)) ∷ (floatDelayT , (ast9 , ast9)) ∷ (forceDelayT , (ast9 , ast9)) ∷ (caseOfCaseT , (ast9 , ast9)) ∷ (caseReduceT , (ast9 , ast9)) ∷ (inlineT , (ast9 , ast9)) ∷ (cseT , (ast9 , ast9)) ∷ (floatDelayT , (ast9 , ast9)) ∷ (forceDelayT , (ast9 , ast9)) ∷ (caseOfCaseT , (ast9 , ast9)) ∷ (caseReduceT , (ast9 , ast9)) ∷ (inlineT , (ast9 , ast9)) ∷ (cseT , (ast9 , ast9)) ∷ (floatDelayT , (ast9 , ast9)) ∷ (forceDelayT , (ast9 , ast9)) ∷ (caseOfCaseT , (ast9 , ast9)) ∷ (caseReduceT , (ast9 , ast9)) ∷ (inlineT , (ast9 , ast9)) ∷ [])

certificate : passed? (runCertifier asts) ≡ true
certificate = refl
