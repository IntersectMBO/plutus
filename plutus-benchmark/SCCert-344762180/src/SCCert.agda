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
open import Ast13
open import Ast14
open import Ast15
open import Ast16
open import Ast17
open import Ast18
open import Ast19
open import Ast20
open import Ast21
open import Agda.Builtin.Sigma using (Σ; _,_)



asts : List (SimplifierTag × Untyped × Untyped)
asts = ((floatDelayT , (ast0 , ast1)) ∷ (forceDelayT , (ast1 , ast2)) ∷ (caseOfCaseT , (ast2 , ast2)) ∷ (caseReduceT , (ast2 , ast2)) ∷ (inlineT , (ast2 , ast3)) ∷ (floatDelayT , (ast3 , ast4)) ∷ (forceDelayT , (ast4 , ast5)) ∷ (caseOfCaseT , (ast5 , ast5)) ∷ (caseReduceT , (ast5 , ast5)) ∷ (inlineT , (ast5 , ast6)) ∷ (floatDelayT , (ast6 , ast7)) ∷ (forceDelayT , (ast7 , ast8)) ∷ (caseOfCaseT , (ast8 , ast9)) ∷ (caseReduceT , (ast9 , ast10)) ∷ (inlineT , (ast10 , ast11)) ∷ (floatDelayT , (ast11 , ast11)) ∷ (forceDelayT , (ast11 , ast12)) ∷ (caseOfCaseT , (ast12 , ast12)) ∷ (caseReduceT , (ast12 , ast12)) ∷ (inlineT , (ast12 , ast13)) ∷ (floatDelayT , (ast13 , ast13)) ∷ (forceDelayT , (ast13 , ast13)) ∷ (caseOfCaseT , (ast13 , ast13)) ∷ (caseReduceT , (ast13 , ast13)) ∷ (inlineT , (ast13 , ast13)) ∷ (floatDelayT , (ast13 , ast13)) ∷ (forceDelayT , (ast13 , ast13)) ∷ (caseOfCaseT , (ast13 , ast13)) ∷ (caseReduceT , (ast13 , ast13)) ∷ (inlineT , (ast13 , ast13)) ∷ (floatDelayT , (ast13 , ast13)) ∷ (forceDelayT , (ast13 , ast13)) ∷ (caseOfCaseT , (ast13 , ast13)) ∷ (caseReduceT , (ast13 , ast13)) ∷ (inlineT , (ast13 , ast13)) ∷ (floatDelayT , (ast13 , ast13)) ∷ (forceDelayT , (ast13 , ast13)) ∷ (caseOfCaseT , (ast13 , ast13)) ∷ (caseReduceT , (ast13 , ast13)) ∷ (inlineT , (ast13 , ast13)) ∷ (floatDelayT , (ast13 , ast13)) ∷ (forceDelayT , (ast13 , ast13)) ∷ (caseOfCaseT , (ast13 , ast13)) ∷ (caseReduceT , (ast13 , ast13)) ∷ (inlineT , (ast13 , ast13)) ∷ (floatDelayT , (ast13 , ast13)) ∷ (forceDelayT , (ast13 , ast13)) ∷ (caseOfCaseT , (ast13 , ast13)) ∷ (caseReduceT , (ast13 , ast13)) ∷ (inlineT , (ast13 , ast13)) ∷ (floatDelayT , (ast13 , ast13)) ∷ (forceDelayT , (ast13 , ast13)) ∷ (caseOfCaseT , (ast13 , ast13)) ∷ (caseReduceT , (ast13 , ast13)) ∷ (inlineT , (ast13 , ast13)) ∷ (floatDelayT , (ast13 , ast13)) ∷ (forceDelayT , (ast13 , ast13)) ∷ (caseOfCaseT , (ast13 , ast13)) ∷ (caseReduceT , (ast13 , ast13)) ∷ (inlineT , (ast13 , ast13)) ∷ (cseT , (ast13 , ast14)) ∷ (floatDelayT , (ast14 , ast14)) ∷ (forceDelayT , (ast14 , ast14)) ∷ (caseOfCaseT , (ast14 , ast14)) ∷ (caseReduceT , (ast14 , ast14)) ∷ (inlineT , (ast14 , ast15)) ∷ (cseT , (ast15 , ast16)) ∷ (floatDelayT , (ast16 , ast16)) ∷ (forceDelayT , (ast16 , ast16)) ∷ (caseOfCaseT , (ast16 , ast16)) ∷ (caseReduceT , (ast16 , ast16)) ∷ (inlineT , (ast16 , ast17)) ∷ (cseT , (ast17 , ast18)) ∷ (floatDelayT , (ast18 , ast18)) ∷ (forceDelayT , (ast18 , ast18)) ∷ (caseOfCaseT , (ast18 , ast18)) ∷ (caseReduceT , (ast18 , ast18)) ∷ (inlineT , (ast18 , ast19)) ∷ (cseT , (ast19 , ast20)) ∷ (floatDelayT , (ast20 , ast20)) ∷ (forceDelayT , (ast20 , ast20)) ∷ (caseOfCaseT , (ast20 , ast20)) ∷ (caseReduceT , (ast20 , ast20)) ∷ (inlineT , (ast20 , ast21)) ∷ [])

certificate : passed? (runCertifier asts) ≡ true
certificate = refl

-- ce' : Maybe (Σ _ \A → (Σ _ \B → (SimplifierTag × A × B)))
-- ce' = getCE (runCertifier asts)
