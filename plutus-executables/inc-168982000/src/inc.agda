module inc where

open import Certifier
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
open import Agda.Builtin.List using (_∷_; [])
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



asts : List (SimplifierTag × Hints × Untyped × Untyped)
asts = ((floatDelayT , (none , (ast0 , ast1))) ∷ (forceCaseDelayT , (none , (ast1 , ast1))) ∷ (forceDelayT , (none , (ast1 , ast2))) ∷ (caseOfCaseT , (none , (ast2 , ast2))) ∷ (caseReduceT , (none , (ast2 , ast2))) ∷ (inlineT , (inline (((ƛ↓ (expand (ƛ ((ƛ↓ ((((force ((ƛ↓ (expand (delay (ƛ var)))) ·↓)) · ((ƛ↓ ((ƛ↓ ((ƛ↓ (force (expand (delay (expand (ƛ ((ƛ↓ (ƛ ((ƛ↓ (((expand builtin) · (expand var)) · (expand var))) ·↓))) ·↓))))))) ·↓)) ·↓)) ·↓)) · con) · (expand var))) ·↓)))) ·↓)) , (ast2 , ast3))) ∷ (floatDelayT , (none , (ast3 , ast3))) ∷ (forceCaseDelayT , (none , (ast3 , ast3))) ∷ (forceDelayT , (none , (ast3 , ast4))) ∷ (caseOfCaseT , (none , (ast4 , ast4))) ∷ (caseReduceT , (none , (ast4 , ast4))) ∷ (inlineT , (inline ((ƛ ((((ƛ↓ (expand (ƛ (ƛ ((builtin · var) · var))))) ·↓) · con) · var))) , (ast4 , ast5))) ∷ (floatDelayT , (none , (ast5 , ast5))) ∷ (forceCaseDelayT , (none , (ast5 , ast5))) ∷ (forceDelayT , (none , (ast5 , ast5))) ∷ (caseOfCaseT , (none , (ast5 , ast5))) ∷ (caseReduceT , (none , (ast5 , ast5))) ∷ (inlineT , (inline ((ƛ (((ƛ↓ (ƛ↓ ((builtin · (expand con)) · (expand var)))) ·↓) ·↓))) , (ast5 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (cseT , (none , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (cseT , (none , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (cseT , (none , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (cseT , (none , (ast6 , ast6))) ∷ (floatDelayT , (none , (ast6 , ast6))) ∷ (forceCaseDelayT , (none , (ast6 , ast6))) ∷ (forceDelayT , (none , (ast6 , ast6))) ∷ (caseOfCaseT , (none , (ast6 , ast6))) ∷ (caseReduceT , (none , (ast6 , ast6))) ∷ (inlineT , (inline ((ƛ ((builtin · con) · var))) , (ast6 , ast6))) ∷ (applyToCaseT , (none , (ast6 , ast6))) ∷ [])

certificate : passed? (runCertifier asts) ≡ true
certificate = refl
