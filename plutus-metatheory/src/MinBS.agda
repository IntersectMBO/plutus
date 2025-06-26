module MinBS where

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

before : (SimplifierTag × Untyped × Untyped)
before = (floatDelayT , ((UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-256) (UCon (tagCon bytestring (Utils.encodeUtf8 "uh"))))) , (UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-256) (UCon (tagCon bytestring (Utils.encodeUtf8 "uh")))))))

after : (SimplifierTag × Untyped × Untyped)
after = (forceDelayT , ((UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-256) (UCon (tagCon bytestring (Utils.encodeUtf8 "uh"))))) , (UApp (UBuiltin equalsByteString) (UApp (UBuiltin blake2b-256) (UCon (tagCon bytestring (Utils.encodeUtf8 "uh")))))))

asts : List (SimplifierTag × Untyped × Untyped)
asts = (before ∷ after ∷ [])
