module Declarative.test.StringLiteral where

open import Type
open import Declarative.Term
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆

-- plutus/language-plutus-core/test/data/stringLiteral.plc

postulate str1 : ByteString
{-# FOREIGN GHC import qualified Data.ByteString.Lazy.Char8 as BS #-}
{-# COMPILE GHC str1 = BS.pack "4321758fabce1aa4780193f" #-}

open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.TrustMe

lemma1 : length str1 ≡ 23
lemma1 = primTrustMe

open import Data.Nat

lemma1' : BoundedB 100 str1
lemma1' rewrite lemma1 = gen _ _ _

stringLit : ∀{Γ} → Γ ⊢ con bytestring (size⋆ 100)
stringLit = con (bytestring 100  str1 lemma1')
