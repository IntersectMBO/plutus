-- from /home/ana/Workspace/IOG/plutus/agda-certificates/plutus_benchmark_PlutusBenchmark_Ed25519_Compiled-i6fvxr.agda-cert

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS -v tc.reduce:110 #-}

module Testing.Proof where

import Testing.AST0
import Testing.AST1
open import Data.Unit using (tt)
open import VerifiedCompilation
open import VerifiedCompilation.Trace
open import VerifiedCompilation.Certificate
open import Utils

-- to-witness-T

-- x : _
-- x = certifyPass (inj₂ forceCaseDelayT) Testing.AST0.hints Testing.AST0.ast Testing.AST1.ast 
-- 
-- import Data.Bool.Base using (T)
-- 
-- y : Data.Bool.Base.T (is-proof x) → RelationOf (inj₂ forceCaseDelayT) Testing.AST0.ast Testing.AST1.ast
-- y = to-witness-T x
-- 
-- related : RelationOf (inj₂ forceCaseDelayT) Testing.AST0.ast Testing.AST1.ast
-- related = y tt

relatedBAD : RelationOf (inj₂ forceCaseDelayT) Testing.AST0.ast Testing.AST1.ast
relatedBAD = {!   !} -- to-witness-T (certifyPass (inj₂ forceCaseDelayT) Testing.AST0.hints Testing.AST0.ast Testing.AST1.ast) tt

open import Untyped using (_⊢)
open import RawU
open import Data.Bool
import Data.Maybe

fooRaw : Untyped
fooRaw = UCon (tagCon bool true)

foo : 0 ⊢
foo = Data.Maybe.to-witness-T (checkScope fooRaw) tt

relatedGOOD : RelationOf (inj₂ forceCaseDelayT) foo foo
relatedGOOD = to-witness-T (certifyPass (inj₂ forceCaseDelayT) Testing.AST0.hints foo foo) tt


-- open import Data.Nat using (ℕ)
-- open import Relation.Binary.PropositionalEquality using (refl; _≡_)
-- 
-- opaque
--   f : ℕ
--   f = 0
-- 
-- opaque
--   unfolding f
-- 
--   p : f ≡ 0
--   p = refl
