{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Algebra.Morphism where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Morphism.Definitions._.Homomorphic₀
d_Homomorphic'8320'_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_32 = erased
-- Algebra.Morphism.Definitions._.Homomorphic₁
d_Homomorphic'8321'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_34 = erased
-- Algebra.Morphism.Definitions._.Homomorphic₂
d_Homomorphic'8322'_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_36 = erased
-- Algebra.Morphism.Definitions._.Morphism
d_Morphism_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> ()
d_Morphism_38 = erased
-- Algebra.Morphism._.F._∙_
d__'8729'__58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__58 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8729'__58 v4
du__'8729'__58 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8729'__58 v0
  = coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 (coe v0)
-- Algebra.Morphism._.F._≈_
d__'8776'__60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__60 = erased
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_138 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_140 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_142 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 -> ()
d_Morphism_144 = erased
-- Algebra.Morphism._.IsSemigroupMorphism
d_IsSemigroupMorphism_148 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemigroupMorphism_148
  = C_constructor_160 (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism._.IsSemigroupMorphism.⟦⟧-cong
d_'10214''10215''45'cong_156 ::
  T_IsSemigroupMorphism_148 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_156 v0
  = case coe v0 of
      C_constructor_160 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsSemigroupMorphism.∙-homo
d_'8729''45'homo_158 ::
  T_IsSemigroupMorphism_148 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_158 v0
  = case coe v0 of
      C_constructor_160 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsSemigroupMorphism-syntax
d_IsSemigroupMorphism'45'syntax_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsSemigroupMorphism'45'syntax_162 = erased
-- Algebra.Morphism._.F.semigroup
d_semigroup_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_semigroup_220 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_semigroup_220 v4
du_semigroup_220 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_semigroup_220 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_976 (coe v0)
-- Algebra.Morphism._.F.ε
d_ε_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 -> AgdaAny
d_ε_230 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_ε_230 v4
du_ε_230 :: MAlonzo.Code.Algebra.Bundles.T_Monoid_914 -> AgdaAny
du_ε_230 v0 = coe MAlonzo.Code.Algebra.Bundles.d_ε_936 (coe v0)
-- Algebra.Morphism._.T.semigroup
d_semigroup_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_semigroup_278 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_semigroup_278 v5
du_semigroup_278 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_semigroup_278 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_976 (coe v0)
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_298 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_300 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_302 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 -> ()
d_Morphism_304 = erased
-- Algebra.Morphism._.IsMonoidMorphism
d_IsMonoidMorphism_308 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMonoidMorphism_308
  = C_constructor_326 T_IsSemigroupMorphism_148 AgdaAny
-- Algebra.Morphism._.IsMonoidMorphism.sm-homo
d_sm'45'homo_316 ::
  T_IsMonoidMorphism_308 -> T_IsSemigroupMorphism_148
d_sm'45'homo_316 v0
  = case coe v0 of
      C_constructor_326 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsMonoidMorphism.ε-homo
d_ε'45'homo_318 :: T_IsMonoidMorphism_308 -> AgdaAny
d_ε'45'homo_318 v0
  = case coe v0 of
      C_constructor_326 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsMonoidMorphism._.∙-homo
d_'8729''45'homo_322 ::
  T_IsMonoidMorphism_308 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_322 v0
  = coe d_'8729''45'homo_158 (coe d_sm'45'homo_316 (coe v0))
-- Algebra.Morphism._.IsMonoidMorphism._.⟦⟧-cong
d_'10214''10215''45'cong_324 ::
  T_IsMonoidMorphism_308 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_324 v0
  = coe d_'10214''10215''45'cong_156 (coe d_sm'45'homo_316 (coe v0))
-- Algebra.Morphism._.IsMonoidMorphism-syntax
d_IsMonoidMorphism'45'syntax_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsMonoidMorphism'45'syntax_328 = erased
-- Algebra.Morphism._.F.monoid
d_monoid_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_monoid_390 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_monoid_390 v4
du_monoid_390 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_monoid_390 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1066 (coe v0)
-- Algebra.Morphism._.T.monoid
d_monoid_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_monoid_462 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_monoid_462 v5
du_monoid_462 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_monoid_462 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1066 (coe v0)
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_492 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_494 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_496 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 -> ()
d_Morphism_498 = erased
-- Algebra.Morphism._.IsCommutativeMonoidMorphism
d_IsCommutativeMonoidMorphism_502 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T_IsCommutativeMonoidMorphism_502
  = C_constructor_520 T_IsMonoidMorphism_308
-- Algebra.Morphism._.IsCommutativeMonoidMorphism.mn-homo
d_mn'45'homo_508 ::
  T_IsCommutativeMonoidMorphism_502 -> T_IsMonoidMorphism_308
d_mn'45'homo_508 v0
  = case coe v0 of
      C_constructor_520 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsCommutativeMonoidMorphism._.sm-homo
d_sm'45'homo_512 ::
  T_IsCommutativeMonoidMorphism_502 -> T_IsSemigroupMorphism_148
d_sm'45'homo_512 v0
  = coe d_sm'45'homo_316 (coe d_mn'45'homo_508 (coe v0))
-- Algebra.Morphism._.IsCommutativeMonoidMorphism._.ε-homo
d_ε'45'homo_514 :: T_IsCommutativeMonoidMorphism_502 -> AgdaAny
d_ε'45'homo_514 v0
  = coe d_ε'45'homo_318 (coe d_mn'45'homo_508 (coe v0))
-- Algebra.Morphism._.IsCommutativeMonoidMorphism._.∙-homo
d_'8729''45'homo_516 ::
  T_IsCommutativeMonoidMorphism_502 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_516 v0
  = coe
      d_'8729''45'homo_158
      (coe d_sm'45'homo_316 (coe d_mn'45'homo_508 (coe v0)))
-- Algebra.Morphism._.IsCommutativeMonoidMorphism._.⟦⟧-cong
d_'10214''10215''45'cong_518 ::
  T_IsCommutativeMonoidMorphism_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_518 v0
  = coe
      d_'10214''10215''45'cong_156
      (coe d_sm'45'homo_316 (coe d_mn'45'homo_508 (coe v0)))
-- Algebra.Morphism._.IsCommutativeMonoidMorphism-syntax
d_IsCommutativeMonoidMorphism'45'syntax_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsCommutativeMonoidMorphism'45'syntax_522 = erased
-- Algebra.Morphism._.F.commutativeMonoid
d_commutativeMonoid_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_commutativeMonoid_560 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_commutativeMonoid_560 v4
du_commutativeMonoid_560 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
du_commutativeMonoid_560 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_commutativeMonoid_1266 (coe v0)
-- Algebra.Morphism._.F.monoid
d_monoid_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_monoid_602 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_monoid_602 v4
du_monoid_602 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_monoid_602 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_monoid_1066
      (coe
         MAlonzo.Code.Algebra.Bundles.du_commutativeMonoid_1266 (coe v0))
-- Algebra.Morphism._.T.commutativeMonoid
d_commutativeMonoid_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_commutativeMonoid_650 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_commutativeMonoid_650 v5
du_commutativeMonoid_650 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
du_commutativeMonoid_650 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_commutativeMonoid_1266 (coe v0)
-- Algebra.Morphism._.T.monoid
d_monoid_692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_monoid_692 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_monoid_692 v5
du_monoid_692 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_monoid_692 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_monoid_1066
      (coe
         MAlonzo.Code.Algebra.Bundles.du_commutativeMonoid_1266 (coe v0))
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_722 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_724 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_726 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  ()
d_Morphism_728 = erased
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism
d_IsIdempotentCommutativeMonoidMorphism_732 a0 a1 a2 a3 a4 a5 a6
  = ()
newtype T_IsIdempotentCommutativeMonoidMorphism_732
  = C_constructor_752 T_IsMonoidMorphism_308
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism.mn-homo
d_mn'45'homo_738 ::
  T_IsIdempotentCommutativeMonoidMorphism_732 ->
  T_IsMonoidMorphism_308
d_mn'45'homo_738 v0
  = case coe v0 of
      C_constructor_752 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism._.sm-homo
d_sm'45'homo_742 ::
  T_IsIdempotentCommutativeMonoidMorphism_732 ->
  T_IsSemigroupMorphism_148
d_sm'45'homo_742 v0
  = coe d_sm'45'homo_316 (coe d_mn'45'homo_738 (coe v0))
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism._.ε-homo
d_ε'45'homo_744 ::
  T_IsIdempotentCommutativeMonoidMorphism_732 -> AgdaAny
d_ε'45'homo_744 v0
  = coe d_ε'45'homo_318 (coe d_mn'45'homo_738 (coe v0))
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism._.∙-homo
d_'8729''45'homo_746 ::
  T_IsIdempotentCommutativeMonoidMorphism_732 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_746 v0
  = coe
      d_'8729''45'homo_158
      (coe d_sm'45'homo_316 (coe d_mn'45'homo_738 (coe v0)))
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism._.⟦⟧-cong
d_'10214''10215''45'cong_748 ::
  T_IsIdempotentCommutativeMonoidMorphism_732 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_748 v0
  = coe
      d_'10214''10215''45'cong_156
      (coe d_sm'45'homo_316 (coe d_mn'45'homo_738 (coe v0)))
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism.isCommutativeMonoidMorphism
d_isCommutativeMonoidMorphism_750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  (AgdaAny -> AgdaAny) ->
  T_IsIdempotentCommutativeMonoidMorphism_732 ->
  T_IsCommutativeMonoidMorphism_502
d_isCommutativeMonoidMorphism_750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMonoidMorphism_750 v7
du_isCommutativeMonoidMorphism_750 ::
  T_IsIdempotentCommutativeMonoidMorphism_732 ->
  T_IsCommutativeMonoidMorphism_502
du_isCommutativeMonoidMorphism_750 v0
  = coe C_constructor_520 (coe d_mn'45'homo_738 (coe v0))
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism-syntax
d_IsIdempotentCommutativeMonoidMorphism'45'syntax_754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsIdempotentCommutativeMonoidMorphism'45'syntax_754 = erased
-- Algebra.Morphism._.F._⁻¹
d__'8315''185'_780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 -> AgdaAny -> AgdaAny
d__'8315''185'_780 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8315''185'_780 v4
du__'8315''185'_780 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 -> AgdaAny -> AgdaAny
du__'8315''185'_780 v0
  = coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 (coe v0)
-- Algebra.Morphism._.F.monoid
d_monoid_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_monoid_828 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_monoid_828 v4
du_monoid_828 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_monoid_828 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1656 (coe v0)
-- Algebra.Morphism._.T.monoid
d_monoid_920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_monoid_920 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_monoid_920 v5
du_monoid_920 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_monoid_920 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1656 (coe v0)
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_958 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_960 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_962 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 -> ()
d_Morphism_964 = erased
-- Algebra.Morphism._.IsGroupMorphism
d_IsGroupMorphism_968 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T_IsGroupMorphism_968
  = C_constructor_1030 T_IsMonoidMorphism_308
-- Algebra.Morphism._.IsGroupMorphism.mn-homo
d_mn'45'homo_974 :: T_IsGroupMorphism_968 -> T_IsMonoidMorphism_308
d_mn'45'homo_974 v0
  = case coe v0 of
      C_constructor_1030 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsGroupMorphism._.sm-homo
d_sm'45'homo_978 ::
  T_IsGroupMorphism_968 -> T_IsSemigroupMorphism_148
d_sm'45'homo_978 v0
  = coe d_sm'45'homo_316 (coe d_mn'45'homo_974 (coe v0))
-- Algebra.Morphism._.IsGroupMorphism._.ε-homo
d_ε'45'homo_980 :: T_IsGroupMorphism_968 -> AgdaAny
d_ε'45'homo_980 v0
  = coe d_ε'45'homo_318 (coe d_mn'45'homo_974 (coe v0))
-- Algebra.Morphism._.IsGroupMorphism._.∙-homo
d_'8729''45'homo_982 ::
  T_IsGroupMorphism_968 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_982 v0
  = coe
      d_'8729''45'homo_158
      (coe d_sm'45'homo_316 (coe d_mn'45'homo_974 (coe v0)))
-- Algebra.Morphism._.IsGroupMorphism._.⟦⟧-cong
d_'10214''10215''45'cong_984 ::
  T_IsGroupMorphism_968 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_984 v0
  = coe
      d_'10214''10215''45'cong_156
      (coe d_sm'45'homo_316 (coe d_mn'45'homo_974 (coe v0)))
-- Algebra.Morphism._.IsGroupMorphism.⁻¹-homo
d_'8315''185''45'homo_986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  (AgdaAny -> AgdaAny) -> T_IsGroupMorphism_968 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_986 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_'8315''185''45'homo_986 v4 v5 v6 v7 v8
du_'8315''185''45'homo_986 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  (AgdaAny -> AgdaAny) -> T_IsGroupMorphism_968 -> AgdaAny -> AgdaAny
du_'8315''185''45'homo_986 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1152
      (MAlonzo.Code.Algebra.Bundles.d__'8729'__1586 (coe v1))
      (MAlonzo.Code.Algebra.Bundles.d_ε_1588 (coe v1))
      (MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 (coe v1))
      (MAlonzo.Code.Algebra.Bundles.d_isGroup_1592 (coe v1))
      (coe
         v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 v0 v4))
      (coe v2 v4)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v5 v6 v7 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1586 v1
            (coe
               v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 v0 v4))
            (coe v2 v4))
         (MAlonzo.Code.Algebra.Bundles.d_ε_1588 (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMagma_496
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                              (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1592 (coe v1))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1586 v1
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 v0 v4))
               (coe v2 v4))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1586 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 v0 v4) v4))
            (MAlonzo.Code.Algebra.Bundles.d_ε_1588 (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMagma_496
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                                 (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1592 (coe v1))))))))
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1586 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 v0 v4) v4))
               (coe v2 (MAlonzo.Code.Algebra.Bundles.d_ε_1588 (coe v0)))
               (MAlonzo.Code.Algebra.Bundles.d_ε_1588 (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isMagma_496
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                                    (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1592 (coe v1))))))))
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.d_ε_1588 (coe v0)))
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1588 (coe v1))
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1588 (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isMagma_496
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                                       (coe
                                          MAlonzo.Code.Algebra.Bundles.d_isGroup_1592
                                          (coe v1))))))))
                     (coe MAlonzo.Code.Algebra.Bundles.d_ε_1588 (coe v1)))
                  (d_ε'45'homo_318 (coe d_mn'45'homo_974 (coe v3))))
               (coe
                  d_'10214''10215''45'cong_156
                  (d_sm'45'homo_316 (coe d_mn'45'homo_974 (coe v3)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1586 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 v0 v4) v4)
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1588 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_inverse'737'_1144
                     (MAlonzo.Code.Algebra.Bundles.d_isGroup_1592 (coe v0)) v4)))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_496
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                           (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1592 (coe v1))))))
               (coe
                  v2
                  (let v5
                         = let v5
                                 = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1656 (coe v0) in
                           coe (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_976 (coe v5)) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v5
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 v0 v4) v4)))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__576
                  (let v5
                         = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1656 (coe v1) in
                   coe (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_976 (coe v5)))
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 v0 v4))
                  (coe v2 v4))
               (coe
                  d_'8729''45'homo_158
                  (d_sm'45'homo_316 (coe d_mn'45'homo_974 (coe v3)))
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1590 v0 v4) v4))))
-- Algebra.Morphism._.IsGroupMorphism-syntax
d_IsGroupMorphism'45'syntax_1032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsGroupMorphism'45'syntax_1032 = erased
-- Algebra.Morphism._.F.group
d_group_1074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564
d_group_1074 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_group_1074 v4
du_group_1074 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564
du_group_1074 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_group_1778 (coe v0)
-- Algebra.Morphism._.T.group
d_group_1178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564
d_group_1178 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_group_1178 v5
du_group_1178 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1564
du_group_1178 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_group_1778 (coe v0)
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_1260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_1260 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_1262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_1262 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_1264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_1264 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_1266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 -> ()
d_Morphism_1266 = erased
-- Algebra.Morphism._.IsAbelianGroupMorphism
d_IsAbelianGroupMorphism_1270 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T_IsAbelianGroupMorphism_1270
  = C_constructor_1292 T_IsGroupMorphism_968
-- Algebra.Morphism._.IsAbelianGroupMorphism.gp-homo
d_gp'45'homo_1276 ::
  T_IsAbelianGroupMorphism_1270 -> T_IsGroupMorphism_968
d_gp'45'homo_1276 v0
  = case coe v0 of
      C_constructor_1292 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsAbelianGroupMorphism._.mn-homo
d_mn'45'homo_1280 ::
  T_IsAbelianGroupMorphism_1270 -> T_IsMonoidMorphism_308
d_mn'45'homo_1280 v0
  = coe d_mn'45'homo_974 (coe d_gp'45'homo_1276 (coe v0))
-- Algebra.Morphism._.IsAbelianGroupMorphism._.sm-homo
d_sm'45'homo_1282 ::
  T_IsAbelianGroupMorphism_1270 -> T_IsSemigroupMorphism_148
d_sm'45'homo_1282 v0
  = coe
      d_sm'45'homo_316
      (coe d_mn'45'homo_974 (coe d_gp'45'homo_1276 (coe v0)))
-- Algebra.Morphism._.IsAbelianGroupMorphism._.ε-homo
d_ε'45'homo_1284 :: T_IsAbelianGroupMorphism_1270 -> AgdaAny
d_ε'45'homo_1284 v0
  = coe
      d_ε'45'homo_318
      (coe d_mn'45'homo_974 (coe d_gp'45'homo_1276 (coe v0)))
-- Algebra.Morphism._.IsAbelianGroupMorphism._.⁻¹-homo
d_'8315''185''45'homo_1286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroupMorphism_1270 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1286 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8315''185''45'homo_1286 v4 v5 v6 v7
du_'8315''185''45'homo_1286 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroupMorphism_1270 -> AgdaAny -> AgdaAny
du_'8315''185''45'homo_1286 v0 v1 v2 v3
  = coe
      du_'8315''185''45'homo_986
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1778 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1778 (coe v1)) (coe v2)
      (coe d_gp'45'homo_1276 (coe v3))
-- Algebra.Morphism._.IsAbelianGroupMorphism._.∙-homo
d_'8729''45'homo_1288 ::
  T_IsAbelianGroupMorphism_1270 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_1288 v0
  = coe
      d_'8729''45'homo_158
      (coe
         d_sm'45'homo_316
         (coe d_mn'45'homo_974 (coe d_gp'45'homo_1276 (coe v0))))
-- Algebra.Morphism._.IsAbelianGroupMorphism._.⟦⟧-cong
d_'10214''10215''45'cong_1290 ::
  T_IsAbelianGroupMorphism_1270 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_1290 v0
  = coe
      d_'10214''10215''45'cong_156
      (coe
         d_sm'45'homo_316
         (coe d_mn'45'homo_974 (coe d_gp'45'homo_1276 (coe v0))))
-- Algebra.Morphism._.IsAbelianGroupMorphism-syntax
d_IsAbelianGroupMorphism'45'syntax_1294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsAbelianGroupMorphism'45'syntax_1294 = erased
-- Algebra.Morphism._.F.*-monoid
d_'42''45'monoid_1346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'42''45'monoid_1346 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_'42''45'monoid_1346 v4
du_'42''45'monoid_1346 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_'42''45'monoid_1346 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_semiring_4060 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2338
         (coe
            MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2474
            (coe v1)))
-- Algebra.Morphism._.F.+-abelianGroup
d_'43''45'abelianGroup_1354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682
d_'43''45'abelianGroup_1354 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_'43''45'abelianGroup_1354 v4
du_'43''45'abelianGroup_1354 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682
du_'43''45'abelianGroup_1354 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_4056 (coe v0)
-- Algebra.Morphism._.T.*-monoid
d_'42''45'monoid_1528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'42''45'monoid_1528 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'monoid_1528 v5
du_'42''45'monoid_1528 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_'42''45'monoid_1528 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_semiring_4060 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2338
         (coe
            MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2474
            (coe v1)))
-- Algebra.Morphism._.T.+-abelianGroup
d_'43''45'abelianGroup_1536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682
d_'43''45'abelianGroup_1536 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'43''45'abelianGroup_1536 v5
du_'43''45'abelianGroup_1536 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682
du_'43''45'abelianGroup_1536 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_4056 (coe v0)
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_1678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_1678 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_1680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_1680 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_1682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_1682 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_1684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 -> ()
d_Morphism_1684 = erased
-- Algebra.Morphism._.IsRingMorphism
d_IsRingMorphism_1688 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingMorphism_1688
  = C_constructor_1700 T_IsAbelianGroupMorphism_1270
                       T_IsMonoidMorphism_308
-- Algebra.Morphism._.IsRingMorphism.+-abgp-homo
d_'43''45'abgp'45'homo_1696 ::
  T_IsRingMorphism_1688 -> T_IsAbelianGroupMorphism_1270
d_'43''45'abgp'45'homo_1696 v0
  = case coe v0 of
      C_constructor_1700 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsRingMorphism.*-mn-homo
d_'42''45'mn'45'homo_1698 ::
  T_IsRingMorphism_1688 -> T_IsMonoidMorphism_308
d_'42''45'mn'45'homo_1698 v0
  = case coe v0 of
      C_constructor_1700 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsRingMorphism-syntax
d_IsRingMorphism'45'syntax_1702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsRingMorphism'45'syntax_1702 = erased
