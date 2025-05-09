{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Algebra.Morphism where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Single qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__58 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8729'__58 v4
du__'8729'__58 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8729'__58 v0
  = coe MAlonzo.Code.Algebra.Bundles.d__'8729'__554 (coe v0)
-- Algebra.Morphism._.F._≈_
d__'8776'__60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__60 = erased
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_138 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_140 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
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
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 -> ()
d_Morphism_144 = erased
-- Algebra.Morphism._.IsSemigroupMorphism
d_IsSemigroupMorphism_148 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemigroupMorphism_148
  = C_IsSemigroupMorphism'46'constructor_1081 (AgdaAny ->
                                               AgdaAny -> AgdaAny -> AgdaAny)
                                              (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Morphism._.IsSemigroupMorphism.⟦⟧-cong
d_'10214''10215''45'cong_156 ::
  T_IsSemigroupMorphism_148 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_156 v0
  = case coe v0 of
      C_IsSemigroupMorphism'46'constructor_1081 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsSemigroupMorphism.∙-homo
d_'8729''45'homo_158 ::
  T_IsSemigroupMorphism_148 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_158 v0
  = case coe v0 of
      C_IsSemigroupMorphism'46'constructor_1081 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsSemigroupMorphism-syntax
d_IsSemigroupMorphism'45'syntax_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsSemigroupMorphism'45'syntax_160 = erased
-- Algebra.Morphism._.F.semigroup
d_semigroup_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_semigroup_218 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_semigroup_218 v4
du_semigroup_218 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_semigroup_218 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_944 (coe v0)
-- Algebra.Morphism._.F.ε
d_ε_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 -> AgdaAny
d_ε_228 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_ε_228 v4
du_ε_228 :: MAlonzo.Code.Algebra.Bundles.T_Monoid_882 -> AgdaAny
du_ε_228 v0 = coe MAlonzo.Code.Algebra.Bundles.d_ε_904 (coe v0)
-- Algebra.Morphism._.T.semigroup
d_semigroup_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_semigroup_276 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_semigroup_276 v5
du_semigroup_276 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_semigroup_276 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_944 (coe v0)
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_296 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_298 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_300 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 -> ()
d_Morphism_302 = erased
-- Algebra.Morphism._.IsMonoidMorphism
d_IsMonoidMorphism_306 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMonoidMorphism_306
  = C_IsMonoidMorphism'46'constructor_2139 T_IsSemigroupMorphism_148
                                           AgdaAny
-- Algebra.Morphism._.IsMonoidMorphism.sm-homo
d_sm'45'homo_314 ::
  T_IsMonoidMorphism_306 -> T_IsSemigroupMorphism_148
d_sm'45'homo_314 v0
  = case coe v0 of
      C_IsMonoidMorphism'46'constructor_2139 v1 v2 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsMonoidMorphism.ε-homo
d_ε'45'homo_316 :: T_IsMonoidMorphism_306 -> AgdaAny
d_ε'45'homo_316 v0
  = case coe v0 of
      C_IsMonoidMorphism'46'constructor_2139 v1 v2 -> coe v2
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsMonoidMorphism._.∙-homo
d_'8729''45'homo_320 ::
  T_IsMonoidMorphism_306 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_320 v0
  = coe d_'8729''45'homo_158 (coe d_sm'45'homo_314 (coe v0))
-- Algebra.Morphism._.IsMonoidMorphism._.⟦⟧-cong
d_'10214''10215''45'cong_322 ::
  T_IsMonoidMorphism_306 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_322 v0
  = coe d_'10214''10215''45'cong_156 (coe d_sm'45'homo_314 (coe v0))
-- Algebra.Morphism._.IsMonoidMorphism-syntax
d_IsMonoidMorphism'45'syntax_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsMonoidMorphism'45'syntax_324 = erased
-- Algebra.Morphism._.F.monoid
d_monoid_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_monoid_386 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_monoid_386 v4
du_monoid_386 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_monoid_386 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1032 (coe v0)
-- Algebra.Morphism._.T.monoid
d_monoid_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_monoid_458 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_monoid_458 v5
du_monoid_458 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_monoid_458 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1032 (coe v0)
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_488 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_490 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_492 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 -> ()
d_Morphism_494 = erased
-- Algebra.Morphism._.IsCommutativeMonoidMorphism
d_IsCommutativeMonoidMorphism_498 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T_IsCommutativeMonoidMorphism_498
  = C_IsCommutativeMonoidMorphism'46'constructor_3705 T_IsMonoidMorphism_306
-- Algebra.Morphism._.IsCommutativeMonoidMorphism.mn-homo
d_mn'45'homo_504 ::
  T_IsCommutativeMonoidMorphism_498 -> T_IsMonoidMorphism_306
d_mn'45'homo_504 v0
  = case coe v0 of
      C_IsCommutativeMonoidMorphism'46'constructor_3705 v1 -> coe v1
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsCommutativeMonoidMorphism._.sm-homo
d_sm'45'homo_508 ::
  T_IsCommutativeMonoidMorphism_498 -> T_IsSemigroupMorphism_148
d_sm'45'homo_508 v0
  = coe d_sm'45'homo_314 (coe d_mn'45'homo_504 (coe v0))
-- Algebra.Morphism._.IsCommutativeMonoidMorphism._.ε-homo
d_ε'45'homo_510 :: T_IsCommutativeMonoidMorphism_498 -> AgdaAny
d_ε'45'homo_510 v0
  = coe d_ε'45'homo_316 (coe d_mn'45'homo_504 (coe v0))
-- Algebra.Morphism._.IsCommutativeMonoidMorphism._.∙-homo
d_'8729''45'homo_512 ::
  T_IsCommutativeMonoidMorphism_498 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_512 v0
  = coe
      d_'8729''45'homo_158
      (coe d_sm'45'homo_314 (coe d_mn'45'homo_504 (coe v0)))
-- Algebra.Morphism._.IsCommutativeMonoidMorphism._.⟦⟧-cong
d_'10214''10215''45'cong_514 ::
  T_IsCommutativeMonoidMorphism_498 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_514 v0
  = coe
      d_'10214''10215''45'cong_156
      (coe d_sm'45'homo_314 (coe d_mn'45'homo_504 (coe v0)))
-- Algebra.Morphism._.IsCommutativeMonoidMorphism-syntax
d_IsCommutativeMonoidMorphism'45'syntax_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsCommutativeMonoidMorphism'45'syntax_516 = erased
-- Algebra.Morphism._.F.commutativeMonoid
d_commutativeMonoid_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_commutativeMonoid_554 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_commutativeMonoid_554 v4
du_commutativeMonoid_554 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
du_commutativeMonoid_554 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_commutativeMonoid_1228 (coe v0)
-- Algebra.Morphism._.F.monoid
d_monoid_596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_monoid_596 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_monoid_596 v4
du_monoid_596 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_monoid_596 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_monoid_1032
      (coe
         MAlonzo.Code.Algebra.Bundles.du_commutativeMonoid_1228 (coe v0))
-- Algebra.Morphism._.T.commutativeMonoid
d_commutativeMonoid_644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_commutativeMonoid_644 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_commutativeMonoid_644 v5
du_commutativeMonoid_644 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
du_commutativeMonoid_644 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_commutativeMonoid_1228 (coe v0)
-- Algebra.Morphism._.T.monoid
d_monoid_686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_monoid_686 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_monoid_686 v5
du_monoid_686 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_monoid_686 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_monoid_1032
      (coe
         MAlonzo.Code.Algebra.Bundles.du_commutativeMonoid_1228 (coe v0))
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_716 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_718 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_718 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_720 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  ()
d_Morphism_722 = erased
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism
d_IsIdempotentCommutativeMonoidMorphism_726 a0 a1 a2 a3 a4 a5 a6
  = ()
newtype T_IsIdempotentCommutativeMonoidMorphism_726
  = C_IsIdempotentCommutativeMonoidMorphism'46'constructor_5361 T_IsMonoidMorphism_306
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism.mn-homo
d_mn'45'homo_732 ::
  T_IsIdempotentCommutativeMonoidMorphism_726 ->
  T_IsMonoidMorphism_306
d_mn'45'homo_732 v0
  = case coe v0 of
      C_IsIdempotentCommutativeMonoidMorphism'46'constructor_5361 v1
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism._.sm-homo
d_sm'45'homo_736 ::
  T_IsIdempotentCommutativeMonoidMorphism_726 ->
  T_IsSemigroupMorphism_148
d_sm'45'homo_736 v0
  = coe d_sm'45'homo_314 (coe d_mn'45'homo_732 (coe v0))
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism._.ε-homo
d_ε'45'homo_738 ::
  T_IsIdempotentCommutativeMonoidMorphism_726 -> AgdaAny
d_ε'45'homo_738 v0
  = coe d_ε'45'homo_316 (coe d_mn'45'homo_732 (coe v0))
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism._.∙-homo
d_'8729''45'homo_740 ::
  T_IsIdempotentCommutativeMonoidMorphism_726 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_740 v0
  = coe
      d_'8729''45'homo_158
      (coe d_sm'45'homo_314 (coe d_mn'45'homo_732 (coe v0)))
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism._.⟦⟧-cong
d_'10214''10215''45'cong_742 ::
  T_IsIdempotentCommutativeMonoidMorphism_726 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_742 v0
  = coe
      d_'10214''10215''45'cong_156
      (coe d_sm'45'homo_314 (coe d_mn'45'homo_732 (coe v0)))
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism.isCommutativeMonoidMorphism
d_isCommutativeMonoidMorphism_744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  (AgdaAny -> AgdaAny) ->
  T_IsIdempotentCommutativeMonoidMorphism_726 ->
  T_IsCommutativeMonoidMorphism_498
d_isCommutativeMonoidMorphism_744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMonoidMorphism_744 v7
du_isCommutativeMonoidMorphism_744 ::
  T_IsIdempotentCommutativeMonoidMorphism_726 ->
  T_IsCommutativeMonoidMorphism_498
du_isCommutativeMonoidMorphism_744 v0
  = coe
      C_IsCommutativeMonoidMorphism'46'constructor_3705
      (coe d_mn'45'homo_732 (coe v0))
-- Algebra.Morphism._.IsIdempotentCommutativeMonoidMorphism-syntax
d_IsIdempotentCommutativeMonoidMorphism'45'syntax_746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1148 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsIdempotentCommutativeMonoidMorphism'45'syntax_746 = erased
-- Algebra.Morphism._.F._⁻¹
d__'8315''185'_772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 -> AgdaAny -> AgdaAny
d__'8315''185'_772 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8315''185'_772 v4
du__'8315''185'_772 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 -> AgdaAny -> AgdaAny
du__'8315''185'_772 v0
  = coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v0)
-- Algebra.Morphism._.F.monoid
d_monoid_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_monoid_820 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_monoid_820 v4
du_monoid_820 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_monoid_820 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1612 (coe v0)
-- Algebra.Morphism._.T.monoid
d_monoid_912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_monoid_912 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_monoid_912 v5
du_monoid_912 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_monoid_912 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1612 (coe v0)
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_950 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_952 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_954 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 -> ()
d_Morphism_956 = erased
-- Algebra.Morphism._.IsGroupMorphism
d_IsGroupMorphism_960 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T_IsGroupMorphism_960
  = C_IsGroupMorphism'46'constructor_7465 T_IsMonoidMorphism_306
-- Algebra.Morphism._.IsGroupMorphism.mn-homo
d_mn'45'homo_966 :: T_IsGroupMorphism_960 -> T_IsMonoidMorphism_306
d_mn'45'homo_966 v0
  = case coe v0 of
      C_IsGroupMorphism'46'constructor_7465 v1 -> coe v1
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsGroupMorphism._.sm-homo
d_sm'45'homo_970 ::
  T_IsGroupMorphism_960 -> T_IsSemigroupMorphism_148
d_sm'45'homo_970 v0
  = coe d_sm'45'homo_314 (coe d_mn'45'homo_966 (coe v0))
-- Algebra.Morphism._.IsGroupMorphism._.ε-homo
d_ε'45'homo_972 :: T_IsGroupMorphism_960 -> AgdaAny
d_ε'45'homo_972 v0
  = coe d_ε'45'homo_316 (coe d_mn'45'homo_966 (coe v0))
-- Algebra.Morphism._.IsGroupMorphism._.∙-homo
d_'8729''45'homo_974 ::
  T_IsGroupMorphism_960 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_974 v0
  = coe
      d_'8729''45'homo_158
      (coe d_sm'45'homo_314 (coe d_mn'45'homo_966 (coe v0)))
-- Algebra.Morphism._.IsGroupMorphism._.⟦⟧-cong
d_'10214''10215''45'cong_976 ::
  T_IsGroupMorphism_960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_976 v0
  = coe
      d_'10214''10215''45'cong_156
      (coe d_sm'45'homo_314 (coe d_mn'45'homo_966 (coe v0)))
-- Algebra.Morphism._.IsGroupMorphism.⁻¹-homo
d_'8315''185''45'homo_978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny) -> T_IsGroupMorphism_960 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_978 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_'8315''185''45'homo_978 v4 v5 v6 v7 v8
du_'8315''185''45'homo_978 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny) -> T_IsGroupMorphism_960 -> AgdaAny -> AgdaAny
du_'8315''185''45'homo_978 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1114
      (MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 (coe v1))
      (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v1))
      (MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 (coe v1))
      (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v1))
      (coe
         v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v4))
      (coe v2 v4)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v5 v6 v7 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v1
            (coe
               v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v4))
            (coe v2 v4))
         (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v1) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v6) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v7)))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v1
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v4))
               (coe v2 v4))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v4) v4))
            (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v5 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v1) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v5) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v6) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                       (coe v7)))))))))
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v4) v4))
               (coe v2 (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)))
               (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v5 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v1) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v5) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                            (coe v6) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v7)))))))))
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0)))
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v1))
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v1))
                  (let v5
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v5 = MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v1) in
                                 coe
                                   (let v6
                                          = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                                              (coe v5) in
                                    coe
                                      (let v7
                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                                 (coe v6) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                               (coe v7))))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v5))
                        (coe MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v1))))
                  (d_ε'45'homo_316 (coe d_mn'45'homo_966 (coe v3))))
               (coe
                  d_'10214''10215''45'cong_156
                  (d_sm'45'homo_314 (coe d_mn'45'homo_966 (coe v3)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1542 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v4) v4)
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1544 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_inverse'737'_1106
                     (MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v0)) v4)))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_480
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                           (coe MAlonzo.Code.Algebra.Bundles.d_isGroup_1548 (coe v1))))))
               (coe
                  v2
                  (let v5
                         = let v5
                                 = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1612 (coe v0) in
                           coe (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_944 (coe v5)) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v5
                        (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v4) v4)))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__554
                  (let v5
                         = coe MAlonzo.Code.Algebra.Bundles.du_monoid_1612 (coe v1) in
                   coe (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_944 (coe v5)))
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v4))
                  (coe v2 v4))
               (coe
                  d_'8729''45'homo_158
                  (d_sm'45'homo_314 (coe d_mn'45'homo_966 (coe v3)))
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1546 v0 v4) v4))))
-- Algebra.Morphism._.IsGroupMorphism-syntax
d_IsGroupMorphism'45'syntax_1022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsGroupMorphism'45'syntax_1022 = erased
-- Algebra.Morphism._.F.group
d_group_1064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520
d_group_1064 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_group_1064 v4
du_group_1064 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520
du_group_1064 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0)
-- Algebra.Morphism._.T.group
d_group_1168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520
d_group_1168 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_group_1168 v5
du_group_1168 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_Group_1520
du_group_1168 v0
  = coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0)
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_1250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_1250 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_1252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_1252 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_1254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_1254 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_1256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 -> ()
d_Morphism_1256 = erased
-- Algebra.Morphism._.IsAbelianGroupMorphism
d_IsAbelianGroupMorphism_1260 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T_IsAbelianGroupMorphism_1260
  = C_IsAbelianGroupMorphism'46'constructor_11939 T_IsGroupMorphism_960
-- Algebra.Morphism._.IsAbelianGroupMorphism.gp-homo
d_gp'45'homo_1266 ::
  T_IsAbelianGroupMorphism_1260 -> T_IsGroupMorphism_960
d_gp'45'homo_1266 v0
  = case coe v0 of
      C_IsAbelianGroupMorphism'46'constructor_11939 v1 -> coe v1
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsAbelianGroupMorphism._.mn-homo
d_mn'45'homo_1270 ::
  T_IsAbelianGroupMorphism_1260 -> T_IsMonoidMorphism_306
d_mn'45'homo_1270 v0
  = coe d_mn'45'homo_966 (coe d_gp'45'homo_1266 (coe v0))
-- Algebra.Morphism._.IsAbelianGroupMorphism._.sm-homo
d_sm'45'homo_1272 ::
  T_IsAbelianGroupMorphism_1260 -> T_IsSemigroupMorphism_148
d_sm'45'homo_1272 v0
  = coe
      d_sm'45'homo_314
      (coe d_mn'45'homo_966 (coe d_gp'45'homo_1266 (coe v0)))
-- Algebra.Morphism._.IsAbelianGroupMorphism._.ε-homo
d_ε'45'homo_1274 :: T_IsAbelianGroupMorphism_1260 -> AgdaAny
d_ε'45'homo_1274 v0
  = coe
      d_ε'45'homo_316
      (coe d_mn'45'homo_966 (coe d_gp'45'homo_1266 (coe v0)))
-- Algebra.Morphism._.IsAbelianGroupMorphism._.⁻¹-homo
d_'8315''185''45'homo_1276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroupMorphism_1260 -> AgdaAny -> AgdaAny
d_'8315''185''45'homo_1276 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8315''185''45'homo_1276 v4 v5 v6 v7
du_'8315''185''45'homo_1276 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  (AgdaAny -> AgdaAny) ->
  T_IsAbelianGroupMorphism_1260 -> AgdaAny -> AgdaAny
du_'8315''185''45'homo_1276 v0 v1 v2 v3
  = coe
      du_'8315''185''45'homo_978
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v1)) (coe v2)
      (coe d_gp'45'homo_1266 (coe v3))
-- Algebra.Morphism._.IsAbelianGroupMorphism._.∙-homo
d_'8729''45'homo_1278 ::
  T_IsAbelianGroupMorphism_1260 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'homo_1278 v0
  = coe
      d_'8729''45'homo_158
      (coe
         d_sm'45'homo_314
         (coe d_mn'45'homo_966 (coe d_gp'45'homo_1266 (coe v0))))
-- Algebra.Morphism._.IsAbelianGroupMorphism._.⟦⟧-cong
d_'10214''10215''45'cong_1280 ::
  T_IsAbelianGroupMorphism_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'10214''10215''45'cong_1280 v0
  = coe
      d_'10214''10215''45'cong_156
      (coe
         d_sm'45'homo_314
         (coe d_mn'45'homo_966 (coe d_gp'45'homo_1266 (coe v0))))
-- Algebra.Morphism._.IsAbelianGroupMorphism-syntax
d_IsAbelianGroupMorphism'45'syntax_1282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsAbelianGroupMorphism'45'syntax_1282 = erased
-- Algebra.Morphism._.F.*-monoid
d_'42''45'monoid_1334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'42''45'monoid_1334 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_'42''45'monoid_1334 v4
du_'42''45'monoid_1334 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'42''45'monoid_1334 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_semiring_3952 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2264
         (coe
            MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2398
            (coe v1)))
-- Algebra.Morphism._.F.+-abelianGroup
d_'43''45'abelianGroup_1342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636
d_'43''45'abelianGroup_1342 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_'43''45'abelianGroup_1342 v4
du_'43''45'abelianGroup_1342 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636
du_'43''45'abelianGroup_1342 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3948 (coe v0)
-- Algebra.Morphism._.T.*-monoid
d_'42''45'monoid_1516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'42''45'monoid_1516 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'monoid_1516 v5
du_'42''45'monoid_1516 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'42''45'monoid_1516 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_semiring_3952 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_'42''45'monoid_2264
         (coe
            MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2398
            (coe v1)))
-- Algebra.Morphism._.T.+-abelianGroup
d_'43''45'abelianGroup_1524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636
d_'43''45'abelianGroup_1524 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'43''45'abelianGroup_1524 v5
du_'43''45'abelianGroup_1524 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636
du_'43''45'abelianGroup_1524 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3948 (coe v0)
-- Algebra.Morphism._._.Homomorphic₀
d_Homomorphic'8320'_1666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> ()
d_Homomorphic'8320'_1666 = erased
-- Algebra.Morphism._._.Homomorphic₁
d_Homomorphic'8321'_1668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8321'_1668 = erased
-- Algebra.Morphism._._.Homomorphic₂
d_Homomorphic'8322'_1670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Homomorphic'8322'_1670 = erased
-- Algebra.Morphism._._.Morphism
d_Morphism_1672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 -> ()
d_Morphism_1672 = erased
-- Algebra.Morphism._.IsRingMorphism
d_IsRingMorphism_1676 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsRingMorphism_1676
  = C_IsRingMorphism'46'constructor_13939 T_IsAbelianGroupMorphism_1260
                                          T_IsMonoidMorphism_306
-- Algebra.Morphism._.IsRingMorphism.+-abgp-homo
d_'43''45'abgp'45'homo_1684 ::
  T_IsRingMorphism_1676 -> T_IsAbelianGroupMorphism_1260
d_'43''45'abgp'45'homo_1684 v0
  = case coe v0 of
      C_IsRingMorphism'46'constructor_13939 v1 v2 -> coe v1
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsRingMorphism.*-mn-homo
d_'42''45'mn'45'homo_1686 ::
  T_IsRingMorphism_1676 -> T_IsMonoidMorphism_306
d_'42''45'mn'45'homo_1686 v0
  = case coe v0 of
      C_IsRingMorphism'46'constructor_13939 v1 v2 -> coe v2
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Morphism._.IsRingMorphism-syntax
d_IsRingMorphism'45'syntax_1688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800 ->
  (AgdaAny -> AgdaAny) -> ()
d_IsRingMorphism'45'syntax_1688 = erased
