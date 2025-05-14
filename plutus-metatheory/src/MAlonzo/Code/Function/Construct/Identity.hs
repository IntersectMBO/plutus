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

module MAlonzo.Code.Function.Construct.Identity where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Construct.Identity._.congruent
d_congruent_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_congruent_22 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_congruent_22 v6
du_congruent_22 :: AgdaAny -> AgdaAny
du_congruent_22 v0 = coe v0
-- Function.Construct.Identity._.injective
d_injective_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_24 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_injective_24 v6
du_injective_24 :: AgdaAny -> AgdaAny
du_injective_24 v0 = coe v0
-- Function.Construct.Identity._.surjective
d_surjective_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_26 ~v0 ~v1 ~v2 ~v3 v4 = du_surjective_26 v4
du_surjective_26 ::
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_surjective_26 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
      (coe (\ v1 v2 -> v2))
-- Function.Construct.Identity._.bijective
d_bijective_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bijective_30 ~v0 ~v1 ~v2 ~v3 = du_bijective_30
du_bijective_30 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bijective_30
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 -> v2)) (coe du_surjective_26)
-- Function.Construct.Identity._.inverseˡ
d_inverse'737'_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_32 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_inverse'737'_32 v6
du_inverse'737'_32 :: AgdaAny -> AgdaAny
du_inverse'737'_32 v0 = coe v0
-- Function.Construct.Identity._.inverseʳ
d_inverse'691'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_34 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_inverse'691'_34 v6
du_inverse'691'_34 :: AgdaAny -> AgdaAny
du_inverse'691'_34 v0 = coe v0
-- Function.Construct.Identity._.inverseᵇ
d_inverse'7495'_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse'7495'_36 ~v0 ~v1 ~v2 ~v3 = du_inverse'7495'_36
du_inverse'7495'_36 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse'7495'_36
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 -> v2)) (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._._.IsBijection
d_IsBijection_56 a0 a1 a2 a3 a4 a5 = ()
-- Function.Construct.Identity._._.IsCongruent
d_IsCongruent_58 a0 a1 a2 a3 a4 a5 = ()
-- Function.Construct.Identity._._.IsInjection
d_IsInjection_60 a0 a1 a2 a3 a4 a5 = ()
-- Function.Construct.Identity._._.IsInverse
d_IsInverse_62 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Construct.Identity._._.IsLeftInverse
d_IsLeftInverse_64 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Construct.Identity._._.IsRightInverse
d_IsRightInverse_66 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Construct.Identity._._.IsSurjection
d_IsSurjection_70 a0 a1 a2 a3 a4 a5 = ()
-- Function.Construct.Identity._._.IsBijection.isInjection
d_isInjection_214 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
d_isInjection_214 v0
  = coe MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0)
-- Function.Construct.Identity._._.IsBijection.surjective
d_surjective_220 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_220 v0
  = coe MAlonzo.Code.Function.Structures.d_surjective_248 (coe v0)
-- Function.Construct.Identity._._.IsCongruent.cong
d_cong_272 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_272 v0
  = coe MAlonzo.Code.Function.Structures.d_cong_32 (coe v0)
-- Function.Construct.Identity._._.IsCongruent.isEquivalence₁
d_isEquivalence'8321'_274 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_274 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0)
-- Function.Construct.Identity._._.IsCongruent.isEquivalence₂
d_isEquivalence'8322'_276 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_276 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0)
-- Function.Construct.Identity._._.IsInjection.injective
d_injective_330 ::
  MAlonzo.Code.Function.Structures.T_IsInjection_92 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_330 v0
  = coe MAlonzo.Code.Function.Structures.d_injective_102 (coe v0)
-- Function.Construct.Identity._._.IsInjection.isCongruent
d_isCongruent_332 ::
  MAlonzo.Code.Function.Structures.T_IsInjection_92 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_332 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v0)
-- Function.Construct.Identity._._.IsInverse.inverseʳ
d_inverse'691'_392 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_392 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_502 (coe v0)
-- Function.Construct.Identity._._.IsInverse.isLeftInverse
d_isLeftInverse_402 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_402 v0
  = coe MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0)
-- Function.Construct.Identity._._.IsLeftInverse.from-cong
d_from'45'cong_464 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_464 v0
  = coe MAlonzo.Code.Function.Structures.d_from'45'cong_336 (coe v0)
-- Function.Construct.Identity._._.IsLeftInverse.inverseˡ
d_inverse'737'_466 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_466 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'737'_338 (coe v0)
-- Function.Construct.Identity._._.IsLeftInverse.isCongruent
d_isCongruent_468 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_468 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0)
-- Function.Construct.Identity._._.IsRightInverse.from-cong
d_from'45'cong_530 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_530 v0
  = coe MAlonzo.Code.Function.Structures.d_from'45'cong_422 (coe v0)
-- Function.Construct.Identity._._.IsRightInverse.inverseʳ
d_inverse'691'_532 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_532 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_424 (coe v0)
-- Function.Construct.Identity._._.IsRightInverse.isCongruent
d_isCongruent_534 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_534 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0)
-- Function.Construct.Identity._._.IsSurjection.isCongruent
d_isCongruent_666 ::
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_666 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_170 (coe v0)
-- Function.Construct.Identity._._.IsSurjection.surjective
d_surjective_674 ::
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_674 v0
  = coe MAlonzo.Code.Function.Structures.d_surjective_172 (coe v0)
-- Function.Construct.Identity._.isCongruent
d_isCongruent_736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_736 ~v0 ~v1 ~v2 ~v3 v4 = du_isCongruent_736 v4
du_isCongruent_736 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_736 v0
  = coe
      MAlonzo.Code.Function.Structures.C_IsCongruent'46'constructor_985
      (coe (\ v1 v2 v3 -> v3)) (coe v0) (coe v0)
-- Function.Construct.Identity._.isInjection
d_isInjection_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
d_isInjection_738 ~v0 ~v1 ~v2 ~v3 v4 = du_isInjection_738 v4
du_isInjection_738 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
du_isInjection_738 v0
  = coe
      MAlonzo.Code.Function.Structures.C_IsInjection'46'constructor_3997
      (coe du_isCongruent_736 (coe v0)) (coe (\ v1 v2 v3 -> v3))
-- Function.Construct.Identity._.isSurjection
d_isSurjection_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
d_isSurjection_740 ~v0 ~v1 ~v2 ~v3 v4 = du_isSurjection_740 v4
du_isSurjection_740 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
du_isSurjection_740 v0
  = coe
      MAlonzo.Code.Function.Structures.C_IsSurjection'46'constructor_6463
      (coe du_isCongruent_736 (coe v0)) (coe du_surjective_26)
-- Function.Construct.Identity._.isBijection
d_isBijection_742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
d_isBijection_742 ~v0 ~v1 ~v2 ~v3 v4 = du_isBijection_742 v4
du_isBijection_742 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
du_isBijection_742 v0
  = coe
      MAlonzo.Code.Function.Structures.C_IsBijection'46'constructor_10113
      (coe du_isInjection_738 (coe v0)) (coe du_surjective_26)
-- Function.Construct.Identity._.isLeftInverse
d_isLeftInverse_744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_744 ~v0 ~v1 ~v2 ~v3 v4 = du_isLeftInverse_744 v4
du_isLeftInverse_744 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
du_isLeftInverse_744 v0
  = coe
      MAlonzo.Code.Function.Structures.C_IsLeftInverse'46'constructor_14363
      (coe du_isCongruent_736 (coe v0)) (coe (\ v1 v2 v3 -> v3))
      (coe (\ v1 v2 v3 -> v3))
-- Function.Construct.Identity._.isRightInverse
d_isRightInverse_746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
d_isRightInverse_746 ~v0 ~v1 ~v2 ~v3 v4 = du_isRightInverse_746 v4
du_isRightInverse_746 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
du_isRightInverse_746 v0
  = coe
      MAlonzo.Code.Function.Structures.C_IsRightInverse'46'constructor_18837
      (coe du_isCongruent_736 (coe v0)) (coe (\ v1 v2 v3 -> v3))
      (coe (\ v1 v2 v3 -> v3))
-- Function.Construct.Identity._.isInverse
d_isInverse_748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490
d_isInverse_748 ~v0 ~v1 ~v2 ~v3 v4 = du_isInverse_748 v4
du_isInverse_748 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490
du_isInverse_748 v0
  = coe
      MAlonzo.Code.Function.Structures.C_IsInverse'46'constructor_22449
      (coe du_isLeftInverse_744 (coe v0)) (coe (\ v1 v2 v3 -> v3))
-- Function.Construct.Identity._.function
d_function_782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_function_782 ~v0 ~v1 ~v2 = du_function_782
du_function_782 :: MAlonzo.Code.Function.Bundles.T_Func_714
du_function_782
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._.injection
d_injection_784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
d_injection_784 ~v0 ~v1 ~v2 = du_injection_784
du_injection_784 :: MAlonzo.Code.Function.Bundles.T_Injection_776
du_injection_784
  = coe
      MAlonzo.Code.Function.Bundles.C_Injection'46'constructor_8675
      (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._.surjection
d_surjection_786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_surjection_786 ~v0 ~v1 ~v2 = du_surjection_786
du_surjection_786 :: MAlonzo.Code.Function.Bundles.T_Surjection_846
du_surjection_786
  = coe
      MAlonzo.Code.Function.Bundles.C_Surjection'46'constructor_11197
      (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2)) (coe du_surjective_26)
-- Function.Construct.Identity._.bijection
d_bijection_788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_bijection_788 ~v0 ~v1 ~v2 = du_bijection_788
du_bijection_788 :: MAlonzo.Code.Function.Bundles.T_Bijection_926
du_bijection_788
  = coe
      MAlonzo.Code.Function.Bundles.C_Bijection'46'constructor_15277
      (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2)) (coe du_bijective_30)
-- Function.Construct.Identity._.equivalence
d_equivalence_790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_equivalence_790 ~v0 ~v1 ~v2 = du_equivalence_790
du_equivalence_790 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_equivalence_790
  = coe
      MAlonzo.Code.Function.Bundles.C_Equivalence'46'constructor_25797
      (coe (\ v0 -> v0)) (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._.leftInverse
d_leftInverse_792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_leftInverse_792 ~v0 ~v1 ~v2 = du_leftInverse_792
du_leftInverse_792 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du_leftInverse_792
  = coe
      MAlonzo.Code.Function.Bundles.C_LeftInverse'46'constructor_29775
      (coe (\ v0 -> v0)) (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 -> v2)) (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._.rightInverse
d_rightInverse_794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_rightInverse_794 ~v0 ~v1 ~v2 = du_rightInverse_794
du_rightInverse_794 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du_rightInverse_794
  = coe
      MAlonzo.Code.Function.Bundles.C_RightInverse'46'constructor_34573
      (coe (\ v0 -> v0)) (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 -> v2)) (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._.inverse
d_inverse_796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_inverse_796 ~v0 ~v1 ~v2 = du_inverse_796
du_inverse_796 :: MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_inverse_796
  = coe
      MAlonzo.Code.Function.Bundles.C_Inverse'46'constructor_38621
      (coe (\ v0 -> v0)) (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 -> v2)) (coe du_inverse'7495'_36)
-- Function.Construct.Identity._.⟶-id
d_'10230''45'id_806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Func_714
d_'10230''45'id_806 ~v0 ~v1 = du_'10230''45'id_806
du_'10230''45'id_806 :: MAlonzo.Code.Function.Bundles.T_Func_714
du_'10230''45'id_806 = coe du_function_782
-- Function.Construct.Identity._.↣-id
d_'8611''45'id_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Injection_776
d_'8611''45'id_808 ~v0 ~v1 = du_'8611''45'id_808
du_'8611''45'id_808 ::
  MAlonzo.Code.Function.Bundles.T_Injection_776
du_'8611''45'id_808 = coe du_injection_784
-- Function.Construct.Identity._.↠-id
d_'8608''45'id_810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Surjection_846
d_'8608''45'id_810 ~v0 ~v1 = du_'8608''45'id_810
du_'8608''45'id_810 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du_'8608''45'id_810 = coe du_surjection_786
-- Function.Construct.Identity._.⤖-id
d_'10518''45'id_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Bijection_926
d_'10518''45'id_812 ~v0 ~v1 = du_'10518''45'id_812
du_'10518''45'id_812 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du_'10518''45'id_812 = coe du_bijection_788
-- Function.Construct.Identity._.⇔-id
d_'8660''45'id_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8660''45'id_814 ~v0 ~v1 = du_'8660''45'id_814
du_'8660''45'id_814 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8660''45'id_814 = coe du_equivalence_790
-- Function.Construct.Identity._.↩-id
d_'8617''45'id_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_'8617''45'id_816 ~v0 ~v1 = du_'8617''45'id_816
du_'8617''45'id_816 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du_'8617''45'id_816 = coe du_leftInverse_792
-- Function.Construct.Identity._.↪-id
d_'8618''45'id_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_'8618''45'id_818 ~v0 ~v1 = du_'8618''45'id_818
du_'8618''45'id_818 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du_'8618''45'id_818 = coe du_rightInverse_794
-- Function.Construct.Identity._.↔-id
d_'8596''45'id_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8596''45'id_820 ~v0 ~v1 = du_'8596''45'id_820
du_'8596''45'id_820 :: MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8596''45'id_820 = coe du_inverse_796
-- Function.Construct.Identity.id-⟶
d_id'45''10230'_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Func_714
d_id'45''10230'_822 v0 v1 = coe du_'10230''45'id_806
-- Function.Construct.Identity.id-↣
d_id'45''8611'_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Injection_776
d_id'45''8611'_824 v0 v1 = coe du_'8611''45'id_808
-- Function.Construct.Identity.id-↠
d_id'45''8608'_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Surjection_846
d_id'45''8608'_826 v0 v1 = coe du_'8608''45'id_810
-- Function.Construct.Identity.id-⤖
d_id'45''10518'_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Bijection_926
d_id'45''10518'_828 v0 v1 = coe du_'10518''45'id_812
-- Function.Construct.Identity.id-⇔
d_id'45''8660'_830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_id'45''8660'_830 v0 v1 = coe du_'8660''45'id_814
-- Function.Construct.Identity.id-↩
d_id'45''8617'_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_id'45''8617'_832 v0 v1 = coe du_'8617''45'id_816
-- Function.Construct.Identity.id-↪
d_id'45''8618'_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_id'45''8618'_834 v0 v1 = coe du_'8618''45'id_818
-- Function.Construct.Identity.id-↔
d_id'45''8596'_836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_id'45''8596'_836 v0 v1 = coe du_'8596''45'id_820
