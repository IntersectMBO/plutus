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

module MAlonzo.Code.Function.Construct.Identity where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Function.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

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
d_IsBijection_52 a0 a1 a2 a3 a4 a5 = ()
-- Function.Construct.Identity._._.IsCongruent
d_IsCongruent_56 a0 a1 a2 a3 a4 a5 = ()
-- Function.Construct.Identity._._.IsInjection
d_IsInjection_60 a0 a1 a2 a3 a4 a5 = ()
-- Function.Construct.Identity._._.IsInverse
d_IsInverse_64 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Construct.Identity._._.IsLeftInverse
d_IsLeftInverse_68 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Construct.Identity._._.IsRightInverse
d_IsRightInverse_72 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Construct.Identity._._.IsSurjection
d_IsSurjection_76 a0 a1 a2 a3 a4 a5 = ()
-- Function.Construct.Identity._._.IsBijection.isInjection
d_isInjection_94 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98
d_isInjection_94 v0
  = coe MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0)
-- Function.Construct.Identity._._.IsBijection.surjective
d_surjective_100 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_100 v0
  = coe MAlonzo.Code.Function.Structures.d_surjective_266 (coe v0)
-- Function.Construct.Identity._._.IsCongruent.cong
d_cong_156 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_156 v0
  = coe MAlonzo.Code.Function.Structures.d_cong_32 (coe v0)
-- Function.Construct.Identity._._.IsCongruent.isEquivalence₁
d_isEquivalence'8321'_158 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence'8321'_158 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0)
-- Function.Construct.Identity._._.IsCongruent.isEquivalence₂
d_isEquivalence'8322'_160 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence'8322'_160 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0)
-- Function.Construct.Identity._._.IsInjection.injective
d_injective_218 ::
  MAlonzo.Code.Function.Structures.T_IsInjection_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_218 v0
  = coe MAlonzo.Code.Function.Structures.d_injective_108 (coe v0)
-- Function.Construct.Identity._._.IsInjection.isCongruent
d_isCongruent_220 ::
  MAlonzo.Code.Function.Structures.T_IsInjection_98 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_220 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v0)
-- Function.Construct.Identity._._.IsInverse.inverseʳ
d_inverse'691'_284 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_284 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_538 (coe v0)
-- Function.Construct.Identity._._.IsInverse.isLeftInverse
d_isLeftInverse_294 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
d_isLeftInverse_294 v0
  = coe MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0)
-- Function.Construct.Identity._._.IsLeftInverse.from-cong
d_from'45'cong_360 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_360 v0
  = coe MAlonzo.Code.Function.Structures.d_from'45'cong_360 (coe v0)
-- Function.Construct.Identity._._.IsLeftInverse.inverseˡ
d_inverse'737'_362 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_362 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'737'_362 (coe v0)
-- Function.Construct.Identity._._.IsLeftInverse.isCongruent
d_isCongruent_364 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_364 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0)
-- Function.Construct.Identity._._.IsRightInverse.from-cong
d_from'45'cong_430 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_430 v0
  = coe MAlonzo.Code.Function.Structures.d_from'45'cong_452 (coe v0)
-- Function.Construct.Identity._._.IsRightInverse.inverseʳ
d_inverse'691'_432 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_432 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_454 (coe v0)
-- Function.Construct.Identity._._.IsRightInverse.isCongruent
d_isCongruent_434 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_434 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0)
-- Function.Construct.Identity._._.IsSurjection.isCongruent
d_isCongruent_500 ::
  MAlonzo.Code.Function.Structures.T_IsSurjection_174 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_500 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_182 (coe v0)
-- Function.Construct.Identity._._.IsSurjection.surjective
d_surjective_508 ::
  MAlonzo.Code.Function.Structures.T_IsSurjection_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_508 v0
  = coe MAlonzo.Code.Function.Structures.d_surjective_184 (coe v0)
-- Function.Construct.Identity._.isCongruent
d_isCongruent_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_574 ~v0 ~v1 ~v2 ~v3 v4 = du_isCongruent_574 v4
du_isCongruent_574 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_574 v0
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_94
      (coe (\ v1 v2 v3 -> v3)) (coe v0) (coe v0)
-- Function.Construct.Identity._.isInjection
d_isInjection_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98
d_isInjection_576 ~v0 ~v1 ~v2 ~v3 v4 = du_isInjection_576 v4
du_isInjection_576 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98
du_isInjection_576 v0
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_170
      (coe du_isCongruent_574 (coe v0)) (coe (\ v1 v2 v3 -> v3))
-- Function.Construct.Identity._.isSurjection
d_isSurjection_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
d_isSurjection_578 ~v0 ~v1 ~v2 ~v3 v4 = du_isSurjection_578 v4
du_isSurjection_578 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
du_isSurjection_578 v0
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_252
      (coe du_isCongruent_574 (coe v0)) (coe du_surjective_26)
-- Function.Construct.Identity._.isBijection
d_isBijection_580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256
d_isBijection_580 ~v0 ~v1 ~v2 ~v3 v4 = du_isBijection_580 v4
du_isBijection_580 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256
du_isBijection_580 v0
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_340
      (coe du_isInjection_576 (coe v0)) (coe du_surjective_26)
-- Function.Construct.Identity._.isLeftInverse
d_isLeftInverse_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
d_isLeftInverse_582 ~v0 ~v1 ~v2 ~v3 v4 = du_isLeftInverse_582 v4
du_isLeftInverse_582 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
du_isLeftInverse_582 v0
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_432
      (coe du_isCongruent_574 (coe v0)) (coe (\ v1 v2 v3 -> v3))
      (coe (\ v1 v2 v3 -> v3))
-- Function.Construct.Identity._.isRightInverse
d_isRightInverse_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438
d_isRightInverse_584 ~v0 ~v1 ~v2 ~v3 v4 = du_isRightInverse_584 v4
du_isRightInverse_584 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438
du_isRightInverse_584 v0
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_520
      (coe du_isCongruent_574 (coe v0)) (coe (\ v1 v2 v3 -> v3))
      (coe (\ v1 v2 v3 -> v3))
-- Function.Construct.Identity._.isInverse
d_isInverse_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526
d_isInverse_586 ~v0 ~v1 ~v2 ~v3 v4 = du_isInverse_586 v4
du_isInverse_586 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526
du_isInverse_586 v0
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_618
      (coe du_isLeftInverse_582 (coe v0)) (coe (\ v1 v2 v3 -> v3))
-- Function.Construct.Identity._.function
d_function_622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_function_622 ~v0 ~v1 ~v2 = du_function_622
du_function_622 :: MAlonzo.Code.Function.Bundles.T_Func_774
du_function_622
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_840 (coe (\ v0 -> v0))
      (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._.injection
d_injection_624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
d_injection_624 ~v0 ~v1 ~v2 = du_injection_624
du_injection_624 :: MAlonzo.Code.Function.Bundles.T_Injection_842
du_injection_624
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_916 (coe (\ v0 -> v0))
      (coe (\ v0 v1 v2 -> v2)) (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._.surjection
d_surjection_626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d_surjection_626 ~v0 ~v1 ~v2 = du_surjection_626
du_surjection_626 :: MAlonzo.Code.Function.Bundles.T_Surjection_918
du_surjection_626
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1002 (coe (\ v0 -> v0))
      (coe (\ v0 v1 v2 -> v2)) (coe du_surjective_26)
-- Function.Construct.Identity._.bijection
d_bijection_628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
d_bijection_628 ~v0 ~v1 ~v2 = du_bijection_628
du_bijection_628 :: MAlonzo.Code.Function.Bundles.T_Bijection_1004
du_bijection_628
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1094 (coe (\ v0 -> v0))
      (coe (\ v0 v1 v2 -> v2)) (coe du_bijective_30)
-- Function.Construct.Identity._.equivalence
d_equivalence_630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_equivalence_630 ~v0 ~v1 ~v2 = du_equivalence_630
du_equivalence_630 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_equivalence_630
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1940 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._.leftInverse
d_leftInverse_632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d_leftInverse_632 ~v0 ~v1 ~v2 = du_leftInverse_632
du_leftInverse_632 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
du_leftInverse_632
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2034 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 -> v2)) (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._.rightInverse
d_rightInverse_634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d_rightInverse_634 ~v0 ~v1 ~v2 = du_rightInverse_634
du_rightInverse_634 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
du_rightInverse_634
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2120 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 -> v2)) (coe (\ v0 v1 v2 -> v2))
-- Function.Construct.Identity._.inverse
d_inverse_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_inverse_636 ~v0 ~v1 ~v2 = du_inverse_636
du_inverse_636 :: MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_inverse_636
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2220 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 -> v2)) (coe du_inverse'7495'_36)
-- Function.Construct.Identity._.⟶-id
d_'10230''45'id_646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Func_774
d_'10230''45'id_646 ~v0 ~v1 = du_'10230''45'id_646
du_'10230''45'id_646 :: MAlonzo.Code.Function.Bundles.T_Func_774
du_'10230''45'id_646 = coe du_function_622
-- Function.Construct.Identity._.↣-id
d_'8611''45'id_648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Injection_842
d_'8611''45'id_648 ~v0 ~v1 = du_'8611''45'id_648
du_'8611''45'id_648 ::
  MAlonzo.Code.Function.Bundles.T_Injection_842
du_'8611''45'id_648 = coe du_injection_624
-- Function.Construct.Identity._.↠-id
d_'8608''45'id_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Surjection_918
d_'8608''45'id_650 ~v0 ~v1 = du_'8608''45'id_650
du_'8608''45'id_650 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_918
du_'8608''45'id_650 = coe du_surjection_626
-- Function.Construct.Identity._.⤖-id
d_'10518''45'id_652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Bijection_1004
d_'10518''45'id_652 ~v0 ~v1 = du_'10518''45'id_652
du_'10518''45'id_652 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
du_'10518''45'id_652 = coe du_bijection_628
-- Function.Construct.Identity._.⇔-id
d_'8660''45'id_654 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_'8660''45'id_654 ~v0 ~v1 = du_'8660''45'id_654
du_'8660''45'id_654 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_'8660''45'id_654 = coe du_equivalence_630
-- Function.Construct.Identity._.↩-id
d_'8617''45'id_656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d_'8617''45'id_656 ~v0 ~v1 = du_'8617''45'id_656
du_'8617''45'id_656 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
du_'8617''45'id_656 = coe du_leftInverse_632
-- Function.Construct.Identity._.↪-id
d_'8618''45'id_658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d_'8618''45'id_658 ~v0 ~v1 = du_'8618''45'id_658
du_'8618''45'id_658 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
du_'8618''45'id_658 = coe du_rightInverse_634
-- Function.Construct.Identity._.↔-id
d_'8596''45'id_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8596''45'id_660 ~v0 ~v1 = du_'8596''45'id_660
du_'8596''45'id_660 :: MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8596''45'id_660 = coe du_inverse_636
-- Function.Construct.Identity.id-⟶
d_id'45''10230'_662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Func_774
d_id'45''10230'_662 v0 v1 = coe du_'10230''45'id_646
-- Function.Construct.Identity.id-↣
d_id'45''8611'_664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Injection_842
d_id'45''8611'_664 v0 v1 = coe du_'8611''45'id_648
-- Function.Construct.Identity.id-↠
d_id'45''8608'_666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Surjection_918
d_id'45''8608'_666 v0 v1 = coe du_'8608''45'id_650
-- Function.Construct.Identity.id-⤖
d_id'45''10518'_668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Bijection_1004
d_id'45''10518'_668 v0 v1 = coe du_'10518''45'id_652
-- Function.Construct.Identity.id-⇔
d_id'45''8660'_670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_id'45''8660'_670 v0 v1 = coe du_'8660''45'id_654
-- Function.Construct.Identity.id-↩
d_id'45''8617'_672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d_id'45''8617'_672 v0 v1 = coe du_'8617''45'id_656
-- Function.Construct.Identity.id-↪
d_id'45''8618'_674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d_id'45''8618'_674 v0 v1 = coe du_'8618''45'id_658
-- Function.Construct.Identity.id-↔
d_id'45''8596'_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_id'45''8596'_676 v0 v1 = coe du_'8596''45'id_660
