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

module MAlonzo.Code.Function.Properties.Surjection where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Function.Construct.Composition
import qualified MAlonzo.Code.Function.Construct.Identity
import qualified MAlonzo.Code.Function.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Function.Properties.Surjection._.Eq₁._≈_
d__'8776'__40 ::
  T_GeneralizeTel_503 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__40 = erased
-- Function.Properties.Surjection._.Eq₂._≈_
d__'8776'__66 ::
  T_GeneralizeTel_503 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__66 = erased
-- Function.Properties.Surjection.mkSurjection
d_mkSurjection_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d_mkSurjection_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_mkSurjection_90 v6 v7
du_mkSurjection_90 ::
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
du_mkSurjection_90 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1002
      (coe MAlonzo.Code.Function.Bundles.d_to_780 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_cong_782 (coe v0)) (coe v1)
-- Function.Properties.Surjection.↠⇒⟶
d_'8608''8658''10230'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_'8608''8658''10230'_158 ~v0 ~v1 ~v2 ~v3
  = du_'8608''8658''10230'_158
du_'8608''8658''10230'_158 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
du_'8608''8658''10230'_158
  = coe MAlonzo.Code.Function.Bundles.du_function_932
-- Function.Properties.Surjection.↠⇒↪
d_'8608''8658''8618'_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d_'8608''8658''8618'_160 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8608''8658''8618'_160 v4
du_'8608''8658''8618'_160 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
du_'8608''8658''8618'_160 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8618'_2496
      (coe
         (\ v1 ->
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Function.Structures.du_strictlySurjective_246
                 (coe
                    MAlonzo.Code.Function.Bundles.du_isSurjection_990
                    (coe
                       MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
                    (coe
                       MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
                    (coe v0))
                 (coe v1))))
      (coe MAlonzo.Code.Function.Bundles.d_to_926 (coe v0)) erased
-- Function.Properties.Surjection._..extendedlambda0
d_'46'extendedlambda0_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_240 = erased
-- Function.Properties.Surjection.↠⇒⇔
d_'8608''8658''8660'_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_'8608''8658''8660'_242 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8608''8658''8660'_242 v4
du_'8608''8658''8660'_242 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_'8608''8658''8660'_242 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2474
      (coe MAlonzo.Code.Function.Bundles.d_to_926 (coe v0))
      (coe
         (\ v1 ->
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe MAlonzo.Code.Function.Bundles.d_surjective_930 v0 v1)))
-- Function.Properties.Surjection.refl
d_refl_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d_refl_322 ~v0 ~v1 ~v2 = du_refl_322
du_refl_322 :: MAlonzo.Code.Function.Bundles.T_Surjection_918
du_refl_322
  = coe MAlonzo.Code.Function.Construct.Identity.du_surjection_626
-- Function.Properties.Surjection.trans
d_trans_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d_trans_326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_trans_326
du_trans_326 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
du_trans_326
  = coe
      MAlonzo.Code.Function.Construct.Composition.du_surjection_1532
-- Function.Properties.Surjection._.to⁻
d_to'8315'_346 ::
  T_GeneralizeTel_11671 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  AgdaAny -> AgdaAny
d_to'8315'_346 ~v0 v1 = du_to'8315'_346 v1
du_to'8315'_346 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  AgdaAny -> AgdaAny
du_to'8315'_346 v0
  = coe MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v0)
-- Function.Properties.Surjection._.Eq₁._≈_
d__'8776'__352 ::
  T_GeneralizeTel_11671 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__352 = erased
-- Function.Properties.Surjection._.Eq₂._≈_
d__'8776'__378 ::
  T_GeneralizeTel_11671 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__378 = erased
-- Function.Properties.Surjection.injective⇒to⁻-cong
d_injective'8658'to'8315''45'cong_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective'8658'to'8315''45'cong_402 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
                                      v8 v9 v10
  = du_injective'8658'to'8315''45'cong_402 v2 v5 v6 v7 v8 v9 v10
du_injective'8658'to'8315''45'cong_402 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_injective'8658'to'8315''45'cong_402 v0 v1 v2 v3 v4 v5 v6
  = coe
      v3
      (coe
         MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v2) (coe v4))
      (coe
         MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            MAlonzo.Code.Function.Bundles.d_to_926 v2
            (coe
               MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v2) (coe v4)))
         (coe
            MAlonzo.Code.Function.Bundles.d_to_926 v2
            (coe
               MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v2) (coe v5)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))))
            (coe
               MAlonzo.Code.Function.Bundles.d_to_926 v2
               (coe
                  MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v2) (coe v4)))
            v4
            (coe
               MAlonzo.Code.Function.Bundles.d_to_926 v2
               (coe
                  MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v2) (coe v5)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))))
               v4 v5
               (coe
                  MAlonzo.Code.Function.Bundles.d_to_926 v2
                  (coe
                     MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v2) (coe v5)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1)))
                  v5
                  (coe
                     MAlonzo.Code.Function.Bundles.d_to_926 v2
                     (coe
                        MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v2) (coe v5)))
                  (coe
                     MAlonzo.Code.Function.Bundles.d_to_926 v2
                     (coe
                        MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v2) (coe v5)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))))
                     (coe
                        MAlonzo.Code.Function.Bundles.d_to_926 v2
                        (coe
                           MAlonzo.Code.Function.Bundles.du_to'8315'_996 (coe v2) (coe v5))))
                  (coe
                     MAlonzo.Code.Function.Bundles.du_to'8728'to'8315'_1000 (coe v0)
                     (coe v1) (coe v2) (coe v5)))
               v6)
            (coe
               MAlonzo.Code.Function.Bundles.du_to'8728'to'8315'_1000 (coe v0)
               (coe v1) (coe v2) (coe v4))))
-- Function.Properties.Surjection..generalizedField-S.a
d_'46'generalizedField'45'S'46'a_491 ::
  T_GeneralizeTel_503 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'a_491 v0
  = case coe v0 of
      C_mkGeneralizeTel_505 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-S.ℓ
d_'46'generalizedField'45'S'46'ℓ_493 ::
  T_GeneralizeTel_503 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'ℓ_493 v0
  = case coe v0 of
      C_mkGeneralizeTel_505 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-S
d_'46'generalizedField'45'S_495 ::
  T_GeneralizeTel_503 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'46'generalizedField'45'S_495 v0
  = case coe v0 of
      C_mkGeneralizeTel_505 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T.a
d_'46'generalizedField'45'T'46'a_497 ::
  T_GeneralizeTel_503 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'a_497 v0
  = case coe v0 of
      C_mkGeneralizeTel_505 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T.ℓ
d_'46'generalizedField'45'T'46'ℓ_499 ::
  T_GeneralizeTel_503 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'ℓ_499 v0
  = case coe v0 of
      C_mkGeneralizeTel_505 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T
d_'46'generalizedField'45'T_501 ::
  T_GeneralizeTel_503 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'46'generalizedField'45'T_501 v0
  = case coe v0 of
      C_mkGeneralizeTel_505 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection.GeneralizeTel
d_GeneralizeTel_503 = ()
data T_GeneralizeTel_503
  = C_mkGeneralizeTel_505 MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Agda.Primitive.T_Level_18
                          MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
-- Function.Properties.Surjection..generalizedField-S.a
d_'46'generalizedField'45'S'46'a_11659 ::
  T_GeneralizeTel_11671 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'a_11659 v0
  = case coe v0 of
      C_mkGeneralizeTel_11673 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-S.ℓ
d_'46'generalizedField'45'S'46'ℓ_11661 ::
  T_GeneralizeTel_11671 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'S'46'ℓ_11661 v0
  = case coe v0 of
      C_mkGeneralizeTel_11673 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-S
d_'46'generalizedField'45'S_11663 ::
  T_GeneralizeTel_11671 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'46'generalizedField'45'S_11663 v0
  = case coe v0 of
      C_mkGeneralizeTel_11673 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T.a
d_'46'generalizedField'45'T'46'a_11665 ::
  T_GeneralizeTel_11671 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'a_11665 v0
  = case coe v0 of
      C_mkGeneralizeTel_11673 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T.ℓ
d_'46'generalizedField'45'T'46'ℓ_11667 ::
  T_GeneralizeTel_11671 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'T'46'ℓ_11667 v0
  = case coe v0 of
      C_mkGeneralizeTel_11673 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection..generalizedField-T
d_'46'generalizedField'45'T_11669 ::
  T_GeneralizeTel_11671 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'46'generalizedField'45'T_11669 v0
  = case coe v0 of
      C_mkGeneralizeTel_11673 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Properties.Surjection.GeneralizeTel
d_GeneralizeTel_11671 = ()
data T_GeneralizeTel_11671
  = C_mkGeneralizeTel_11673 MAlonzo.Code.Agda.Primitive.T_Level_18
                            MAlonzo.Code.Agda.Primitive.T_Level_18
                            MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
                            MAlonzo.Code.Agda.Primitive.T_Level_18
                            MAlonzo.Code.Agda.Primitive.T_Level_18
                            MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
