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

module MAlonzo.Code.Relation.Nullary.Reflects where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Bool.Base qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Nullary.Negation.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Nullary.Reflects.Reflects
d_Reflects_16 a0 a1 a2 = ()
data T_Reflects_16 = C_of'696'_22 AgdaAny | C_of'8319'_26
-- Relation.Nullary.Reflects.of
d_of_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Bool -> AgdaAny -> T_Reflects_16
d_of_30 ~v0 ~v1 v2 v3 = du_of_30 v2 v3
du_of_30 :: Bool -> AgdaAny -> T_Reflects_16
du_of_30 v0 v1
  = if coe v0 then coe C_of'696'_22 (coe v1) else coe C_of'8319'_26
-- Relation.Nullary.Reflects.invert
d_invert_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Bool -> T_Reflects_16 -> AgdaAny
d_invert_38 ~v0 ~v1 ~v2 v3 = du_invert_38 v3
du_invert_38 :: T_Reflects_16 -> AgdaAny
du_invert_38 v0
  = case coe v0 of
      C_of'696'_22 v1 -> coe v1
      C_of'8319'_26   -> erased
      _               -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Reflects.recompute
d_recompute_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Bool -> T_Reflects_16 -> AgdaAny -> AgdaAny
d_recompute_46 ~v0 ~v1 ~v2 v3 ~v4 = du_recompute_46 v3
du_recompute_46 :: T_Reflects_16 -> AgdaAny
du_recompute_46 v0
  = case coe v0 of
      C_of'696'_22 v1 -> coe v1
      C_of'8319'_26
        -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction'45'irr_38
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Reflects.recompute-constant
d_recompute'45'constant_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  T_Reflects_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_recompute'45'constant_62 = erased
-- Relation.Nullary.Reflects.T-reflects
d_T'45'reflects_66 :: Bool -> T_Reflects_16
d_T'45'reflects_66 v0
  = if coe v0
      then coe
             du_of_30 (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      else coe du_of_30 (coe v0) (coe (\ v1 -> v1))
-- Relation.Nullary.Reflects.¬-reflects
d_'172''45'reflects_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Bool -> T_Reflects_16 -> T_Reflects_16
d_'172''45'reflects_70 ~v0 ~v1 ~v2 v3 = du_'172''45'reflects_70 v3
du_'172''45'reflects_70 :: T_Reflects_16 -> T_Reflects_16
du_'172''45'reflects_70 v0
  = case coe v0 of
      C_of'696'_22 v1
        -> coe
             du_of_30
             (coe
                MAlonzo.Code.Data.Bool.Base.d_not_22
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe (\ v2 -> coe v2 v1))
      C_of'8319'_26
        -> coe
             du_of_30
             (coe
                MAlonzo.Code.Data.Bool.Base.d_not_22
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Reflects._×-reflects_
d__'215''45'reflects__82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool -> Bool -> T_Reflects_16 -> T_Reflects_16 -> T_Reflects_16
d__'215''45'reflects__82 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du__'215''45'reflects__82 v5 v6 v7
du__'215''45'reflects__82 ::
  Bool -> T_Reflects_16 -> T_Reflects_16 -> T_Reflects_16
du__'215''45'reflects__82 v0 v1 v2
  = case coe v1 of
      C_of'696'_22 v3
        -> case coe v2 of
             C_of'696'_22 v4
               -> coe
                    du_of_30
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
             C_of'8319'_26
               -> coe
                    du_of_30
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      C_of'8319'_26
        -> coe
             du_of_30
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Reflects._⊎-reflects_
d__'8846''45'reflects__98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool -> Bool -> T_Reflects_16 -> T_Reflects_16 -> T_Reflects_16
d__'8846''45'reflects__98 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du__'8846''45'reflects__98 v5 v6 v7
du__'8846''45'reflects__98 ::
  Bool -> T_Reflects_16 -> T_Reflects_16 -> T_Reflects_16
du__'8846''45'reflects__98 v0 v1 v2
  = case coe v1 of
      C_of'696'_22 v3
        -> coe
             du_of_30
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v0))
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v3))
      C_of'8319'_26
        -> case coe v2 of
             C_of'696'_22 v4
               -> coe
                    du_of_30
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4))
             C_of'8319'_26
               -> coe
                    du_of_30
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Reflects._→-reflects_
d__'8594''45'reflects__114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool -> Bool -> T_Reflects_16 -> T_Reflects_16 -> T_Reflects_16
d__'8594''45'reflects__114 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du__'8594''45'reflects__114 v5 v6 v7
du__'8594''45'reflects__114 ::
  Bool -> T_Reflects_16 -> T_Reflects_16 -> T_Reflects_16
du__'8594''45'reflects__114 v0 v1 v2
  = case coe v1 of
      C_of'696'_22 v3
        -> case coe v2 of
             C_of'696'_22 v4
               -> coe
                    du_of_30
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d_not_22
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                    (coe (\ v5 -> v4))
             C_of'8319'_26
               -> coe
                    du_of_30
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d_not_22
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      C_of'8319'_26
        -> coe
             du_of_30
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe
                   MAlonzo.Code.Data.Bool.Base.d_not_22
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                (coe v0))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                     erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Reflects.fromEquivalence
d_fromEquivalence_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_Reflects_16
d_fromEquivalence_132 ~v0 ~v1 v2 v3 v4
  = du_fromEquivalence_132 v2 v3 v4
du_fromEquivalence_132 ::
  Bool ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_Reflects_16
du_fromEquivalence_132 v0 v1 v2
  = if coe v0
      then coe
             du_of_30 (coe v0)
             (coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      else coe du_of_30 (coe v0) (coe v2)
-- Relation.Nullary.Reflects.det
d_det_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  Bool ->
  T_Reflects_16 ->
  T_Reflects_16 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_det_146 = erased
-- Relation.Nullary.Reflects.T-reflects-elim
d_T'45'reflects'45'elim_164 ::
  Bool ->
  Bool ->
  T_Reflects_16 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'45'reflects'45'elim_164 = erased
