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

module MAlonzo.Code.Untyped.RenamingSubstitution where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Untyped

-- Untyped.RenamingSubstitution.Ren
d_Ren_4 :: Integer -> Integer -> ()
d_Ren_4 = erased
-- Untyped.RenamingSubstitution.lift
d_lift_14 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_lift_14 ~v0 ~v1 v2 v3 = du_lift_14 v2 v3
du_lift_14 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_lift_14 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> coe MAlonzo.Code.Data.Fin.Base.C_suc_16 (coe v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.renList
d_renList_26 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_renList_26 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe v3
      (:) v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_ren_32 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_renList_26 (coe v0) (coe v1) (coe v2) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.ren
d_ren_32 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_ren_32 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Untyped.C_'96'_18 v4
        -> coe MAlonzo.Code.Untyped.C_'96'_18 (coe v2 v4)
      MAlonzo.Code.Untyped.C_ƛ_20 v4
        -> coe
             MAlonzo.Code.Untyped.C_ƛ_20
             (coe
                d_ren_32 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe addInt (coe (1 :: Integer)) (coe v1))
                (coe du_lift_14 (coe v2)) (coe v4))
      MAlonzo.Code.Untyped.C__'183'__22 v4 v5
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22
             (coe d_ren_32 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_ren_32 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Untyped.C_force_24 v4
        -> coe
             MAlonzo.Code.Untyped.C_force_24
             (coe d_ren_32 (coe v0) (coe v1) (coe v2) (coe v4))
      MAlonzo.Code.Untyped.C_delay_26 v4
        -> coe
             MAlonzo.Code.Untyped.C_delay_26
             (coe d_ren_32 (coe v0) (coe v1) (coe v2) (coe v4))
      MAlonzo.Code.Untyped.C_con_28 v4 -> coe v3
      MAlonzo.Code.Untyped.C_constr_34 v4 v5
        -> coe
             MAlonzo.Code.Untyped.C_constr_34 (coe v4)
             (coe d_renList_26 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Untyped.C_case_40 v4 v5
        -> coe
             MAlonzo.Code.Untyped.C_case_40
             (coe d_ren_32 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_renList_26 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Untyped.C_builtin_44 v4 -> coe v3
      MAlonzo.Code.Untyped.C_error_46 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.weaken
d_weaken_88 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_weaken_88 v0 v1
  = coe
      d_ren_32 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe MAlonzo.Code.Data.Fin.Base.C_suc_16) (coe v1)
-- Untyped.RenamingSubstitution.lift-cong
d_lift'45'cong_104 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'45'cong_104 = erased
-- Untyped.RenamingSubstitution.renList-cong
d_renList'45'cong_124 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renList'45'cong_124 = erased
-- Untyped.RenamingSubstitution.ren-cong
d_ren'45'cong_138 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'cong_138 = erased
-- Untyped.RenamingSubstitution.lift-id
d_lift'45'id_196 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'45'id_196 = erased
-- Untyped.RenamingSubstitution.lift-comp
d_lift'45'comp_212 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'45'comp_212 = erased
-- Untyped.RenamingSubstitution.renList-id
d_renList'45'id_228 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renList'45'id_228 = erased
-- Untyped.RenamingSubstitution.ren-id
d_ren'45'id_234 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'id_234 = erased
-- Untyped.RenamingSubstitution.renList-comp
d_renList'45'comp_276 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renList'45'comp_276 = erased
-- Untyped.RenamingSubstitution.ren-comp
d_ren'45'comp_290 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'comp_290 = erased
-- Untyped.RenamingSubstitution.Sub
d_Sub_368 :: Integer -> Integer -> ()
d_Sub_368 = erased
-- Untyped.RenamingSubstitution.lifts
d_lifts_378 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_lifts_378 ~v0 v1 v2 v3 = du_lifts_378 v1 v2 v3
du_lifts_378 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_lifts_378 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Untyped.C_'96'_18
             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> coe
             d_ren_32 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v0))
             (coe MAlonzo.Code.Data.Fin.Base.C_suc_16) (coe v1 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.subList
d_subList_390 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_subList_390 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe v3
      (:) v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_sub_396 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_subList_390 (coe v0) (coe v1) (coe v2) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.sub
d_sub_396 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_sub_396 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Untyped.C_'96'_18 v4 -> coe v2 v4
      MAlonzo.Code.Untyped.C_ƛ_20 v4
        -> coe
             MAlonzo.Code.Untyped.C_ƛ_20
             (coe
                d_sub_396 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe addInt (coe (1 :: Integer)) (coe v1))
                (coe du_lifts_378 (coe v1) (coe v2)) (coe v4))
      MAlonzo.Code.Untyped.C__'183'__22 v4 v5
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22
             (coe d_sub_396 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_sub_396 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Untyped.C_force_24 v4
        -> coe
             MAlonzo.Code.Untyped.C_force_24
             (coe d_sub_396 (coe v0) (coe v1) (coe v2) (coe v4))
      MAlonzo.Code.Untyped.C_delay_26 v4
        -> coe
             MAlonzo.Code.Untyped.C_delay_26
             (coe d_sub_396 (coe v0) (coe v1) (coe v2) (coe v4))
      MAlonzo.Code.Untyped.C_con_28 v4 -> coe v3
      MAlonzo.Code.Untyped.C_constr_34 v4 v5
        -> coe
             MAlonzo.Code.Untyped.C_constr_34 (coe v4)
             (coe d_subList_390 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Untyped.C_case_40 v4 v5
        -> coe
             MAlonzo.Code.Untyped.C_case_40
             (coe d_sub_396 (coe v0) (coe v1) (coe v2) (coe v4))
             (coe d_subList_390 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Untyped.C_builtin_44 v4 -> coe v3
      MAlonzo.Code.Untyped.C_error_46 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.extend
d_extend_454 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_extend_454 ~v0 ~v1 v2 v3 v4 = du_extend_454 v2 v3 v4
du_extend_454 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_extend_454 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v1
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4 -> coe v0 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution._[_]
d__'91'_'93'_468 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d__'91'_'93'_468 v0 v1 v2
  = coe
      d_sub_396 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v0)
      (coe du_extend_454 (coe MAlonzo.Code.Untyped.C_'96'_18) (coe v2))
      (coe v1)
-- Untyped.RenamingSubstitution.lifts-cong
d_lifts'45'cong_486 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lifts'45'cong_486 = erased
-- Untyped.RenamingSubstitution.subList-cong
d_subList'45'cong_506 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subList'45'cong_506 = erased
-- Untyped.RenamingSubstitution.sub-cong
d_sub'45'cong_520 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'cong_520 = erased
-- Untyped.RenamingSubstitution.lifts-id
d_lifts'45'id_578 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lifts'45'id_578 = erased
-- Untyped.RenamingSubstitution.subList-id
d_subList'45'id_586 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subList'45'id_586 = erased
-- Untyped.RenamingSubstitution.sub-id
d_sub'45'id_592 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'id_592 = erased
-- Untyped.RenamingSubstitution.lifts-lift
d_lifts'45'lift_634 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lifts'45'lift_634 = erased
-- Untyped.RenamingSubstitution.subList-ren
d_subList'45'ren_658 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subList'45'ren_658 = erased
-- Untyped.RenamingSubstitution.sub-ren
d_sub'45'ren_672 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'ren_672 = erased
-- Untyped.RenamingSubstitution.ren-lift-lifts
d_ren'45'lift'45'lifts_762 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'lift'45'lifts_762 = erased
-- Untyped.RenamingSubstitution.renList-sub
d_renList'45'sub_786 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renList'45'sub_786 = erased
-- Untyped.RenamingSubstitution.ren-sub
d_ren'45'sub_800 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'sub_800 = erased
-- Untyped.RenamingSubstitution.lifts-comp
d_lifts'45'comp_890 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lifts'45'comp_890 = erased
-- Untyped.RenamingSubstitution.subList-comp
d_subList'45'comp_914 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subList'45'comp_914 = erased
-- Untyped.RenamingSubstitution.sub-comp
d_sub'45'comp_928 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'comp_928 = erased
