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

module MAlonzo.Code.Untyped.RenamingSubstitution where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.List qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Untyped qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Untyped.RenamingSubstitution.Ren
d_Ren_4 :: () -> () -> ()
d_Ren_4 = erased
-- Untyped.RenamingSubstitution.lift
d_lift_14 ::
  () -> () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_lift_14 ~v0 ~v1 v2 v3 = du_lift_14 v2 v3
du_lift_14 ::
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_lift_14 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.renList
d_renList_26 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_renList_26 ~v0 ~v1 v2 v3 = du_renList_26 v2 v3
du_renList_26 ::
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
du_renList_26 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe du_ren_32 (coe v0) (coe v2))
             (coe du_renList_26 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.ren
d_ren_32 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_ren_32 ~v0 ~v1 v2 v3 = du_ren_32 v2 v3
du_ren_32 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_ren_32 v0 v1
  = case coe v1 of
      MAlonzo.Code.Untyped.C_'96'_18 v2
        -> coe MAlonzo.Code.Untyped.C_'96'_18 (coe v0 v2)
      MAlonzo.Code.Untyped.C_ƛ_20 v2
        -> coe
             MAlonzo.Code.Untyped.C_ƛ_20
             (coe du_ren_32 (coe du_lift_14 (coe v0)) (coe v2))
      MAlonzo.Code.Untyped.C__'183'__22 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22 (coe du_ren_32 (coe v0) (coe v2))
             (coe du_ren_32 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_force_24 v2
        -> coe
             MAlonzo.Code.Untyped.C_force_24 (coe du_ren_32 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_delay_26 v2
        -> coe
             MAlonzo.Code.Untyped.C_delay_26 (coe du_ren_32 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_con_28 v2 -> coe v1
      MAlonzo.Code.Untyped.C_constr_34 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C_constr_34 (coe v2)
             (coe du_renList_26 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_case_40 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C_case_40 (coe du_ren_32 (coe v0) (coe v2))
             (coe du_renList_26 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_builtin_44 v2 -> coe v1
      MAlonzo.Code.Untyped.C_error_46 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.weaken
d_weaken_88 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_weaken_88 ~v0 v1 = du_weaken_88 v1
du_weaken_88 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_weaken_88 v0
  = coe
      du_ren_32 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16) (coe v0)
-- Untyped.RenamingSubstitution.lift-cong
d_lift'45'cong_104 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'45'cong_104 = erased
-- Untyped.RenamingSubstitution.renList-cong
d_renList'45'cong_124 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renList'45'cong_124 = erased
-- Untyped.RenamingSubstitution.ren-cong
d_ren'45'cong_138 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'cong_138 = erased
-- Untyped.RenamingSubstitution.lift-id
d_lift'45'id_196 ::
  () ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'45'id_196 = erased
-- Untyped.RenamingSubstitution.lift-comp
d_lift'45'comp_212 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'45'comp_212 = erased
-- Untyped.RenamingSubstitution.renList-id
d_renList'45'id_228 ::
  () ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renList'45'id_228 = erased
-- Untyped.RenamingSubstitution.ren-id
d_ren'45'id_234 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'id_234 = erased
-- Untyped.RenamingSubstitution.renList-comp
d_renList'45'comp_276 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renList'45'comp_276 = erased
-- Untyped.RenamingSubstitution.ren-comp
d_ren'45'comp_290 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'comp_290 = erased
-- Untyped.RenamingSubstitution.Sub
d_Sub_368 :: () -> () -> ()
d_Sub_368 = erased
-- Untyped.RenamingSubstitution.lifts
d_lifts_378 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  Maybe AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14
d_lifts_378 ~v0 ~v1 v2 v3 = du_lifts_378 v2 v3
du_lifts_378 ::
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  Maybe AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14
du_lifts_378 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             du_ren_32 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16)
             (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Untyped.C_'96'_18 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.subList
d_subList_390 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_subList_390 ~v0 ~v1 v2 v3 = du_subList_390 v2 v3
du_subList_390 ::
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
du_subList_390 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe du_sub_396 (coe v0) (coe v2))
             (coe du_subList_390 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.sub
d_sub_396 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_sub_396 ~v0 ~v1 v2 v3 = du_sub_396 v2 v3
du_sub_396 ::
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_sub_396 v0 v1
  = case coe v1 of
      MAlonzo.Code.Untyped.C_'96'_18 v2 -> coe v0 v2
      MAlonzo.Code.Untyped.C_ƛ_20 v2
        -> coe
             MAlonzo.Code.Untyped.C_ƛ_20
             (coe du_sub_396 (coe du_lifts_378 (coe v0)) (coe v2))
      MAlonzo.Code.Untyped.C__'183'__22 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22
             (coe du_sub_396 (coe v0) (coe v2))
             (coe du_sub_396 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_force_24 v2
        -> coe
             MAlonzo.Code.Untyped.C_force_24 (coe du_sub_396 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_delay_26 v2
        -> coe
             MAlonzo.Code.Untyped.C_delay_26 (coe du_sub_396 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_con_28 v2 -> coe v1
      MAlonzo.Code.Untyped.C_constr_34 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C_constr_34 (coe v2)
             (coe du_subList_390 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_case_40 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C_case_40 (coe du_sub_396 (coe v0) (coe v2))
             (coe du_subList_390 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_builtin_44 v2 -> coe v1
      MAlonzo.Code.Untyped.C_error_46 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution.extend
d_extend_454 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14
d_extend_454 ~v0 ~v1 v2 v3 v4 = du_extend_454 v2 v3 v4
du_extend_454 ::
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14
du_extend_454 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3 -> coe v0 v3
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Untyped.RenamingSubstitution._[_]
d__'91'_'93'_468 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d__'91'_'93'_468 ~v0 v1 v2 = du__'91'_'93'_468 v1 v2
du__'91'_'93'_468 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du__'91'_'93'_468 v0 v1
  = coe
      du_sub_396
      (coe du_extend_454 (coe MAlonzo.Code.Untyped.C_'96'_18) (coe v1))
      (coe v0)
-- Untyped.RenamingSubstitution.lifts-cong
d_lifts'45'cong_486 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lifts'45'cong_486 = erased
-- Untyped.RenamingSubstitution.subList-cong
d_subList'45'cong_506 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subList'45'cong_506 = erased
-- Untyped.RenamingSubstitution.sub-cong
d_sub'45'cong_520 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'cong_520 = erased
-- Untyped.RenamingSubstitution.lifts-id
d_lifts'45'id_578 ::
  () ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lifts'45'id_578 = erased
-- Untyped.RenamingSubstitution.subList-id
d_subList'45'id_586 ::
  () ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subList'45'id_586 = erased
-- Untyped.RenamingSubstitution.sub-id
d_sub'45'id_592 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'id_592 = erased
-- Untyped.RenamingSubstitution.lifts-lift
d_lifts'45'lift_634 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lifts'45'lift_634 = erased
-- Untyped.RenamingSubstitution.subList-ren
d_subList'45'ren_658 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subList'45'ren_658 = erased
-- Untyped.RenamingSubstitution.sub-ren
d_sub'45'ren_672 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'ren_672 = erased
-- Untyped.RenamingSubstitution.ren-lift-lifts
d_ren'45'lift'45'lifts_762 ::
  () ->
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'lift'45'lifts_762 = erased
-- Untyped.RenamingSubstitution.renList-sub
d_renList'45'sub_786 ::
  () ->
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renList'45'sub_786 = erased
-- Untyped.RenamingSubstitution.ren-sub
d_ren'45'sub_800 ::
  () ->
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'sub_800 = erased
-- Untyped.RenamingSubstitution.lifts-comp
d_lifts'45'comp_890 ::
  () ->
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lifts'45'comp_890 = erased
-- Untyped.RenamingSubstitution.subList-comp
d_subList'45'comp_914 ::
  () ->
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subList'45'comp_914 = erased
-- Untyped.RenamingSubstitution.sub-comp
d_sub'45'comp_928 ::
  () ->
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  (AgdaAny -> MAlonzo.Code.Untyped.T__'8866'_14) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'comp_928 = erased
