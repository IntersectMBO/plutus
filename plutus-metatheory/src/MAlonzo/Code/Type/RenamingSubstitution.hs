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

module MAlonzo.Code.Type.RenamingSubstitution where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Utils

-- Type.RenamingSubstitution.Ren
d_Ren_4 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 -> ()
d_Ren_4 = erased
-- Type.RenamingSubstitution.ext
d_ext_18 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Type.T__'8715''8902'__14
d_ext_18 ~v0 ~v1 v2 ~v3 v4 v5 = du_ext_18 v2 v4 v5
du_ext_18 ::
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Type.T__'8715''8902'__14
du_ext_18 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Type.C_Z_16 -> coe MAlonzo.Code.Type.C_Z_16
      MAlonzo.Code.Type.C_S_18 v6
        -> coe MAlonzo.Code.Type.C_S_18 (coe v0 v1 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.RenamingSubstitution.ren
d_ren_28 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_ren_28 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Type.C_'96'_22 v7
        -> coe MAlonzo.Code.Type.C_'96'_22 (coe v2 v3 v7)
      MAlonzo.Code.Type.C_Π_24 v6 v7
        -> coe
             MAlonzo.Code.Type.C_Π_24 v6
             (d_ren_28
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v6))
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v6))
                (coe du_ext_18 (coe v2)) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v7))
      MAlonzo.Code.Type.C__'8658'__26 v6 v7
        -> coe
             MAlonzo.Code.Type.C__'8658'__26
             (d_ren_28
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v6))
             (d_ren_28
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v7))
      MAlonzo.Code.Type.C_ƛ_28 v8
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'8658'__760 v9 v10
               -> coe
                    MAlonzo.Code.Type.C_ƛ_28
                    (d_ren_28
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v9))
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v9))
                       (coe du_ext_18 (coe v2)) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Type.C__'183'__30 v6 v8 v9
        -> coe
             MAlonzo.Code.Type.C__'183'__30 v6
             (d_ren_28
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Utils.C__'8658'__760 (coe v6) (coe v3)) (coe v8))
             (d_ren_28 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
      MAlonzo.Code.Type.C_μ_32 v6 v7 v8
        -> coe
             MAlonzo.Code.Type.C_μ_32 v6
             (d_ren_28
                (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Utils.C__'8658'__760
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__760 (coe v6)
                      (coe MAlonzo.Code.Utils.C_'42'_756))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__760 (coe v6)
                      (coe MAlonzo.Code.Utils.C_'42'_756)))
                (coe v7))
             (d_ren_28 (coe v0) (coe v1) (coe v2) (coe v6) (coe v8))
      MAlonzo.Code.Type.C_'94'_34 v7
        -> coe MAlonzo.Code.Type.C_'94'_34 v7
      MAlonzo.Code.Type.C_con_36 v6
        -> coe
             MAlonzo.Code.Type.C_con_36
             (d_ren_28
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'9839'_758)
                (coe v6))
      MAlonzo.Code.Type.C_SOP_40 v6 v7
        -> coe
             MAlonzo.Code.Type.C_SOP_40 v6
             (coe
                du_ren'45'VecList_38 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Utils.C_'42'_756) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.RenamingSubstitution.ren-List
d_ren'45'List_32 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  [MAlonzo.Code.Type.T__'8866''8902'__20]
d_ren'45'List_32 v0 v1 v2 v3 v4
  = case coe v4 of
      [] -> coe v4
      (:) v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_ren_28 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
             (coe d_ren'45'List_32 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.RenamingSubstitution.ren-VecList
d_ren'45'VecList_38 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  Integer ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_ren'45'VecList_38 v0 v1 v2 ~v3 v4 v5
  = du_ren'45'VecList_38 v0 v1 v2 v4 v5
du_ren'45'VecList_38 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_ren'45'VecList_38 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe v4
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
        -> coe
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38
             (d_ren'45'List_32 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
             (coe
                du_ren'45'VecList_38 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.RenamingSubstitution.weaken
d_weaken_98 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_weaken_98 v0 v1 v2
  = coe
      d_ren_28 (coe v0)
      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v2))
      (coe (\ v3 -> coe MAlonzo.Code.Type.C_S_18)) (coe v1)
-- Type.RenamingSubstitution.ext-id
d_ext'45'id_102 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'id_102 = erased
-- Type.RenamingSubstitution.ext-cong
d_ext'45'cong_116 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'cong_116 = erased
-- Type.RenamingSubstitution.ren-cong
d_ren'45'cong_132 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'cong_132 = erased
-- Type.RenamingSubstitution.ren-cong-List
d_ren'45'cong'45'List_142 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'cong'45'List_142 = erased
-- Type.RenamingSubstitution.ren-cong-VecList
d_ren'45'cong'45'VecList_154 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'cong'45'VecList_154 = erased
-- Type.RenamingSubstitution.ren-id
d_ren'45'id_216 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'id_216 = erased
-- Type.RenamingSubstitution.ren-id-List
d_ren'45'id'45'List_220 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'id'45'List_220 = erased
-- Type.RenamingSubstitution.ren-id-VecList
d_ren'45'id'45'VecList_226 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'id'45'VecList_226 = erased
-- Type.RenamingSubstitution.ext-comp
d_ext'45'comp_266 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'comp_266 = erased
-- Type.RenamingSubstitution.ren-comp
d_ren'45'comp_274 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'comp_274 = erased
-- Type.RenamingSubstitution.ren-comp-List
d_ren'45'comp'45'List_280 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'comp'45'List_280 = erased
-- Type.RenamingSubstitution.ren-comp-VecList
d_ren'45'comp'45'VecList_288 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  Integer ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'comp'45'VecList_288 = erased
-- Type.RenamingSubstitution.Sub
d_Sub_322 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 -> ()
d_Sub_322 = erased
-- Type.RenamingSubstitution.exts
d_exts_336 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_exts_336 ~v0 v1 v2 v3 v4 v5 = du_exts_336 v1 v2 v3 v4 v5
du_exts_336 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
du_exts_336 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Type.C_Z_16
        -> coe MAlonzo.Code.Type.C_'96'_22 (coe MAlonzo.Code.Type.C_Z_16)
      MAlonzo.Code.Type.C_S_18 v8
        -> coe d_weaken_98 v0 v3 v2 (coe v1 v3 v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.RenamingSubstitution.sub
d_sub_346 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_sub_346 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Type.C_'96'_22 v7 -> coe v2 v3 v7
      MAlonzo.Code.Type.C_Π_24 v6 v7
        -> coe
             MAlonzo.Code.Type.C_Π_24 v6
             (d_sub_346
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v6))
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v6))
                (coe du_exts_336 (coe v1) (coe v2) (coe v6))
                (coe MAlonzo.Code.Utils.C_'42'_756) (coe v7))
      MAlonzo.Code.Type.C__'8658'__26 v6 v7
        -> coe
             MAlonzo.Code.Type.C__'8658'__26
             (d_sub_346
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v6))
             (d_sub_346
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v7))
      MAlonzo.Code.Type.C_ƛ_28 v8
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'8658'__760 v9 v10
               -> coe
                    MAlonzo.Code.Type.C_ƛ_28
                    (d_sub_346
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v9))
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v9))
                       (coe du_exts_336 (coe v1) (coe v2) (coe v9)) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Type.C__'183'__30 v6 v8 v9
        -> coe
             MAlonzo.Code.Type.C__'183'__30 v6
             (d_sub_346
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Utils.C__'8658'__760 (coe v6) (coe v3)) (coe v8))
             (d_sub_346 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
      MAlonzo.Code.Type.C_μ_32 v6 v7 v8
        -> coe
             MAlonzo.Code.Type.C_μ_32 v6
             (d_sub_346
                (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Utils.C__'8658'__760
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__760 (coe v6)
                      (coe MAlonzo.Code.Utils.C_'42'_756))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__760 (coe v6)
                      (coe MAlonzo.Code.Utils.C_'42'_756)))
                (coe v7))
             (d_sub_346 (coe v0) (coe v1) (coe v2) (coe v6) (coe v8))
      MAlonzo.Code.Type.C_'94'_34 v7
        -> coe MAlonzo.Code.Type.C_'94'_34 v7
      MAlonzo.Code.Type.C_con_36 v6
        -> coe
             MAlonzo.Code.Type.C_con_36
             (d_sub_346
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'9839'_758)
                (coe v6))
      MAlonzo.Code.Type.C_SOP_40 v6 v7
        -> coe
             MAlonzo.Code.Type.C_SOP_40 v6
             (coe
                du_sub'45'VecList_356 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Utils.C_'42'_756) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.RenamingSubstitution.sub-List
d_sub'45'List_350 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  [MAlonzo.Code.Type.T__'8866''8902'__20]
d_sub'45'List_350 v0 v1 v2 v3 v4
  = case coe v4 of
      [] -> coe v4
      (:) v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_sub_346 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
             (coe
                d_sub'45'List_350 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.RenamingSubstitution.sub-VecList
d_sub'45'VecList_356 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  Integer ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_sub'45'VecList_356 v0 v1 v2 ~v3 v4 v5
  = du_sub'45'VecList_356 v0 v1 v2 v4 v5
du_sub'45'VecList_356 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_sub'45'VecList_356 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe v4
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
        -> coe
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38
             (d_sub'45'List_350 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
             (coe
                du_sub'45'VecList_356 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.RenamingSubstitution.sub-cons
d_sub'45'cons_420 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_sub'45'cons_420 ~v0 ~v1 v2 ~v3 v4 v5 v6
  = du_sub'45'cons_420 v2 v4 v5 v6
du_sub'45'cons_420 ::
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
du_sub'45'cons_420 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Type.C_Z_16 -> coe v1
      MAlonzo.Code.Type.C_S_18 v7 -> coe v0 v2 v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.RenamingSubstitution._[_]
d__'91'_'93'_432 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d__'91'_'93'_432 v0 v1 v2 v3 v4
  = coe
      d_sub_346
      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v1)) (coe v0)
      (coe
         du_sub'45'cons_420 (\ v5 v6 -> coe MAlonzo.Code.Type.C_'96'_22 v6)
         (coe v4))
      (coe v2) (coe v3)
-- Type.RenamingSubstitution.exts-id
d_exts'45'id_440 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exts'45'id_440 = erased
-- Type.RenamingSubstitution.exts-cong
d_exts'45'cong_454 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exts'45'cong_454 = erased
-- Type.RenamingSubstitution.sub-cong
d_sub'45'cong_470 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'cong_470 = erased
-- Type.RenamingSubstitution.sub-cong-List
d_sub'45'cong'45'List_480 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'cong'45'List_480 = erased
-- Type.RenamingSubstitution.sub-cong-VecList
d_sub'45'cong'45'VecList_492 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'cong'45'VecList_492 = erased
-- Type.RenamingSubstitution.sub-id
d_sub'45'id_554 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'id_554 = erased
-- Type.RenamingSubstitution.sub-id-List
d_sub'45'id'45'List_558 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'id'45'List_558 = erased
-- Type.RenamingSubstitution.sub-id-VecList
d_sub'45'id'45'VecList_564 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'id'45'VecList_564 = erased
-- Type.RenamingSubstitution.exts-ext
d_exts'45'ext_604 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exts'45'ext_604 = erased
-- Type.RenamingSubstitution.sub-ren
d_sub'45'ren_612 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'ren_612 = erased
-- Type.RenamingSubstitution.sub-ren-List
d_sub'45'ren'45'List_618 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'ren'45'List_618 = erased
-- Type.RenamingSubstitution.sub-ren-VecList
d_sub'45'ren'45'VecList_626 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  Integer ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'ren'45'VecList_626 = erased
-- Type.RenamingSubstitution.ren-ext-exts
d_ren'45'ext'45'exts_666 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'ext'45'exts_666 = erased
-- Type.RenamingSubstitution.ren-sub
d_ren'45'sub_674 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'sub_674 = erased
-- Type.RenamingSubstitution.ren-sub-List
d_ren'45'sub'45'List_680 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'sub'45'List_680 = erased
-- Type.RenamingSubstitution.ren-sub-VecList
d_ren'45'sub'45'VecList_688 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  Integer ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'sub'45'VecList_688 = erased
-- Type.RenamingSubstitution.extscomp
d_extscomp_728 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extscomp_728 = erased
-- Type.RenamingSubstitution.sub-comp
d_sub'45'comp_738 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'comp_738 = erased
-- Type.RenamingSubstitution.sub-com-List
d_sub'45'com'45'List_744 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'com'45'List_744 = erased
-- Type.RenamingSubstitution.sub-com-VecList
d_sub'45'com'45'VecList_752 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  Integer ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'com'45'VecList_752 = erased
-- Type.RenamingSubstitution.ren-sub-cons
d_ren'45'sub'45'cons_792 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'sub'45'cons_792 = erased
-- Type.RenamingSubstitution.sub-sub-cons
d_sub'45'sub'45'cons_810 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'sub'45'cons_810 = erased
-- Type.RenamingSubstitution.ren-μ
d_ren'45'μ_828 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'μ_828 = erased
-- Type.RenamingSubstitution.ren-Π
d_ren'45'Π_844 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'Π_844 = erased
-- Type.RenamingSubstitution.sub-μ
d_sub'45'μ_858 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'μ_858 = erased
-- Type.RenamingSubstitution.sub-Π
d_sub'45'Π_874 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'Π_874 = erased
-- Type.RenamingSubstitution.sub-∅
d_sub'45''8709'_886 ::
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45''8709'_886 = erased
-- Type.RenamingSubstitution.sub∅
d_sub'8709'_896 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_sub'8709'_896 v0 v1 v2
  = coe
      d_sub_346 (coe MAlonzo.Code.Type.C_'8709'_4) (coe v0) erased
      (coe v1) (coe v2)
-- Type.RenamingSubstitution.sub∅-ren
d_sub'8709''45'ren_906 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'8709''45'ren_906 = erased
-- Type.RenamingSubstitution.sub∅-sub
d_sub'8709''45'sub_918 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'8709''45'sub_918 = erased
-- Type.RenamingSubstitution.lookup-ren-VecList
d_lookup'45'ren'45'VecList_932 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'ren'45'VecList_932 = erased
-- Type.RenamingSubstitution.lookup-sub-VecList
d_lookup'45'sub'45'VecList_950 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'sub'45'VecList_950 = erased
