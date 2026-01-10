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

module MAlonzo.Code.Type.Equality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Utils

-- Type.Equality._[≡]β_
d__'91''8801''93'β__4 a0 a1 a2 = ()
data T__'91''8801''93'β__4
  = C_nil'91''8801''93'β_50 |
    C_cons'91''8801''93'β_60 T__'8801'β__10 T__'91''8801''93'β__4
-- Type.Equality._⟨[≡]⟩β_
d__'10216''91''8801''93''10217'β__8 a0 a1 a2 a3 = ()
data T__'10216''91''8801''93''10217'β__8
  = C_nil'10216''91''8801''93''10217'β_62 |
    C_cons'10216''91''8801''93''10217'β_74 T__'91''8801''93'β__4
                                           T__'10216''91''8801''93''10217'β__8
-- Type.Equality._≡β_
d__'8801'β__10 a0 a1 a2 a3 = ()
data T__'8801'β__10
  = C_refl'8801'β_14 | C_sym'8801'β_16 T__'8801'β__10 |
    C_trans'8801'β_18 MAlonzo.Code.Type.T__'8866''8902'__20
                      T__'8801'β__10 T__'8801'β__10 |
    C_'8658''8801'β_20 T__'8801'β__10 T__'8801'β__10 |
    C_Π'8801'β_22 T__'8801'β__10 | C_ƛ'8801'β_24 T__'8801'β__10 |
    C_'183''8801'β_26 T__'8801'β__10 T__'8801'β__10 |
    C_μ'8801'β_28 T__'8801'β__10 T__'8801'β__10 |
    C_con'8801'β_34 T__'8801'β__10 |
    C_SOP'8801'β_42 T__'10216''91''8801''93''10217'β__8 | C_β'8801'β_48
-- Type.Equality.≡2β
d_'8801'2β_76 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8801'β__10
d_'8801'2β_76 ~v0 ~v1 ~v2 ~v3 ~v4 = du_'8801'2β_76
du_'8801'2β_76 :: T__'8801'β__10
du_'8801'2β_76 = coe C_refl'8801'β_14
-- Type.Equality.ren≡β
d_ren'8801'β_80 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  T__'8801'β__10 -> T__'8801'β__10
d_ren'8801'β_80 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_refl'8801'β_14 -> coe C_refl'8801'β_14
      C_sym'8801'β_16 v11
        -> coe
             C_sym'8801'β_16
             (d_ren'8801'β_80
                (coe v0) (coe v1) (coe v2) (coe v4) (coe v3) (coe v5) (coe v11))
      C_trans'8801'β_18 v10 v12 v13
        -> coe
             C_trans'8801'β_18
             (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                (coe v0) (coe v1) (coe v5) (coe v2) (coe v10))
             (d_ren'8801'β_80
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v5) (coe v12))
             (d_ren'8801'β_80
                (coe v0) (coe v1) (coe v2) (coe v10) (coe v4) (coe v5) (coe v13))
      C_'8658''8801'β_20 v12 v13
        -> case coe v3 of
             MAlonzo.Code.Type.C__'8658'__26 v15 v16
               -> case coe v4 of
                    MAlonzo.Code.Type.C__'8658'__26 v18 v19
                      -> coe
                           C_'8658''8801'β_20
                           (d_ren'8801'β_80
                              (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v15)
                              (coe v18) (coe v5) (coe v12))
                           (d_ren'8801'β_80
                              (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v16)
                              (coe v19) (coe v5) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Π'8801'β_22 v11
        -> case coe v3 of
             MAlonzo.Code.Type.C_Π_24 v13 v14
               -> case coe v4 of
                    MAlonzo.Code.Type.C_Π_24 v16 v17
                      -> coe
                           C_Π'8801'β_22
                           (d_ren'8801'β_80
                              (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                              (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                              (coe MAlonzo.Code.Utils.C_'42'_704) (coe v14) (coe v17)
                              (coe MAlonzo.Code.Type.RenamingSubstitution.du_ext_18 (coe v5))
                              (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ƛ'8801'β_24 v12
        -> case coe v2 of
             MAlonzo.Code.Utils.C__'8658'__708 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Type.C_ƛ_28 v18
                      -> case coe v4 of
                           MAlonzo.Code.Type.C_ƛ_28 v22
                             -> coe
                                  C_ƛ'8801'β_24
                                  (d_ren'8801'β_80
                                     (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                                     (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                                     (coe v14) (coe v18) (coe v22)
                                     (coe MAlonzo.Code.Type.RenamingSubstitution.du_ext_18 (coe v5))
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'183''8801'β_26 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Type.C__'183'__30 v17 v19 v20
               -> case coe v4 of
                    MAlonzo.Code.Type.C__'183'__30 v22 v24 v25
                      -> coe
                           C_'183''8801'β_26
                           (d_ren'8801'β_80
                              (coe v0) (coe v1)
                              (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v17) (coe v2))
                              (coe v19) (coe v24) (coe v5) (coe v14))
                           (d_ren'8801'β_80
                              (coe v0) (coe v1) (coe v17) (coe v20) (coe v25) (coe v5) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'8801'β_28 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Type.C_μ_32 v16 v17 v18
               -> case coe v4 of
                    MAlonzo.Code.Type.C_μ_32 v20 v21 v22
                      -> coe
                           C_μ'8801'β_28
                           (d_ren'8801'β_80
                              (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Utils.C__'8658'__708
                                 (coe
                                    MAlonzo.Code.Utils.C__'8658'__708 (coe v16)
                                    (coe MAlonzo.Code.Utils.C_'42'_704))
                                 (coe
                                    MAlonzo.Code.Utils.C__'8658'__708 (coe v16)
                                    (coe MAlonzo.Code.Utils.C_'42'_704)))
                              (coe v17) (coe v21) (coe v5) (coe v13))
                           (d_ren'8801'β_80
                              (coe v0) (coe v1) (coe v16) (coe v18) (coe v22) (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_con'8801'β_34 v10
        -> case coe v3 of
             MAlonzo.Code.Type.C_con_36 v12
               -> case coe v4 of
                    MAlonzo.Code.Type.C_con_36 v14
                      -> coe
                           C_con'8801'β_34
                           (d_ren'8801'β_80
                              (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'9839'_706) (coe v12)
                              (coe v14) (coe v5) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_SOP'8801'β_42 v11
        -> case coe v3 of
             MAlonzo.Code.Type.C_SOP_40 v13 v14
               -> case coe v4 of
                    MAlonzo.Code.Type.C_SOP_40 v16 v17
                      -> coe
                           C_SOP'8801'β_42
                           (coe
                              du_ren'8801'β'45'VecList_98 (coe v0) (coe v1) (coe v14) (coe v17)
                              (coe v5) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_β'8801'β_48
        -> case coe v3 of
             MAlonzo.Code.Type.C__'183'__30 v13 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Type.C_ƛ_28 v20
                      -> coe
                           C_trans'8801'β_18
                           (MAlonzo.Code.Type.RenamingSubstitution.d__'91'_'93'_432
                              (coe v1) (coe v13) (coe v2)
                              (coe
                                 MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                                 (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                                 (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                                 (coe MAlonzo.Code.Type.RenamingSubstitution.du_ext_18 (coe v5))
                                 (coe v2) (coe v20))
                              (coe
                                 MAlonzo.Code.Type.RenamingSubstitution.d_ren_28 (coe v0) (coe v1)
                                 (coe v5) (coe v13) (coe v16)))
                           (coe C_β'8801'β_48) (coe du_'8801'2β_76)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.Equality.ren≡β-List
d_ren'8801'β'45'List_88 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  T__'91''8801''93'β__4 -> T__'91''8801''93'β__4
d_ren'8801'β'45'List_88 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_nil'91''8801''93'β_50 -> coe C_nil'91''8801''93'β_50
      C_cons'91''8801''93'β_60 v11 v12
        -> case coe v2 of
             (:) v13 v14
               -> case coe v3 of
                    (:) v15 v16
                      -> coe
                           C_cons'91''8801''93'β_60
                           (d_ren'8801'β_80
                              (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v13)
                              (coe v15) (coe v4) (coe v11))
                           (d_ren'8801'β'45'List_88
                              (coe v0) (coe v1) (coe v14) (coe v16) (coe v4) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.Equality.ren≡β-VecList
d_ren'8801'β'45'VecList_98 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  T__'10216''91''8801''93''10217'β__8 ->
  T__'10216''91''8801''93''10217'β__8
d_ren'8801'β'45'VecList_98 v0 v1 ~v2 v3 v4 v5 v6
  = du_ren'8801'β'45'VecList_98 v0 v1 v3 v4 v5 v6
du_ren'8801'β'45'VecList_98 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  T__'10216''91''8801''93''10217'β__8 ->
  T__'10216''91''8801''93''10217'β__8
du_ren'8801'β'45'VecList_98 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_nil'10216''91''8801''93''10217'β_62
        -> coe C_nil'10216''91''8801''93''10217'β_62
      C_cons'10216''91''8801''93''10217'β_74 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v18 v19
                      -> coe
                           C_cons'10216''91''8801''93''10217'β_74
                           (d_ren'8801'β'45'List_88
                              (coe v0) (coe v1) (coe v15) (coe v18) (coe v4) (coe v12))
                           (coe
                              du_ren'8801'β'45'VecList_98 (coe v0) (coe v1) (coe v16) (coe v19)
                              (coe v4) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.Equality.sub≡β
d_sub'8801'β_172 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  T__'8801'β__10 -> T__'8801'β__10
d_sub'8801'β_172 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_refl'8801'β_14 -> coe C_refl'8801'β_14
      C_sym'8801'β_16 v11
        -> coe
             C_sym'8801'β_16
             (d_sub'8801'β_172
                (coe v0) (coe v1) (coe v2) (coe v4) (coe v3) (coe v5) (coe v11))
      C_trans'8801'β_18 v10 v12 v13
        -> coe
             C_trans'8801'β_18
             (MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                (coe v0) (coe v1) (coe v5) (coe v2) (coe v10))
             (d_sub'8801'β_172
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v5) (coe v12))
             (d_sub'8801'β_172
                (coe v0) (coe v1) (coe v2) (coe v10) (coe v4) (coe v5) (coe v13))
      C_'8658''8801'β_20 v12 v13
        -> case coe v3 of
             MAlonzo.Code.Type.C__'8658'__26 v15 v16
               -> case coe v4 of
                    MAlonzo.Code.Type.C__'8658'__26 v18 v19
                      -> coe
                           C_'8658''8801'β_20
                           (d_sub'8801'β_172
                              (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v15)
                              (coe v18) (coe v5) (coe v12))
                           (d_sub'8801'β_172
                              (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v16)
                              (coe v19) (coe v5) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Π'8801'β_22 v11
        -> case coe v3 of
             MAlonzo.Code.Type.C_Π_24 v13 v14
               -> case coe v4 of
                    MAlonzo.Code.Type.C_Π_24 v16 v17
                      -> coe
                           C_Π'8801'β_22
                           (d_sub'8801'β_172
                              (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                              (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                              (coe MAlonzo.Code.Utils.C_'42'_704) (coe v14) (coe v17)
                              (coe
                                 MAlonzo.Code.Type.RenamingSubstitution.du_exts_336 (coe v1)
                                 (coe v5) (coe v13))
                              (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ƛ'8801'β_24 v12
        -> case coe v2 of
             MAlonzo.Code.Utils.C__'8658'__708 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Type.C_ƛ_28 v18
                      -> case coe v4 of
                           MAlonzo.Code.Type.C_ƛ_28 v22
                             -> coe
                                  C_ƛ'8801'β_24
                                  (d_sub'8801'β_172
                                     (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                                     (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                                     (coe v14) (coe v18) (coe v22)
                                     (coe
                                        MAlonzo.Code.Type.RenamingSubstitution.du_exts_336 (coe v1)
                                        (coe v5) (coe v13))
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'183''8801'β_26 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Type.C__'183'__30 v17 v19 v20
               -> case coe v4 of
                    MAlonzo.Code.Type.C__'183'__30 v22 v24 v25
                      -> coe
                           C_'183''8801'β_26
                           (d_sub'8801'β_172
                              (coe v0) (coe v1)
                              (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v17) (coe v2))
                              (coe v19) (coe v24) (coe v5) (coe v14))
                           (d_sub'8801'β_172
                              (coe v0) (coe v1) (coe v17) (coe v20) (coe v25) (coe v5) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'8801'β_28 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Type.C_μ_32 v16 v17 v18
               -> case coe v4 of
                    MAlonzo.Code.Type.C_μ_32 v20 v21 v22
                      -> coe
                           C_μ'8801'β_28
                           (d_sub'8801'β_172
                              (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Utils.C__'8658'__708
                                 (coe
                                    MAlonzo.Code.Utils.C__'8658'__708 (coe v16)
                                    (coe MAlonzo.Code.Utils.C_'42'_704))
                                 (coe
                                    MAlonzo.Code.Utils.C__'8658'__708 (coe v16)
                                    (coe MAlonzo.Code.Utils.C_'42'_704)))
                              (coe v17) (coe v21) (coe v5) (coe v13))
                           (d_sub'8801'β_172
                              (coe v0) (coe v1) (coe v16) (coe v18) (coe v22) (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_con'8801'β_34 v10
        -> case coe v3 of
             MAlonzo.Code.Type.C_con_36 v12
               -> case coe v4 of
                    MAlonzo.Code.Type.C_con_36 v14
                      -> coe
                           C_con'8801'β_34
                           (d_sub'8801'β_172
                              (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'9839'_706) (coe v12)
                              (coe v14) (coe v5) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_SOP'8801'β_42 v11
        -> case coe v3 of
             MAlonzo.Code.Type.C_SOP_40 v13 v14
               -> case coe v4 of
                    MAlonzo.Code.Type.C_SOP_40 v16 v17
                      -> coe
                           C_SOP'8801'β_42
                           (coe
                              du_sub'8801'β'45'VecList_190 (coe v0) (coe v1) (coe v14) (coe v17)
                              (coe v5) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_β'8801'β_48
        -> case coe v3 of
             MAlonzo.Code.Type.C__'183'__30 v13 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Type.C_ƛ_28 v20
                      -> coe
                           C_trans'8801'β_18
                           (MAlonzo.Code.Type.RenamingSubstitution.d__'91'_'93'_432
                              (coe v1) (coe v13) (coe v2)
                              (coe
                                 MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                                 (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                                 (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                                 (coe
                                    MAlonzo.Code.Type.RenamingSubstitution.du_exts_336 (coe v1)
                                    (coe v5) (coe v13))
                                 (coe v2) (coe v20))
                              (coe
                                 MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                                 (coe v5) (coe v13) (coe v16)))
                           (coe C_β'8801'β_48) (coe du_'8801'2β_76)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.Equality.sub≡β-List
d_sub'8801'β'45'List_180 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  T__'91''8801''93'β__4 -> T__'91''8801''93'β__4
d_sub'8801'β'45'List_180 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_nil'91''8801''93'β_50 -> coe C_nil'91''8801''93'β_50
      C_cons'91''8801''93'β_60 v11 v12
        -> case coe v2 of
             (:) v13 v14
               -> case coe v3 of
                    (:) v15 v16
                      -> coe
                           C_cons'91''8801''93'β_60
                           (d_sub'8801'β_172
                              (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v13)
                              (coe v15) (coe v4) (coe v11))
                           (d_sub'8801'β'45'List_180
                              (coe v0) (coe v1) (coe v14) (coe v16) (coe v4) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.Equality.sub≡β-VecList
d_sub'8801'β'45'VecList_190 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  T__'10216''91''8801''93''10217'β__8 ->
  T__'10216''91''8801''93''10217'β__8
d_sub'8801'β'45'VecList_190 v0 v1 ~v2 v3 v4 v5 v6
  = du_sub'8801'β'45'VecList_190 v0 v1 v3 v4 v5 v6
du_sub'8801'β'45'VecList_190 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  T__'10216''91''8801''93''10217'β__8 ->
  T__'10216''91''8801''93''10217'β__8
du_sub'8801'β'45'VecList_190 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_nil'10216''91''8801''93''10217'β_62
        -> coe C_nil'10216''91''8801''93''10217'β_62
      C_cons'10216''91''8801''93''10217'β_74 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v18 v19
                      -> coe
                           C_cons'10216''91''8801''93''10217'β_74
                           (d_sub'8801'β'45'List_180
                              (coe v0) (coe v1) (coe v15) (coe v18) (coe v4) (coe v12))
                           (coe
                              du_sub'8801'β'45'VecList_190 (coe v0) (coe v1) (coe v16) (coe v19)
                              (coe v4) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
