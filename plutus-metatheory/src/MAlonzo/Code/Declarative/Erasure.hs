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

module MAlonzo.Code.Declarative.Erasure where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Declarative
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Declarative.Erasure.len
d_len_6 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 -> Integer
d_len_6 v0 v1
  = case coe v1 of
      MAlonzo.Code.Declarative.C_'8709'_18 -> coe (0 :: Integer)
      MAlonzo.Code.Declarative.C__'44''8902'__22 v3
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v5 v6
               -> coe d_len_6 (coe v5) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'44'__26 v3 v4
        -> coe addInt (coe (1 :: Integer)) (coe d_len_6 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.Erasure.lenI
d_lenI_18 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 -> Integer
d_lenI_18 v0 v1
  = case coe v1 of
      MAlonzo.Code.Declarative.C_'8709'_18 -> coe (0 :: Integer)
      MAlonzo.Code.Declarative.C__'44''8902'__22 v3
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v5 v6
               -> coe
                    addInt (coe (1 :: Integer)) (coe d_lenI_18 (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'44'__26 v3 v4
        -> coe
             addInt (coe (1 :: Integer)) (coe d_lenI_18 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.Erasure.len⋆
d_len'8902'_28 :: MAlonzo.Code.Type.T_Ctx'8902'_2 -> Integer
d_len'8902'_28 v0
  = case coe v0 of
      MAlonzo.Code.Type.C_'8709'_4 -> coe (0 :: Integer)
      MAlonzo.Code.Type.C__'44''8902'__6 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe d_len'8902'_28 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.Erasure.eraseVar
d_eraseVar_40 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_eraseVar_40 v0 v1 ~v2 v3 = du_eraseVar_40 v0 v1 v3
du_eraseVar_40 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_eraseVar_40 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Declarative.C_Z_36
        -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      MAlonzo.Code.Declarative.C_S_38 v7
        -> case coe v1 of
             MAlonzo.Code.Declarative.C__'44'__26 v9 v10
               -> coe
                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                    (coe du_eraseVar_40 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_T_40 v5 v7
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Declarative.C__'44''8902'__22 v11
                      -> coe du_eraseVar_40 (coe v8) (coe v11) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.Erasure.eraseTC
d_eraseTC_48 ::
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  AgdaAny -> MAlonzo.Code.RawU.T_TmCon_202
d_eraseTC_48 v0 v1
  = coe
      MAlonzo.Code.RawU.C_tmCon_206
      (coe MAlonzo.Code.Declarative.d_ty2TyTag_74 (coe v0)) (coe v1)
-- Declarative.Erasure.erase
d_erase_60 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_erase_60 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Declarative.C_'96'_114 v5
        -> coe
             MAlonzo.Code.Untyped.C_'96'_18
             (coe du_eraseVar_40 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Declarative.C_ƛ_116 v6
        -> case coe v2 of
             MAlonzo.Code.Type.C__'8658'__26 v8 v9
               -> coe
                    MAlonzo.Code.Untyped.C_ƛ_20
                    (coe
                       d_erase_60 (coe v0)
                       (coe MAlonzo.Code.Declarative.C__'44'__26 v1 v8) (coe v9) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'183'__118 v4 v6 v7
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22
             (coe
                d_erase_60 (coe v0) (coe v1)
                (coe MAlonzo.Code.Type.C__'8658'__26 v4 v2) (coe v6))
             (coe d_erase_60 (coe v0) (coe v1) (coe v4) (coe v7))
      MAlonzo.Code.Declarative.C_Λ_120 v6
        -> case coe v2 of
             MAlonzo.Code.Type.C_Π_24 v8 v9
               -> coe
                    MAlonzo.Code.Untyped.C_delay_26
                    (coe
                       d_erase_60
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                       (coe MAlonzo.Code.Declarative.C__'44''8902'__22 v1) (coe v9)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'183''8902'__124 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Untyped.C_force_24
             (coe
                d_erase_60 (coe v0) (coe v1) (coe MAlonzo.Code.Type.C_Π_24 v4 v5)
                (coe v6))
      MAlonzo.Code.Declarative.C_wrap_130 v7
        -> case coe v2 of
             MAlonzo.Code.Type.C_μ_32 v9 v10 v11
               -> coe
                    d_erase_60 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Type.C__'183'__30 v9
                       (coe
                          MAlonzo.Code.Type.C__'183'__30
                          (coe
                             MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                             (coe MAlonzo.Code.Utils.C_'42'_756))
                          v10
                          (coe
                             MAlonzo.Code.Type.C_ƛ_28
                             (coe
                                MAlonzo.Code.Type.C_μ_32 v9
                                (coe
                                   MAlonzo.Code.Type.RenamingSubstitution.d_weaken_98 v0
                                   (coe
                                      MAlonzo.Code.Utils.C__'8658'__760
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                         (coe MAlonzo.Code.Utils.C_'42'_756))
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                         (coe MAlonzo.Code.Utils.C_'42'_756)))
                                   v9 v10)
                                (coe MAlonzo.Code.Type.C_'96'_22 (coe MAlonzo.Code.Type.C_Z_16)))))
                       v11)
                    (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_unwrap_132 v7
        -> case coe v2 of
             MAlonzo.Code.Type.C__'183'__30 v9 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Type.C__'183'__30 v14 v16 v17
                      -> coe
                           d_erase_60 (coe v0) (coe v1)
                           (coe MAlonzo.Code.Type.C_μ_32 v9 v16 v12) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_constr_142 v5 v7 v9
        -> coe
             MAlonzo.Code.Untyped.C_constr_34
             (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v5))
             (coe d_erase'45'ConstrArgs_82 (coe v0) (coe v1) (coe v7) (coe v9))
      MAlonzo.Code.Declarative.C_case_154 v4 v5 v7 v8
        -> coe
             MAlonzo.Code.Untyped.C_case_40
             (coe
                d_erase_60 (coe v0) (coe v1) (coe MAlonzo.Code.Type.C_SOP_40 v4 v5)
                (coe v7))
             (coe
                du_erase'45'Cases_100 (coe v0) (coe v1) (coe v2) (coe v5) (coe v8))
      MAlonzo.Code.Declarative.C_conv_156 v4 v6 v7
        -> coe d_erase_60 (coe v0) (coe v1) (coe v4) (coe v7)
      MAlonzo.Code.Declarative.C_con_162 v4 v6 v7
        -> coe
             MAlonzo.Code.Untyped.C_con_28 (coe d_eraseTC_48 (coe v4) (coe v6))
      MAlonzo.Code.Declarative.C_builtin_166 v4
        -> coe MAlonzo.Code.Untyped.C_builtin_44 (coe v4)
      MAlonzo.Code.Declarative.C_error_170
        -> coe MAlonzo.Code.Untyped.C_error_46
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.Erasure.erase-Sub
d_erase'45'Sub_72 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8866'__110) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_erase'45'Sub_72 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_erase_60 (coe v1) (coe v3)
      (coe
         MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
         (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
         (coe d_backVar'8902'_156 (coe v0) (coe v2) (coe v6)))
      (coe
         v5 (d_backVar'8902'_156 (coe v0) (coe v2) (coe v6))
         (d_backVar_180 (coe v0) (coe v2) (coe v6)))
-- Declarative.Erasure.erase-ConstrArgs
d_erase'45'ConstrArgs_82 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_erase'45'ConstrArgs_82 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Utils.List.C_'91''93'_308
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Utils.List.C__'8759'__314 v6 v7
        -> case coe v2 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe d_erase_60 (coe v0) (coe v1) (coe v8) (coe v6))
                    (coe d_erase'45'ConstrArgs_82 (coe v0) (coe v1) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.Erasure.erase-Cases
d_erase'45'Cases_100 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Declarative.T_Cases_104 ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_erase'45'Cases_100 v0 v1 v2 ~v3 v4 v5
  = du_erase'45'Cases_100 v0 v1 v2 v4 v5
du_erase'45'Cases_100 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Declarative.T_Cases_104 ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
du_erase'45'Cases_100 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Declarative.C_'91''93'_180
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Declarative.C__'8759'__192 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       d_erase_60 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Declarative.du_mkCaseType_82 (coe v2) (coe v11))
                       (coe v8))
                    (coe
                       du_erase'45'Cases_100 (coe v0) (coe v1) (coe v2) (coe v12)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.Erasure.backVar⋆
d_backVar'8902'_156 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_backVar'8902'_156 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Declarative.C__'44''8902'__22 v4
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v6 v7
               -> coe
                    MAlonzo.Code.Type.RenamingSubstitution.d_weaken_98 v6
                    (coe MAlonzo.Code.Utils.C_'42'_756) v7
                    (d_backVar'8902'_156 (coe v6) (coe v4) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'44'__26 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v5
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe d_backVar'8902'_156 (coe v0) (coe v4) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.Erasure.backVar
d_backVar_180 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Declarative.T__'8715'__34
d_backVar_180 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Declarative.C__'44''8902'__22 v4
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v6 v7
               -> coe
                    MAlonzo.Code.Declarative.C_T_40
                    (d_backVar'8902'_156 (coe v6) (coe v4) (coe v2))
                    (d_backVar_180 (coe v6) (coe v4) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'44'__26 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Declarative.C_Z_36
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    MAlonzo.Code.Declarative.C_S_38
                    (d_backVar_180 (coe v0) (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
