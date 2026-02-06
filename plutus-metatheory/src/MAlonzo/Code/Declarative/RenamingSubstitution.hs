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

module MAlonzo.Code.Declarative.RenamingSubstitution where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Declarative
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.Equality
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Declarative.RenamingSubstitution.Ren
d_Ren_8 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  ()
d_Ren_8 = erased
-- Declarative.RenamingSubstitution.ext
d_ext_22 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8715'__34) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Declarative.T__'8715'__34
d_ext_22 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 = du_ext_22 v5 v7 v8
du_ext_22 ::
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8715'__34) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Declarative.T__'8715'__34
du_ext_22 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Declarative.C_Z_36
        -> coe MAlonzo.Code.Declarative.C_Z_36
      MAlonzo.Code.Declarative.C_S_38 v7
        -> coe MAlonzo.Code.Declarative.C_S_38 (coe v0 v1 v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution.ext⋆
d_ext'8902'_34 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8715'__34) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Declarative.T__'8715'__34
d_ext'8902'_34 v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8
  = du_ext'8902'_34 v0 v1 v4 v5 v8
du_ext'8902'_34 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8715'__34) ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Declarative.T__'8715'__34
du_ext'8902'_34 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Declarative.C_T_40 v7 v9
        -> coe
             MAlonzo.Code.Declarative.C_T_40
             (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v7))
             (coe v3 v7 v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution.ren
d_ren_44 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8715'__34) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d_ren_44 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Declarative.C_'96'_114 v9
        -> coe MAlonzo.Code.Declarative.C_'96'_114 (coe v5 v6 v9)
      MAlonzo.Code.Declarative.C_ƛ_116 v10
        -> case coe v6 of
             MAlonzo.Code.Type.C__'8658'__26 v12 v13
               -> coe
                    MAlonzo.Code.Declarative.C_ƛ_116
                    (d_ren_44
                       (coe v0) (coe v1) (coe MAlonzo.Code.Declarative.C__'44'__26 v2 v12)
                       (coe
                          MAlonzo.Code.Declarative.C__'44'__26 v3
                          (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                             (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                             (coe v12)))
                       (coe v4) (coe du_ext_22 (coe v5)) (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'183'__118 v8 v10 v11
        -> coe
             MAlonzo.Code.Declarative.C__'183'__118
             (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v8))
             (d_ren_44
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.C__'8658'__26 v8 v6) (coe v10))
             (d_ren_44
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v8)
                (coe v11))
      MAlonzo.Code.Declarative.C_Λ_120 v10
        -> case coe v6 of
             MAlonzo.Code.Type.C_Π_24 v12 v13
               -> coe
                    MAlonzo.Code.Declarative.C_Λ_120
                    (d_ren_44
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v12))
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v12))
                       (coe MAlonzo.Code.Declarative.C__'44''8902'__22 v2)
                       (coe MAlonzo.Code.Declarative.C__'44''8902'__22 v3)
                       (coe MAlonzo.Code.Type.RenamingSubstitution.du_ext_18 (coe v4))
                       (\ v14 v15 ->
                          coe du_ext'8902'_34 (coe v0) (coe v1) (coe v4) (coe v5) v15)
                       (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'183''8902'__124 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Declarative.C__'183''8902'__124 (coe v8)
             (coe
                MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v8))
                (coe MAlonzo.Code.Type.RenamingSubstitution.du_ext_18 (coe v4))
                (coe MAlonzo.Code.Utils.C_'42'_756) (coe v9))
             (coe
                d_ren_44 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.C_Π_24 v8 v9) (coe v10))
             (coe
                MAlonzo.Code.Type.RenamingSubstitution.d_ren_28 (coe v0) (coe v1)
                (coe v4) (coe v8) (coe v11))
      MAlonzo.Code.Declarative.C_wrap_130 v11
        -> case coe v6 of
             MAlonzo.Code.Type.C_μ_32 v13 v14 v15
               -> coe
                    MAlonzo.Code.Declarative.C_wrap_130
                    (d_ren_44
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Type.C__'183'__30 v13
                          (coe
                             MAlonzo.Code.Type.C__'183'__30
                             (coe
                                MAlonzo.Code.Utils.C__'8658'__760 (coe v13)
                                (coe MAlonzo.Code.Utils.C_'42'_756))
                             v14
                             (coe
                                MAlonzo.Code.Type.C_ƛ_28
                                (coe
                                   MAlonzo.Code.Type.C_μ_32 v13
                                   (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                                      (coe v0)
                                      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                                      (coe (\ v16 -> coe MAlonzo.Code.Type.C_S_18))
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__760
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__760 (coe v13)
                                            (coe MAlonzo.Code.Utils.C_'42'_756))
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__760 (coe v13)
                                            (coe MAlonzo.Code.Utils.C_'42'_756)))
                                      (coe v14))
                                   (coe
                                      MAlonzo.Code.Type.C_'96'_22 (coe MAlonzo.Code.Type.C_Z_16)))))
                          v15)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_unwrap_132 v11
        -> case coe v6 of
             MAlonzo.Code.Type.C__'183'__30 v13 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Type.C__'183'__30 v18 v20 v21
                      -> coe
                           MAlonzo.Code.Declarative.C_unwrap_132
                           (d_ren_44
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                              (coe MAlonzo.Code.Type.C_μ_32 v13 v20 v16) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_constr_142 v9 v11 v13
        -> case coe v6 of
             MAlonzo.Code.Type.C_SOP_40 v15 v16
               -> coe
                    MAlonzo.Code.Declarative.C_constr_142 v9
                    (MAlonzo.Code.Type.RenamingSubstitution.d_ren'45'List_32
                       (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                       (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v9)))
                    (d_ren'45'ConstrArgs_62
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v9))
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_case_154 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Declarative.C_case_154 v8
             (coe
                MAlonzo.Code.Type.RenamingSubstitution.du_ren'45'VecList_38
                (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v9))
             (d_ren_44
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.C_SOP_40 v8 v9) (coe v11))
             (coe
                du_ren'45'Cases_128 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v9) (coe v12))
      MAlonzo.Code.Declarative.C_conv_156 v8 v10 v11
        -> coe
             MAlonzo.Code.Declarative.C_conv_156
             (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v8))
             (MAlonzo.Code.Type.Equality.d_ren'8801'β_80
                (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_756) (coe v8)
                (coe v6) (coe v4) (coe v10))
             (d_ren_44
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v8)
                (coe v11))
      MAlonzo.Code.Declarative.C_con_162 v8 v10 v11
        -> case coe v6 of
             MAlonzo.Code.Type.C_con_36 v13
               -> coe
                    MAlonzo.Code.Declarative.C_con_162 v8 v10
                    (coe
                       MAlonzo.Code.Type.Equality.C_trans'8801'β_18
                       (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                          (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'9839'_758)
                          (coe
                             MAlonzo.Code.Type.RenamingSubstitution.d_sub'8709'_896 (coe v0)
                             (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v8)))
                       (MAlonzo.Code.Type.Equality.d_ren'8801'β_80
                          (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v13)
                          (coe
                             MAlonzo.Code.Type.RenamingSubstitution.d_sub'8709'_896 (coe v0)
                             (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v8))
                          (coe v4) (coe v11))
                       (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_builtin_166 v8 -> coe v7
      MAlonzo.Code.Declarative.C_error_170
        -> coe MAlonzo.Code.Declarative.C_error_170
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution.ren-ConstrArgs
d_ren'45'ConstrArgs_62 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8715'__34) ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
d_ren'45'ConstrArgs_62 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Utils.List.C_'91''93'_308 -> coe v7
      MAlonzo.Code.Utils.List.C__'8759'__314 v10 v11
        -> case coe v6 of
             (:) v12 v13
               -> coe
                    MAlonzo.Code.Utils.List.C__'8759'__314
                    (d_ren_44
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v12)
                       (coe v10))
                    (d_ren'45'ConstrArgs_62
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v13)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution.lem-ren-mkCaseType
d_lem'45'ren'45'mkCaseType_92 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8715'__34) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45'ren'45'mkCaseType_92 = erased
-- Declarative.RenamingSubstitution.ren-Cases
d_ren'45'Cases_128 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8715'__34) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Declarative.T_Cases_104 ->
  MAlonzo.Code.Declarative.T_Cases_104
d_ren'45'Cases_128 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_ren'45'Cases_128 v0 v1 v2 v3 v4 v5 v6 v8 v9
du_ren'45'Cases_128 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8715'__34) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Declarative.T_Cases_104 ->
  MAlonzo.Code.Declarative.T_Cases_104
du_ren'45'Cases_128 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Declarative.C_'91''93'_180 -> coe v8
      MAlonzo.Code.Declarative.C__'8759'__192 v12 v13
        -> case coe v7 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
               -> coe
                    MAlonzo.Code.Declarative.C__'8759'__192
                    (d_ren_44
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe MAlonzo.Code.Declarative.du_mkCaseType_82 (coe v6) (coe v15))
                       (coe v12))
                    (coe
                       du_ren'45'Cases_128 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v16) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution.weaken
d_weaken_224 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d_weaken_224 v0 v1 v2 v3 v4
  = coe
      d_ren_44 (coe v0) (coe v0) (coe v1)
      (coe MAlonzo.Code.Declarative.C__'44'__26 v1 v3)
      (coe (\ v5 v6 -> v6))
      (coe (\ v5 v6 -> coe MAlonzo.Code.Declarative.C_S_38 v6)) (coe v2)
      (coe v4)
-- Declarative.RenamingSubstitution.weaken⋆
d_weaken'8902'_228 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d_weaken'8902'_228 v0 v1 v2 v3 v4
  = coe
      d_ren_44 (coe v0)
      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v3)) (coe v1)
      (coe MAlonzo.Code.Declarative.C__'44''8902'__22 v1)
      (coe (\ v5 -> coe MAlonzo.Code.Type.C_S_18))
      (coe (\ v5 -> coe MAlonzo.Code.Declarative.C_T_40 v5)) (coe v2)
      (coe v4)
-- Declarative.RenamingSubstitution.Sub
d_Sub_236 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  ()
d_Sub_236 = erased
-- Declarative.RenamingSubstitution.exts
d_exts_250 ::
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
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d_exts_250 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_exts_250 v0 v1 v3 v4 v5 v6 v7 v8
du_exts_250 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8866'__110) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Declarative.T__'8866'__110
du_exts_250 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Declarative.C_Z_36
        -> coe
             MAlonzo.Code.Declarative.C_'96'_114
             (coe MAlonzo.Code.Declarative.C_Z_36)
      MAlonzo.Code.Declarative.C_S_38 v12
        -> coe
             d_weaken_224 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                (coe v3) (coe MAlonzo.Code.Utils.C_'42'_756) (coe v6))
             (coe
                MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                (coe v3) (coe MAlonzo.Code.Utils.C_'42'_756) (coe v5))
             (coe v4 v6 v12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution.exts⋆
d_exts'8902'_266 ::
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
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d_exts'8902'_266 v0 v1 ~v2 v3 v4 v5 v6 ~v7 v8
  = du_exts'8902'_266 v0 v1 v3 v4 v5 v6 v8
du_exts'8902'_266 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8866'__110) ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Declarative.T__'8866'__110
du_exts'8902'_266 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Declarative.C_T_40 v9 v11
        -> coe
             d_weaken'8902'_228 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                (coe v3) (coe MAlonzo.Code.Utils.C_'42'_756) (coe v9))
             (coe v5) (coe v4 v9 v11)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution.sub
d_sub_278 ::
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
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d_sub_278 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Declarative.C_'96'_114 v9 -> coe v5 v6 v9
      MAlonzo.Code.Declarative.C_ƛ_116 v10
        -> case coe v6 of
             MAlonzo.Code.Type.C__'8658'__26 v12 v13
               -> coe
                    MAlonzo.Code.Declarative.C_ƛ_116
                    (d_sub_278
                       (coe v0) (coe v1) (coe MAlonzo.Code.Declarative.C__'44'__26 v2 v12)
                       (coe
                          MAlonzo.Code.Declarative.C__'44'__26 v3
                          (MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                             (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                             (coe v12)))
                       (coe v4)
                       (coe
                          du_exts_250 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v12))
                       (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'183'__118 v8 v10 v11
        -> coe
             MAlonzo.Code.Declarative.C__'183'__118
             (MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v8))
             (d_sub_278
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.C__'8658'__26 v8 v6) (coe v10))
             (d_sub_278
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v8)
                (coe v11))
      MAlonzo.Code.Declarative.C_Λ_120 v10
        -> case coe v6 of
             MAlonzo.Code.Type.C_Π_24 v12 v13
               -> coe
                    MAlonzo.Code.Declarative.C_Λ_120
                    (d_sub_278
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v12))
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v12))
                       (coe MAlonzo.Code.Declarative.C__'44''8902'__22 v2)
                       (coe MAlonzo.Code.Declarative.C__'44''8902'__22 v3)
                       (coe
                          MAlonzo.Code.Type.RenamingSubstitution.du_exts_336 (coe v1)
                          (coe v4) (coe v12))
                       (\ v14 v15 ->
                          coe
                            du_exts'8902'_266 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
                            (coe v12) v15)
                       (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'183''8902'__124 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Declarative.C__'183''8902'__124 (coe v8)
             (coe
                MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v8))
                (coe
                   MAlonzo.Code.Type.RenamingSubstitution.du_exts_336 (coe v1)
                   (coe v4) (coe v8))
                (coe MAlonzo.Code.Utils.C_'42'_756) (coe v9))
             (coe
                d_sub_278 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.C_Π_24 v8 v9) (coe v10))
             (coe
                MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                (coe v4) (coe v8) (coe v11))
      MAlonzo.Code.Declarative.C_wrap_130 v11
        -> case coe v6 of
             MAlonzo.Code.Type.C_μ_32 v13 v14 v15
               -> coe
                    MAlonzo.Code.Declarative.C_wrap_130
                    (d_sub_278
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Type.C__'183'__30 v13
                          (coe
                             MAlonzo.Code.Type.C__'183'__30
                             (coe
                                MAlonzo.Code.Utils.C__'8658'__760 (coe v13)
                                (coe MAlonzo.Code.Utils.C_'42'_756))
                             v14
                             (coe
                                MAlonzo.Code.Type.C_ƛ_28
                                (coe
                                   MAlonzo.Code.Type.C_μ_32 v13
                                   (coe
                                      MAlonzo.Code.Type.RenamingSubstitution.d_weaken_98 v0
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__760
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__760 (coe v13)
                                            (coe MAlonzo.Code.Utils.C_'42'_756))
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__760 (coe v13)
                                            (coe MAlonzo.Code.Utils.C_'42'_756)))
                                      v13 v14)
                                   (coe
                                      MAlonzo.Code.Type.C_'96'_22 (coe MAlonzo.Code.Type.C_Z_16)))))
                          v15)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_unwrap_132 v11
        -> case coe v6 of
             MAlonzo.Code.Type.C__'183'__30 v13 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Type.C__'183'__30 v18 v20 v21
                      -> coe
                           MAlonzo.Code.Declarative.C_unwrap_132
                           (d_sub_278
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                              (coe MAlonzo.Code.Type.C_μ_32 v13 v20 v16) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_constr_142 v9 v11 v13
        -> case coe v6 of
             MAlonzo.Code.Type.C_SOP_40 v15 v16
               -> coe
                    MAlonzo.Code.Declarative.C_constr_142 v9
                    (MAlonzo.Code.Type.RenamingSubstitution.d_sub'45'List_350
                       (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                       (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v9)))
                    (d_sub'45'ConstrArgs_296
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v9))
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_case_154 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Declarative.C_case_154 v8
             (coe
                MAlonzo.Code.Type.RenamingSubstitution.du_sub'45'VecList_356
                (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v9))
             (d_sub_278
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.C_SOP_40 v8 v9) (coe v11))
             (coe
                du_sub'45'Cases_362 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v9) (coe v12))
      MAlonzo.Code.Declarative.C_conv_156 v8 v10 v11
        -> coe
             MAlonzo.Code.Declarative.C_conv_156
             (MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe v8))
             (MAlonzo.Code.Type.Equality.d_sub'8801'β_172
                (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_756) (coe v8)
                (coe v6) (coe v4) (coe v10))
             (d_sub_278
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v8)
                (coe v11))
      MAlonzo.Code.Declarative.C_con_162 v8 v10 v11
        -> case coe v6 of
             MAlonzo.Code.Type.C_con_36 v13
               -> coe
                    MAlonzo.Code.Declarative.C_con_162 v8 v10
                    (coe
                       MAlonzo.Code.Type.Equality.C_trans'8801'β_18
                       (MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                          (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'9839'_758)
                          (coe
                             MAlonzo.Code.Type.RenamingSubstitution.d_sub'8709'_896 (coe v0)
                             (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v8)))
                       (MAlonzo.Code.Type.Equality.d_sub'8801'β_172
                          (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v13)
                          (coe
                             MAlonzo.Code.Type.RenamingSubstitution.d_sub'8709'_896 (coe v0)
                             (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v8))
                          (coe v4) (coe v11))
                       (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_builtin_166 v8 -> coe v7
      MAlonzo.Code.Declarative.C_error_170
        -> coe MAlonzo.Code.Declarative.C_error_170
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution.sub-ConstrArgs
d_sub'45'ConstrArgs_296 ::
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
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
d_sub'45'ConstrArgs_296 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Utils.List.C_'91''93'_308 -> coe v7
      MAlonzo.Code.Utils.List.C__'8759'__314 v10 v11
        -> case coe v6 of
             (:) v12 v13
               -> coe
                    MAlonzo.Code.Utils.List.C__'8759'__314
                    (d_sub_278
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v12)
                       (coe v10))
                    (d_sub'45'ConstrArgs_296
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v13)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution.lem-sub-mkCaseType
d_lem'45'sub'45'mkCaseType_326 ::
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
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45'sub'45'mkCaseType_326 = erased
-- Declarative.RenamingSubstitution.sub-Cases
d_sub'45'Cases_362 ::
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
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Declarative.T_Cases_104 ->
  MAlonzo.Code.Declarative.T_Cases_104
d_sub'45'Cases_362 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_sub'45'Cases_362 v0 v1 v2 v3 v4 v5 v6 v8 v9
du_sub'45'Cases_362 ::
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
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Declarative.T_Cases_104 ->
  MAlonzo.Code.Declarative.T_Cases_104
du_sub'45'Cases_362 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Declarative.C_'91''93'_180 -> coe v8
      MAlonzo.Code.Declarative.C__'8759'__192 v12 v13
        -> case coe v7 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
               -> coe
                    MAlonzo.Code.Declarative.C__'8759'__192
                    (d_sub_278
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe MAlonzo.Code.Declarative.du_mkCaseType_82 (coe v6) (coe v15))
                       (coe v12))
                    (coe
                       du_sub'45'Cases_362 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v16) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution.subcons
d_subcons_458 ::
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
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d_subcons_458 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_subcons_458 v5 v7 v8 v9
du_subcons_458 ::
  (MAlonzo.Code.Type.T__'8866''8902'__20 ->
   MAlonzo.Code.Declarative.T__'8715'__34 ->
   MAlonzo.Code.Declarative.T__'8866'__110) ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Declarative.T__'8866'__110
du_subcons_458 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Declarative.C_Z_36 -> coe v1
      MAlonzo.Code.Declarative.C_S_38 v8 -> coe v0 v2 v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.RenamingSubstitution._[_]
d__'91'_'93'_470 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d__'91'_'93'_470 v0 v1 v2 v3 v4 v5
  = coe
      d_sub_278 (coe v0) (coe v0)
      (coe MAlonzo.Code.Declarative.C__'44'__26 v1 v2) (coe v1)
      (\ v6 v7 -> coe MAlonzo.Code.Type.C_'96'_22 v7)
      (coe
         du_subcons_458
         (coe (\ v6 v7 -> coe MAlonzo.Code.Declarative.C_'96'_114 v7))
         (coe v5))
      (coe v3) (coe v4)
-- Declarative.RenamingSubstitution._[_]⋆
d__'91'_'93''8902'_478 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d__'91'_'93''8902'_478 v0 v1 v2 v3 v4 v5
  = coe
      d_sub_278
      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v2)) (coe v0)
      (coe MAlonzo.Code.Declarative.C__'44''8902'__22 v1) (coe v1)
      (coe
         MAlonzo.Code.Type.RenamingSubstitution.du_sub'45'cons_420
         (\ v6 v7 -> coe MAlonzo.Code.Type.C_'96'_22 v7) (coe v5))
      (coe
         (\ v6 v7 ->
            case coe v7 of
              MAlonzo.Code.Declarative.C_T_40 v10 v12
                -> coe MAlonzo.Code.Declarative.C_'96'_114 v12
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe v3) (coe v4)
