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

module MAlonzo.Code.Algorithmic.Completeness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Declarative
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNBE.Soundness
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Algorithmic.Completeness.nfCtx
d_nfCtx_6 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2
d_nfCtx_6 v0 v1
  = case coe v1 of
      MAlonzo.Code.Declarative.C_'8709'_18
        -> coe MAlonzo.Code.Algorithmic.C_'8709'_4
      MAlonzo.Code.Declarative.C__'44''8902'__22 v3
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v5 v6
               -> coe
                    MAlonzo.Code.Algorithmic.C__'44''8902'__8
                    (d_nfCtx_6 (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'44'__26 v3 v4
        -> coe
             MAlonzo.Code.Algorithmic.C__'44'__12 (d_nfCtx_6 (coe v0) (coe v3))
             (MAlonzo.Code.Type.BetaNBE.d_nf_258
                (coe v0) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Completeness.nfTyVar
d_nfTyVar_22 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16
d_nfTyVar_22 v0 v1 ~v2 v3 = du_nfTyVar_22 v0 v1 v3
du_nfTyVar_22 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16
du_nfTyVar_22 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Declarative.C_Z_36
        -> coe MAlonzo.Code.Algorithmic.C_Z_22
      MAlonzo.Code.Declarative.C_S_38 v7
        -> case coe v1 of
             MAlonzo.Code.Declarative.C__'44'__26 v9 v10
               -> coe
                    MAlonzo.Code.Algorithmic.C_S_30
                    (coe du_nfTyVar_22 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_T_40 v5 v7
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Declarative.C__'44''8902'__22 v11
                      -> coe
                           MAlonzo.Code.Algorithmic.C_T_38
                           (MAlonzo.Code.Type.BetaNBE.d_eval_166
                              (coe v8) (coe v8) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v5)
                              (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
                           (coe du_nfTyVar_22 (coe v8) (coe v11) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Completeness.lemΠ
d_lemΠ_36 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemΠ_36 = erased
-- Algorithmic.Completeness.stability-μ
d_stability'45'μ_48 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stability'45'μ_48 = erased
-- Algorithmic.Completeness.lem[]
d_lem'91''93'_62 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'91''93'_62 = erased
-- Algorithmic.Completeness.lemσ
d_lemσ_94 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemσ_94 = erased
-- Algorithmic.Completeness.nfList
d_nfList_106 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4]
d_nfList_106 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v0)
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v2))
             (coe d_nfList_106 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Completeness.subNf-sub∅
d_subNf'45'sub'8709'_118 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'sub'8709'_118 = erased
-- Algorithmic.Completeness.subNf∅-sub∅
d_subNf'8709''45'sub'8709'_130 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'8709''45'sub'8709'_130 = erased
-- Algorithmic.Completeness.con-injective
d_con'45'injective_140 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_con'45'injective_140 = erased
-- Algorithmic.Completeness.helper
d_helper_148 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_148 = erased
-- Algorithmic.Completeness.mkTy-lem
d_mkTy'45'lem_176 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.Signature.T__'47'_'8866''8902'_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkTy'45'lem_176 = erased
-- Algorithmic.Completeness.sig2type⇒-lem
d_sig2type'8658''45'lem_192 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  [MAlonzo.Code.Builtin.Signature.T__'47'_'8866''8902'_26] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sig2type'8658''45'lem_192 = erased
-- Algorithmic.Completeness.sig2typeΠ-lem
d_sig2typeΠ'45'lem_210 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sig2typeΠ'45'lem_210 = erased
-- Algorithmic.Completeness.sig2type-lem
d_sig2type'45'lem_226 ::
  MAlonzo.Code.Builtin.Signature.T_Sig_72 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sig2type'45'lem_226 = erased
-- Algorithmic.Completeness.btype-lem
d_btype'45'lem_254 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_btype'45'lem_254 = erased
-- Algorithmic.Completeness.nfType
d_nfType_264 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_nfType_264 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Declarative.C_'96'_114 v5
        -> coe
             MAlonzo.Code.Algorithmic.C_'96'_184
             (coe du_nfTyVar_22 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Declarative.C_ƛ_116 v6
        -> case coe v2 of
             MAlonzo.Code.Type.C__'8658'__26 v8 v9
               -> coe
                    MAlonzo.Code.Algorithmic.C_ƛ_190
                    (d_nfType_264
                       (coe v0) (coe MAlonzo.Code.Declarative.C__'44'__26 v1 v8) (coe v9)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'183'__118 v4 v6 v7
        -> coe
             MAlonzo.Code.Algorithmic.C__'183'__196
             (MAlonzo.Code.Type.BetaNBE.d_reify_86
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v0)
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0)
                   (coe MAlonzo.Code.Utils.C_'42'_704) (coe v4)
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
             (d_nfType_264
                (coe v0) (coe v1) (coe MAlonzo.Code.Type.C__'8658'__26 v4 v2)
                (coe v6))
             (d_nfType_264 (coe v0) (coe v1) (coe v4) (coe v7))
      MAlonzo.Code.Declarative.C_Λ_120 v6
        -> case coe v2 of
             MAlonzo.Code.Type.C_Π_24 v8 v9
               -> coe
                    MAlonzo.Code.Algorithmic.C_Λ_202
                    (d_nfType_264
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                       (coe MAlonzo.Code.Declarative.C__'44''8902'__22 v1) (coe v9)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C__'183''8902'__124 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v4
             (MAlonzo.Code.Type.BetaNBE.d_nf_258
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v4))
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v5))
             (d_nfType_264
                (coe v0) (coe v1) (coe MAlonzo.Code.Type.C_Π_24 v4 v5) (coe v6))
             (MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Declarative.C_wrap_130 v7
        -> case coe v2 of
             MAlonzo.Code.Type.C_μ_32 v9 v10 v11
               -> coe
                    MAlonzo.Code.Algorithmic.C_wrap_220
                    (d_nfType_264
                       (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Type.C__'183'__30 v9
                          (coe
                             MAlonzo.Code.Type.C__'183'__30
                             (coe
                                MAlonzo.Code.Utils.C__'8658'__708 (coe v9)
                                (coe MAlonzo.Code.Utils.C_'42'_704))
                             v10
                             (coe
                                MAlonzo.Code.Type.C_ƛ_28
                                (coe
                                   MAlonzo.Code.Type.C_μ_32 v9
                                   (coe
                                      MAlonzo.Code.Type.RenamingSubstitution.d_weaken_98 v0
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__708
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__708 (coe v9)
                                            (coe MAlonzo.Code.Utils.C_'42'_704))
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__708 (coe v9)
                                            (coe MAlonzo.Code.Utils.C_'42'_704)))
                                      v9 v10)
                                   (coe
                                      MAlonzo.Code.Type.C_'96'_22 (coe MAlonzo.Code.Type.C_Z_16)))))
                          v11)
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_unwrap_132 v7
        -> case coe v2 of
             MAlonzo.Code.Type.C__'183'__30 v9 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Type.C__'183'__30 v14 v16 v17
                      -> coe
                           MAlonzo.Code.Algorithmic.C_unwrap_230 v9
                           (MAlonzo.Code.Type.BetaNBE.d_reify_86
                              (coe
                                 MAlonzo.Code.Utils.C__'8658'__708
                                 (coe
                                    MAlonzo.Code.Utils.C__'8658'__708 (coe v9)
                                    (coe MAlonzo.Code.Utils.C_'42'_704))
                                 (coe
                                    MAlonzo.Code.Utils.C__'8658'__708 (coe v9)
                                    (coe MAlonzo.Code.Utils.C_'42'_704)))
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0)
                                 (coe
                                    MAlonzo.Code.Utils.C__'8658'__708
                                    (coe
                                       MAlonzo.Code.Utils.C__'8658'__708 (coe v9)
                                       (coe MAlonzo.Code.Utils.C_'42'_704))
                                    (coe
                                       MAlonzo.Code.Utils.C__'8658'__708 (coe v9)
                                       (coe MAlonzo.Code.Utils.C_'42'_704)))
                                 (coe v16) (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
                           (MAlonzo.Code.Type.BetaNBE.d_reify_86
                              (coe v9) (coe v0)
                              (coe
                                 MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0) (coe v9)
                                 (coe v12) (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
                           (d_nfType_264
                              (coe v0) (coe v1) (coe MAlonzo.Code.Type.C_μ_32 v9 v16 v12)
                              (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_constr_142 v5 v7 v9
        -> case coe v2 of
             MAlonzo.Code.Type.C_SOP_40 v11 v12
               -> coe
                    MAlonzo.Code.Algorithmic.C_constr_240 v5
                    (MAlonzo.Code.Type.BetaNBE.d_eval'45'List_174
                       (coe v0) (coe v0) (coe MAlonzo.Code.Utils.C_'42'_704)
                       (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v12) (coe v5))
                       (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
                    (d_nfType'45'ConstrArgs_274
                       (coe v0) (coe v1)
                       (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v12) (coe v5))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Declarative.C_case_154 v4 v5 v7 v8
        -> coe
             MAlonzo.Code.Algorithmic.C_case_252 v4
             (coe
                MAlonzo.Code.Type.BetaNBE.du_eval'45'VecList_184 (coe v0) (coe v0)
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v5)
                (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
             (d_nfType_264
                (coe v0) (coe v1) (coe MAlonzo.Code.Type.C_SOP_40 v4 v5) (coe v7))
             (coe
                du_nfType'45'Cases_306 (coe v0) (coe v1) (coe v2) (coe v5)
                (coe v8))
      MAlonzo.Code.Declarative.C_conv_156 v4 v6 v7
        -> coe d_nfType_264 (coe v0) (coe v1) (coe v4) (coe v7)
      MAlonzo.Code.Declarative.C_con_162 v4 v6 v7
        -> coe
             MAlonzo.Code.Algorithmic.C_con_258
             (MAlonzo.Code.Type.BetaNBE.d_nf_258
                (coe MAlonzo.Code.Type.C_'8709'_4)
                (coe MAlonzo.Code.Utils.C_'9839'_706) (coe v4))
             v6
      MAlonzo.Code.Declarative.C_builtin_166 v4
        -> coe MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v4
      MAlonzo.Code.Declarative.C_error_170
        -> coe MAlonzo.Code.Algorithmic.C_error_268
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Completeness.nfType-ConstrArgs
d_nfType'45'ConstrArgs_274 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
d_nfType'45'ConstrArgs_274 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Utils.List.C_'91''93'_308 -> coe v3
      MAlonzo.Code.Utils.List.C__'8759'__314 v6 v7
        -> case coe v2 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Utils.List.C__'8759'__314
                    (d_nfType_264 (coe v0) (coe v1) (coe v8) (coe v6))
                    (d_nfType'45'ConstrArgs_274 (coe v0) (coe v1) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Completeness.lemma-mkCaseType
d_lemma'45'mkCaseType_286 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'45'mkCaseType_286 = erased
-- Algorithmic.Completeness.nfType-Cases
d_nfType'45'Cases_306 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Declarative.T_Cases_104 ->
  MAlonzo.Code.Algorithmic.T_Cases_172
d_nfType'45'Cases_306 v0 v1 v2 ~v3 v4 v5
  = du_nfType'45'Cases_306 v0 v1 v2 v4 v5
du_nfType'45'Cases_306 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Declarative.T_Cases_104 ->
  MAlonzo.Code.Algorithmic.T_Cases_172
du_nfType'45'Cases_306 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Declarative.C_'91''93'_180
        -> coe MAlonzo.Code.Algorithmic.C_'91''93'_278
      MAlonzo.Code.Declarative.C__'8759'__192 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
               -> coe
                    MAlonzo.Code.Algorithmic.C__'8759'__290
                    (d_nfType_264
                       (coe v0) (coe v1)
                       (coe MAlonzo.Code.Declarative.du_mkCaseType_82 (coe v2) (coe v11))
                       (coe v8))
                    (coe
                       du_nfType'45'Cases_306 (coe v0) (coe v1) (coe v2) (coe v12)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Completeness.completenessT
d_completenessT_376 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completenessT_376 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_nfType_264 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Type.BetaNBE.Soundness.d_soundness_470 (coe v0)
         (coe MAlonzo.Code.Utils.C_'42'_704) (coe v2))
