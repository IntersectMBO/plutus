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

module MAlonzo.Code.Algorithmic.RenamingSubstitution where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNBE.RenamingSubstitution
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Algorithmic.RenamingSubstitution.Ren
d_Ren_8 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 -> ()
d_Ren_8 = erased
-- Algorithmic.RenamingSubstitution.ext
d_ext_32 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16
d_ext_32 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 = du_ext_32 v5 v7 v8
du_ext_32 ::
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16
du_ext_32 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Algorithmic.C_Z_22
        -> coe MAlonzo.Code.Algorithmic.C_Z_22
      MAlonzo.Code.Algorithmic.C_S_30 v7
        -> coe MAlonzo.Code.Algorithmic.C_S_30 (coe v0 v1 v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.ext⋆
d_ext'8902'_58 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16
d_ext'8902'_58 v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8
  = du_ext'8902'_58 v0 v1 v4 v5 v8
du_ext'8902'_58 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16
du_ext'8902'_58 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Algorithmic.C_T_38 v8 v9
        -> coe
             MAlonzo.Code.Algorithmic.C_T_38
             (MAlonzo.Code.Type.BetaNormal.d_renNf_46
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'42'_704)
                (coe v8))
             (coe v3 v8 v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.ren-mkCaseType
d_ren'45'mkCaseType_78 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'mkCaseType_78 = erased
-- Algorithmic.RenamingSubstitution.ren
d_ren_104 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_ren_104 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Algorithmic.C_'96'_184 v9
        -> coe MAlonzo.Code.Algorithmic.C_'96'_184 (coe v5 v6 v9)
      MAlonzo.Code.Algorithmic.C_ƛ_190 v10
        -> case coe v6 of
             MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v12 v13
               -> coe
                    MAlonzo.Code.Algorithmic.C_ƛ_190
                    (d_ren_104
                       (coe v0) (coe v1) (coe MAlonzo.Code.Algorithmic.C__'44'__12 v2 v12)
                       (coe
                          MAlonzo.Code.Algorithmic.C__'44'__12 v3
                          (MAlonzo.Code.Type.BetaNormal.d_renNf_46
                             (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_704)
                             (coe v12)))
                       (coe v4) (coe du_ext_32 (coe v5)) (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183'__196 v8 v10 v11
        -> coe
             MAlonzo.Code.Algorithmic.C__'183'__196
             (MAlonzo.Code.Type.BetaNormal.d_renNf_46
                (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_704)
                (coe v8))
             (d_ren_104
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v8 v6) (coe v10))
             (d_ren_104
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v8)
                (coe v11))
      MAlonzo.Code.Algorithmic.C_Λ_202 v10
        -> case coe v6 of
             MAlonzo.Code.Type.BetaNormal.C_Π_14 v12 v13
               -> coe
                    MAlonzo.Code.Algorithmic.C_Λ_202
                    (d_ren_104
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v12))
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v12))
                       (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v2)
                       (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v3)
                       (coe MAlonzo.Code.Type.RenamingSubstitution.du_ext_18 (coe v4))
                       (\ v14 v15 ->
                          coe du_ext'8902'_58 (coe v0) (coe v1) (coe v4) (coe v5) v15)
                       (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v8
             (MAlonzo.Code.Type.BetaNormal.d_renNf_46
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v8))
                (coe MAlonzo.Code.Type.RenamingSubstitution.du_ext_18 (coe v4))
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v10))
             (d_ren_104
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v8 v10) (coe v11))
             (MAlonzo.Code.Type.BetaNormal.d_renNf_46
                (coe v0) (coe v1) (coe v4) (coe v8) (coe v12))
      MAlonzo.Code.Algorithmic.C_wrap_220 v11
        -> case coe v6 of
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v13 v14 v15
               -> coe
                    MAlonzo.Code.Algorithmic.C_wrap_220
                    (d_ren_104
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Type.BetaNBE.d__'183'V__150 (coe v0) (coe v13)
                          (coe MAlonzo.Code.Utils.C_'42'_704)
                          (coe
                             MAlonzo.Code.Type.BetaNBE.d__'183'V__150 (coe v0)
                             (coe
                                MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                (coe MAlonzo.Code.Utils.C_'42'_704))
                             (coe
                                MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                (coe MAlonzo.Code.Utils.C_'42'_704))
                             (coe
                                MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0)
                                (coe
                                   MAlonzo.Code.Utils.C__'8658'__708
                                   (coe
                                      MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                      (coe MAlonzo.Code.Utils.C_'42'_704))
                                   (coe
                                      MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                      (coe MAlonzo.Code.Utils.C_'42'_704)))
                                (coe
                                   MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0)
                                   (coe
                                      MAlonzo.Code.Utils.C__'8658'__708
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                         (coe MAlonzo.Code.Utils.C_'42'_704))
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                         (coe MAlonzo.Code.Utils.C_'42'_704)))
                                   (coe v14))
                                (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
                             (coe
                                MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0)
                                (coe
                                   MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                   (coe MAlonzo.Code.Utils.C_'42'_704))
                                (coe
                                   MAlonzo.Code.Type.C_ƛ_28
                                   (coe
                                      MAlonzo.Code.Type.C_μ_32 v13
                                      (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                         (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__708
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                               (coe MAlonzo.Code.Utils.C_'42'_704))
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                               (coe MAlonzo.Code.Utils.C_'42'_704)))
                                         (coe
                                            MAlonzo.Code.Type.BetaNormal.d_weakenNf_122 v0
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__708
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                                  (coe MAlonzo.Code.Utils.C_'42'_704))
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                                  (coe MAlonzo.Code.Utils.C_'42'_704)))
                                            v13 v14))
                                      (coe
                                         MAlonzo.Code.Type.C_'96'_22
                                         (coe MAlonzo.Code.Type.C_Z_16))))
                                (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
                          (coe
                             MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0) (coe v13)
                             (coe
                                MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v13)
                                (coe v15))
                             (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_unwrap_230 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Algorithmic.C_unwrap_230 v8
             (MAlonzo.Code.Type.BetaNormal.d_renNf_46
                (coe v0) (coe v1) (coe v4)
                (coe
                   MAlonzo.Code.Utils.C__'8658'__708
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                      (coe MAlonzo.Code.Utils.C_'42'_704))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                      (coe MAlonzo.Code.Utils.C_'42'_704)))
                (coe v10))
             (MAlonzo.Code.Type.BetaNormal.d_renNf_46
                (coe v0) (coe v1) (coe v4) (coe v8) (coe v11))
             (d_ren_104
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v8 v10 v11) (coe v12))
      MAlonzo.Code.Algorithmic.C_constr_240 v9 v11 v13
        -> case coe v6 of
             MAlonzo.Code.Type.BetaNormal.C_SOP_28 v15 v16
               -> coe
                    MAlonzo.Code.Algorithmic.C_constr_240 v9
                    (coe
                       MAlonzo.Code.Data.Vec.Base.du_lookup_82
                       (coe
                          MAlonzo.Code.Type.BetaNormal.du_renNf'45'VecList_58 (coe v0)
                          (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v16))
                       (coe v9))
                    (coe
                       du_ren'45'ConstrArgs_126 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v5) (coe v9) (coe v16) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_case_252 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Algorithmic.C_case_252 v8
             (coe
                MAlonzo.Code.Type.BetaNormal.du_renNf'45'VecList_58 (coe v0)
                (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v9))
             (d_ren_104
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v8 v9) (coe v11))
             (coe
                du_ren'45'Cases_166 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v9) (coe v12))
      MAlonzo.Code.Algorithmic.C_con_258 v8 v10
        -> coe MAlonzo.Code.Algorithmic.C_con_258 v8 v10
      MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v9
        -> coe MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v9
      MAlonzo.Code.Algorithmic.C_error_268
        -> coe MAlonzo.Code.Algorithmic.C_error_268
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.ren-ConstrArgs
d_ren'45'ConstrArgs_126 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  Integer ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
d_ren'45'ConstrArgs_126 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_ren'45'ConstrArgs_126 v0 v1 v2 v3 v5 v6 v7 v8 v9
du_ren'45'ConstrArgs_126 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
du_ren'45'ConstrArgs_126 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      d_ren'45'ConstrArgs'45'List_144 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
      (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v7) (coe v6))
      (coe v8)
-- Algorithmic.RenamingSubstitution.ren-ConstrArgs-List
d_ren'45'ConstrArgs'45'List_144 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
d_ren'45'ConstrArgs'45'List_144 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Utils.List.C_'91''93'_308 -> coe v7
      MAlonzo.Code.Utils.List.C__'8759'__314 v10 v11
        -> case coe v6 of
             (:) v12 v13
               -> coe
                    MAlonzo.Code.Utils.List.C__'8759'__314
                    (d_ren_104
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v12)
                       (coe v10))
                    (d_ren'45'ConstrArgs'45'List_144
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v13)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.ren-Cases
d_ren'45'Cases_166 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  Integer ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Algorithmic.T_Cases_172
d_ren'45'Cases_166 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_ren'45'Cases_166 v0 v1 v2 v3 v5 v6 v7 v8 v9
du_ren'45'Cases_166 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Algorithmic.T_Cases_172
du_ren'45'Cases_166 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Algorithmic.C_'91''93'_278 -> coe v8
      MAlonzo.Code.Algorithmic.C__'8759'__290 v12 v13
        -> case coe v7 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
               -> coe
                    MAlonzo.Code.Algorithmic.C__'8759'__290
                    (d_ren_104
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Data.List.Base.du_foldr_216
                          (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16) (coe v6)
                          (coe v15))
                       (coe v12))
                    (coe
                       du_ren'45'Cases_166 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v16) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.weaken
d_weaken_314 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_weaken_314 v0 v1 v2 v3 v4
  = coe
      d_ren_104 (coe v0) (coe v0) (coe v1)
      (coe MAlonzo.Code.Algorithmic.C__'44'__12 v1 v3)
      (coe (\ v5 v6 -> v6))
      (coe (\ v5 v6 -> coe MAlonzo.Code.Algorithmic.C_S_30 v6)) (coe v2)
      (coe v4)
-- Algorithmic.RenamingSubstitution.weaken⋆
d_weaken'8902'_326 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_weaken'8902'_326 v0 v1 v2 v3 v4
  = coe
      d_ren_104 (coe v0)
      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v3)) (coe v1)
      (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v1)
      (coe (\ v5 -> coe MAlonzo.Code.Type.C_S_18))
      (coe MAlonzo.Code.Algorithmic.C_T_38) (coe v2) (coe v4)
-- Algorithmic.RenamingSubstitution.Sub
d_Sub_336 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 -> ()
d_Sub_336 = erased
-- Algorithmic.RenamingSubstitution.exts
d_exts_360 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_exts_360 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_exts_360 v0 v1 v3 v4 v5 v6 v7 v8
du_exts_360 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du_exts_360 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Algorithmic.C_Z_22
        -> coe
             MAlonzo.Code.Algorithmic.C_'96'_184
             (coe MAlonzo.Code.Algorithmic.C_Z_22)
      MAlonzo.Code.Algorithmic.C_S_30 v12
        -> coe
             d_weaken_314 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d_subNf_104 (coe v0)
                (coe v1) (coe v3) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v6))
             (coe
                MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d_subNf_104 (coe v0)
                (coe v1) (coe v3) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v5))
             (coe v4 v6 v12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.exts⋆
d_exts'8902'_386 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_exts'8902'_386 v0 v1 ~v2 v3 v4 v5 v6 ~v7 v8
  = du_exts'8902'_386 v0 v1 v3 v4 v5 v6 v8
du_exts'8902'_386 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du_exts'8902'_386 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Algorithmic.C_T_38 v10 v11
        -> coe
             d_weaken'8902'_326 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v1) (coe v1)
                (coe MAlonzo.Code.Utils.C_'42'_704)
                (coe
                   MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                   (coe
                      (\ v12 v13 ->
                         MAlonzo.Code.Type.BetaNormal.d_embNf_128
                           (coe v1) (coe v12) (coe v3 v12 v13)))
                   (coe MAlonzo.Code.Utils.C_'42'_704)
                   (coe
                      MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0)
                      (coe MAlonzo.Code.Utils.C_'42'_704) (coe v10)))
                (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
             (coe v5) (coe v4 v10 v11)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.sub
d_sub_412 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_sub_412 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Algorithmic.C_'96'_184 v9 -> coe v5 v6 v9
      MAlonzo.Code.Algorithmic.C_ƛ_190 v10
        -> case coe v6 of
             MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v12 v13
               -> coe
                    MAlonzo.Code.Algorithmic.C_ƛ_190
                    (d_sub_412
                       (coe v0) (coe v1) (coe MAlonzo.Code.Algorithmic.C__'44'__12 v2 v12)
                       (coe
                          MAlonzo.Code.Algorithmic.C__'44'__12 v3
                          (MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d_subNf_104
                             (coe v0) (coe v1) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_704)
                             (coe v12)))
                       (coe v4)
                       (coe
                          du_exts_360 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v12))
                       (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183'__196 v8 v10 v11
        -> coe
             MAlonzo.Code.Algorithmic.C__'183'__196
             (MAlonzo.Code.Type.BetaNBE.d_reify_86
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v1)
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v1) (coe v1)
                   (coe MAlonzo.Code.Utils.C_'42'_704)
                   (coe
                      MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                      (coe
                         (\ v12 v13 ->
                            MAlonzo.Code.Type.BetaNormal.d_embNf_128
                              (coe v1) (coe v12) (coe v4 v12 v13)))
                      (coe MAlonzo.Code.Utils.C_'42'_704)
                      (coe
                         MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0)
                         (coe MAlonzo.Code.Utils.C_'42'_704) (coe v8)))
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
             (d_sub_412
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v8 v6) (coe v10))
             (d_sub_412
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v8)
                (coe v11))
      MAlonzo.Code.Algorithmic.C_Λ_202 v10
        -> case coe v6 of
             MAlonzo.Code.Type.BetaNormal.C_Π_14 v12 v13
               -> coe
                    MAlonzo.Code.Algorithmic.C_Λ_202
                    (d_sub_412
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v12))
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v12))
                       (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v2)
                       (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v3)
                       (coe
                          MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.du_extsNf_198
                          (coe v1) (coe v4) (coe v12))
                       (\ v14 v15 ->
                          coe
                            du_exts'8902'_386 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
                            (coe v12) v15)
                       (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v8
             (MAlonzo.Code.Type.BetaNBE.d_reify_86
                (coe MAlonzo.Code.Utils.C_'42'_704)
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v8))
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166
                   (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v8))
                   (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v8))
                   (coe MAlonzo.Code.Utils.C_'42'_704)
                   (coe
                      MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v8))
                      (coe
                         MAlonzo.Code.Type.RenamingSubstitution.du_exts_336 (coe v1)
                         (coe
                            (\ v14 v15 ->
                               MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                 (coe v1) (coe v14) (coe v4 v14 v15)))
                         (coe v8))
                      (coe MAlonzo.Code.Utils.C_'42'_704)
                      (coe
                         MAlonzo.Code.Type.BetaNormal.d_embNf_128
                         (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                         (coe MAlonzo.Code.Utils.C_'42'_704) (coe v10)))
                   (coe
                      MAlonzo.Code.Type.BetaNBE.du_exte_140 (coe v1)
                      (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250) (coe v8))))
             (d_sub_412
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v8 v10) (coe v11))
             (MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d_subNf_104
                (coe v0) (coe v1) (coe v4) (coe v8) (coe v12))
      MAlonzo.Code.Algorithmic.C_wrap_220 v11
        -> case coe v6 of
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v13 v14 v15
               -> coe
                    MAlonzo.Code.Algorithmic.C_wrap_220
                    (d_sub_412
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v0)
                          (coe MAlonzo.Code.Utils.C_'42'_704)
                          (coe
                             MAlonzo.Code.Type.C__'183'__30 v13
                             (coe
                                MAlonzo.Code.Type.C__'183'__30
                                (coe
                                   MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                   (coe MAlonzo.Code.Utils.C_'42'_704))
                                (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                   (coe v0)
                                   (coe
                                      MAlonzo.Code.Utils.C__'8658'__708
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                         (coe MAlonzo.Code.Utils.C_'42'_704))
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                         (coe MAlonzo.Code.Utils.C_'42'_704)))
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Type.C_ƛ_28
                                   (coe
                                      MAlonzo.Code.Type.C_μ_32 v13
                                      (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                         (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__708
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                               (coe MAlonzo.Code.Utils.C_'42'_704))
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                               (coe MAlonzo.Code.Utils.C_'42'_704)))
                                         (coe
                                            MAlonzo.Code.Type.BetaNormal.d_weakenNf_122 v0
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__708
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                                  (coe MAlonzo.Code.Utils.C_'42'_704))
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__708 (coe v13)
                                                  (coe MAlonzo.Code.Utils.C_'42'_704)))
                                            v13 v14))
                                      (coe
                                         MAlonzo.Code.Type.C_'96'_22
                                         (coe MAlonzo.Code.Type.C_Z_16)))))
                             (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                (coe v0) (coe v13) (coe v15))))
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_unwrap_230 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Algorithmic.C_unwrap_230 v8
             (MAlonzo.Code.Type.BetaNBE.d_reify_86
                (coe
                   MAlonzo.Code.Utils.C__'8658'__708
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                      (coe MAlonzo.Code.Utils.C_'42'_704))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                      (coe MAlonzo.Code.Utils.C_'42'_704)))
                (coe v1)
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v1) (coe v1)
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                         (coe MAlonzo.Code.Utils.C_'42'_704))
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                         (coe MAlonzo.Code.Utils.C_'42'_704)))
                   (coe
                      MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                      (coe
                         (\ v14 v15 ->
                            MAlonzo.Code.Type.BetaNormal.d_embNf_128
                              (coe v1) (coe v14) (coe v4 v14 v15)))
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__708
                         (coe
                            MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                            (coe MAlonzo.Code.Utils.C_'42'_704))
                         (coe
                            MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                            (coe MAlonzo.Code.Utils.C_'42'_704)))
                      (coe
                         MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0)
                         (coe
                            MAlonzo.Code.Utils.C__'8658'__708
                            (coe
                               MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                               (coe MAlonzo.Code.Utils.C_'42'_704))
                            (coe
                               MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                               (coe MAlonzo.Code.Utils.C_'42'_704)))
                         (coe v10)))
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
             (MAlonzo.Code.Type.BetaNBE.d_reify_86
                (coe v8) (coe v1)
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v1) (coe v1) (coe v8)
                   (coe
                      MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                      (coe
                         (\ v14 v15 ->
                            MAlonzo.Code.Type.BetaNormal.d_embNf_128
                              (coe v1) (coe v14) (coe v4 v14 v15)))
                      (coe v8)
                      (coe
                         MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v8)
                         (coe v11)))
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
             (d_sub_412
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v8 v10 v11) (coe v12))
      MAlonzo.Code.Algorithmic.C_constr_240 v9 v11 v13
        -> case coe v6 of
             MAlonzo.Code.Type.BetaNormal.C_SOP_28 v15 v16
               -> coe
                    MAlonzo.Code.Algorithmic.C_constr_240 v9
                    (coe
                       MAlonzo.Code.Data.Vec.Base.du_lookup_82
                       (coe
                          MAlonzo.Code.Type.BetaNBE.du_eval'45'VecList_184 (coe v1) (coe v1)
                          (coe MAlonzo.Code.Utils.C_'42'_704)
                          (coe
                             MAlonzo.Code.Type.RenamingSubstitution.du_sub'45'VecList_356
                             (coe v0) (coe v1)
                             (coe
                                (\ v17 v18 ->
                                   MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                     (coe v1) (coe v17) (coe v4 v17 v18)))
                             (coe MAlonzo.Code.Utils.C_'42'_704)
                             (coe
                                MAlonzo.Code.Type.BetaNormal.du_embNf'45'VecList_148 (coe v0)
                                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v16)))
                          (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
                       (coe v9))
                    (coe
                       du_sub'45'VecList_470 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v9) (coe v16) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_case_252 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Algorithmic.C_case_252 v8
             (coe
                MAlonzo.Code.Type.BetaNBE.du_eval'45'VecList_184 (coe v1) (coe v1)
                (coe MAlonzo.Code.Utils.C_'42'_704)
                (coe
                   MAlonzo.Code.Type.RenamingSubstitution.du_sub'45'VecList_356
                   (coe v0) (coe v1)
                   (coe
                      (\ v13 v14 ->
                         MAlonzo.Code.Type.BetaNormal.d_embNf_128
                           (coe v1) (coe v13) (coe v4 v13 v14)))
                   (coe MAlonzo.Code.Utils.C_'42'_704)
                   (coe
                      MAlonzo.Code.Type.BetaNormal.du_embNf'45'VecList_148 (coe v0)
                      (coe MAlonzo.Code.Utils.C_'42'_704) (coe v9)))
                (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
             (d_sub_412
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v8 v9) (coe v11))
             (coe
                du_sub'45'Cases_544 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v9) (coe v12))
      MAlonzo.Code.Algorithmic.C_con_258 v8 v10
        -> coe MAlonzo.Code.Algorithmic.C_con_258 v8 v10
      MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v9
        -> coe MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v9
      MAlonzo.Code.Algorithmic.C_error_268
        -> coe MAlonzo.Code.Algorithmic.C_error_268
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.sub-ConstrList
d_sub'45'ConstrList_434 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
d_sub'45'ConstrList_434 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Utils.List.C_'91''93'_308 -> coe v7
      MAlonzo.Code.Utils.List.C__'8759'__314 v10 v11
        -> case coe v6 of
             (:) v12 v13
               -> coe
                    MAlonzo.Code.Utils.List.C__'8759'__314
                    (d_sub_412
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v12)
                       (coe v10))
                    (d_sub'45'ConstrList_434
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v13)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.sub-VecList
d_sub'45'VecList_470 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  Integer ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
d_sub'45'VecList_470 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_sub'45'VecList_470 v0 v1 v2 v3 v5 v6 v7 v8 v9
du_sub'45'VecList_470 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
du_sub'45'VecList_470 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      d_sub'45'ConstrList_434 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
      (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v7) (coe v6))
      (coe v8)
-- Algorithmic.RenamingSubstitution.sub-mkCaseType
d_sub'45'mkCaseType_510 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'mkCaseType_510 = erased
-- Algorithmic.RenamingSubstitution.sub-Cases
d_sub'45'Cases_544 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  Integer ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Algorithmic.T_Cases_172
d_sub'45'Cases_544 v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9
  = du_sub'45'Cases_544 v0 v1 v2 v3 v5 v6 v7 v8 v9
du_sub'45'Cases_544 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Algorithmic.T_Cases_172
du_sub'45'Cases_544 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Algorithmic.C_'91''93'_278 -> coe v8
      MAlonzo.Code.Algorithmic.C__'8759'__290 v12 v13
        -> case coe v7 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
               -> coe
                    MAlonzo.Code.Algorithmic.C__'8759'__290
                    (d_sub_412
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe MAlonzo.Code.Algorithmic.du_mkCaseType_156 v6 v15) (coe v12))
                    (coe
                       du_sub'45'Cases_544 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v16) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.subcons
d_subcons_678 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_subcons_678 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_subcons_678 v5 v7 v8 v9
du_subcons_678 ::
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du_subcons_678 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Algorithmic.C_Z_22 -> coe v1
      MAlonzo.Code.Algorithmic.C_S_30 v8 -> coe v0 v2 v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution._[_]
d__'91'_'93'_702 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d__'91'_'93'_702 v0 v1 v2 v3 v4 v5
  = coe
      d_sub_412 (coe v0) (coe v0)
      (coe MAlonzo.Code.Algorithmic.C__'44'__12 v1 v3) (coe v1)
      (coe
         (\ v6 v7 ->
            coe
              MAlonzo.Code.Type.BetaNormal.C_ne_20
              (coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v7)))
      (coe
         du_subcons_678
         (coe (\ v6 v7 -> coe MAlonzo.Code.Algorithmic.C_'96'_184 v7))
         (coe v5))
      (coe v2) (coe v4)
-- Algorithmic.RenamingSubstitution.lem
d_lem_726 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_lem_726 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_lem_726 v5
du_lem_726 ::
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du_lem_726 v0
  = case coe v0 of
      MAlonzo.Code.Algorithmic.C_T_38 v4 v5
        -> coe MAlonzo.Code.Algorithmic.C_'96'_184 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution._[_]⋆
d__'91'_'93''8902'_740 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d__'91'_'93''8902'_740 v0 v1 v2 v3 v4 v5
  = coe
      d_sub_412
      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v2)) (coe v0)
      (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v1) (coe v1)
      (coe
         MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.du_subNf'45'cons_218
         (coe
            (\ v6 v7 ->
               coe
                 MAlonzo.Code.Type.BetaNormal.C_ne_20
                 (coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v7)))
         (coe v5))
      (coe (\ v6 -> coe du_lem_726)) (coe v3) (coe v4)
-- Algorithmic.RenamingSubstitution.Renˢ
d_Ren'738'_748 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 -> ()
d_Ren'738'_748 = erased
-- Algorithmic.RenamingSubstitution.extˢ
d_ext'738'_766 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16
d_ext'738'_766 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_ext'738'_766 v3 v5 v6
du_ext'738'_766 ::
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16
du_ext'738'_766 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Algorithmic.C_Z_22
        -> coe MAlonzo.Code.Algorithmic.C_Z_22
      MAlonzo.Code.Algorithmic.C_S_30 v7
        -> coe MAlonzo.Code.Algorithmic.C_S_30 (coe v0 v1 v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.extˢ⋆
d_ext'738''8902'_784 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16
d_ext'738''8902'_784 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_ext'738''8902'_784 v3 v6
du_ext'738''8902'_784 ::
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16
du_ext'738''8902'_784 v0 v1
  = case coe v1 of
      MAlonzo.Code.Algorithmic.C_T_38 v5 v6
        -> coe MAlonzo.Code.Algorithmic.C_T_38 v5 (coe v0 v5 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.renˢ
d_ren'738'_800 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_ren'738'_800 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Algorithmic.C_'96'_184 v7
        -> coe MAlonzo.Code.Algorithmic.C_'96'_184 (coe v3 v4 v7)
      MAlonzo.Code.Algorithmic.C_ƛ_190 v8
        -> case coe v4 of
             MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v10 v11
               -> coe
                    MAlonzo.Code.Algorithmic.C_ƛ_190
                    (d_ren'738'_800
                       (coe v0) (coe MAlonzo.Code.Algorithmic.C__'44'__12 v1 v10)
                       (coe MAlonzo.Code.Algorithmic.C__'44'__12 v2 v10)
                       (coe du_ext'738'_766 (coe v3)) (coe v11) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183'__196 v6 v8 v9
        -> coe
             MAlonzo.Code.Algorithmic.C__'183'__196 v6
             (d_ren'738'_800
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v6 v4) (coe v8))
             (d_ren'738'_800
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v9))
      MAlonzo.Code.Algorithmic.C_Λ_202 v8
        -> case coe v4 of
             MAlonzo.Code.Type.BetaNormal.C_Π_14 v10 v11
               -> coe
                    MAlonzo.Code.Algorithmic.C_Λ_202
                    (d_ren'738'_800
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v10))
                       (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v1)
                       (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v2)
                       (\ v12 v13 -> coe du_ext'738''8902'_784 (coe v3) v13) (coe v11)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v6 v8
             (d_ren'738'_800
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v6 v8) (coe v9))
             v10
      MAlonzo.Code.Algorithmic.C_wrap_220 v9
        -> case coe v4 of
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v11 v12 v13
               -> coe
                    MAlonzo.Code.Algorithmic.C_wrap_220
                    (d_ren'738'_800
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v0)
                          (coe MAlonzo.Code.Utils.C_'42'_704)
                          (coe
                             MAlonzo.Code.Type.C__'183'__30 v11
                             (coe
                                MAlonzo.Code.Type.C__'183'__30
                                (coe
                                   MAlonzo.Code.Utils.C__'8658'__708 (coe v11)
                                   (coe MAlonzo.Code.Utils.C_'42'_704))
                                (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                   (coe v0)
                                   (coe
                                      MAlonzo.Code.Utils.C__'8658'__708
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__708 (coe v11)
                                         (coe MAlonzo.Code.Utils.C_'42'_704))
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__708 (coe v11)
                                         (coe MAlonzo.Code.Utils.C_'42'_704)))
                                   (coe v12))
                                (coe
                                   MAlonzo.Code.Type.C_ƛ_28
                                   (coe
                                      MAlonzo.Code.Type.C_μ_32 v11
                                      (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                         (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v11))
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__708
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__708 (coe v11)
                                               (coe MAlonzo.Code.Utils.C_'42'_704))
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__708 (coe v11)
                                               (coe MAlonzo.Code.Utils.C_'42'_704)))
                                         (coe
                                            MAlonzo.Code.Type.BetaNormal.d_weakenNf_122 v0
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__708
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__708 (coe v11)
                                                  (coe MAlonzo.Code.Utils.C_'42'_704))
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__708 (coe v11)
                                                  (coe MAlonzo.Code.Utils.C_'42'_704)))
                                            v11 v12))
                                      (coe
                                         MAlonzo.Code.Type.C_'96'_22
                                         (coe MAlonzo.Code.Type.C_Z_16)))))
                             (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                (coe v0) (coe v11) (coe v13))))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_unwrap_230 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Algorithmic.C_unwrap_230 v6 v8 v9
             (d_ren'738'_800
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v6 v8 v9) (coe v10))
      MAlonzo.Code.Algorithmic.C_constr_240 v7 v9 v11
        -> case coe v4 of
             MAlonzo.Code.Type.BetaNormal.C_SOP_28 v13 v14
               -> coe
                    MAlonzo.Code.Algorithmic.C_constr_240 v7
                    (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v14) (coe v7))
                    (coe
                       du_ren'738''45'ConstrArgs_838 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v14) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_case_252 v6 v7 v9 v10
        -> coe
             MAlonzo.Code.Algorithmic.C_case_252 v6 v7
             (d_ren'738'_800
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v6 v7) (coe v9))
             (coe
                du_ren'738''45'Cases_874 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v7) (coe v10))
      MAlonzo.Code.Algorithmic.C_con_258 v6 v8
        -> coe MAlonzo.Code.Algorithmic.C_con_258 v6 v8
      MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v7
        -> coe MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v7
      MAlonzo.Code.Algorithmic.C_error_268
        -> coe MAlonzo.Code.Algorithmic.C_error_268
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.renˢ-List
d_ren'738''45'List_812 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
d_ren'738''45'List_812 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Utils.List.C_'91''93'_308 -> coe v5
      MAlonzo.Code.Utils.List.C__'8759'__314 v8 v9
        -> case coe v4 of
             (:) v10 v11
               -> coe
                    MAlonzo.Code.Utils.List.C__'8759'__314
                    (d_ren'738'_800
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v10) (coe v8))
                    (d_ren'738''45'List_812
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.renˢ-ConstrArgs
d_ren'738''45'ConstrArgs_838 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  Integer ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
d_ren'738''45'ConstrArgs_838 v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_ren'738''45'ConstrArgs_838 v0 v1 v2 v4 v5 v6 v7
du_ren'738''45'ConstrArgs_838 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
du_ren'738''45'ConstrArgs_838 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v5 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
               -> coe
                    d_ren'738''45'List_812 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Data.Vec.Base.du_lookup_82
                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10)
                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v8
        -> case coe v5 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
               -> coe
                    du_ren'738''45'ConstrArgs_838 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v8) (coe v11) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.renˢ-Cases
d_ren'738''45'Cases_874 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  Integer ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Algorithmic.T_Cases_172
d_ren'738''45'Cases_874 v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_ren'738''45'Cases_874 v0 v1 v2 v4 v5 v6 v7
du_ren'738''45'Cases_874 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Algorithmic.T_Cases_172
du_ren'738''45'Cases_874 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Algorithmic.C_'91''93'_278 -> coe v6
      MAlonzo.Code.Algorithmic.C__'8759'__290 v10 v11
        -> case coe v5 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v13 v14
               -> coe
                    MAlonzo.Code.Algorithmic.C__'8759'__290
                    (d_ren'738'_800
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe MAlonzo.Code.Algorithmic.du_mkCaseType_156 v4 v13) (coe v10))
                    (coe
                       du_ren'738''45'Cases_874 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v14) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.RenamingSubstitution.weakenˢ
d_weaken'738'_958 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_weaken'738'_958 v0 v1 v2 v3 v4
  = coe
      d_ren'738'_800 (coe v0) (coe v1)
      (coe MAlonzo.Code.Algorithmic.C__'44'__12 v1 v3)
      (coe (\ v5 -> coe MAlonzo.Code.Algorithmic.C_S_30)) (coe v2)
      (coe v4)
-- Algorithmic.RenamingSubstitution.extˢ-id
d_ext'738''45'id_972 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'738''45'id_972 = erased
-- Algorithmic.RenamingSubstitution.extˢ-comp
d_ext'738''45'comp_994 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'738''45'comp_994 = erased
-- Algorithmic.RenamingSubstitution.extˢ⋆-id
d_ext'738''8902''45'id_1008 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'738''8902''45'id_1008 = erased
-- Algorithmic.RenamingSubstitution.extˢ⋆-comp
d_ext'738''8902''45'comp_1030 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'738''8902''45'comp_1030 = erased
-- Algorithmic.RenamingSubstitution.extˢ-cong
d_ext'738''45'cong_1054 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'738''45'cong_1054 = erased
-- Algorithmic.RenamingSubstitution.extˢ⋆-cong
d_ext'738''8902''45'cong_1082 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'738''8902''45'cong_1082 = erased
-- Algorithmic.RenamingSubstitution.renˢ-cong
d_ren'738''45'cong_1106 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'cong_1106 = erased
-- Algorithmic.RenamingSubstitution.renˢ-List-cong
d_ren'738''45'List'45'cong_1126 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'List'45'cong_1126 = erased
-- Algorithmic.RenamingSubstitution.renˢ-ConstrArgs-cong
d_ren'738''45'ConstrArgs'45'cong_1158 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  Integer ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'ConstrArgs'45'cong_1158 = erased
-- Algorithmic.RenamingSubstitution.renˢ-Cases-cong
d_ren'738''45'Cases'45'cong_1196 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'Cases'45'cong_1196 = erased
-- Algorithmic.RenamingSubstitution.renˢ-id
d_ren'738''45'id_1284 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'id_1284 = erased
-- Algorithmic.RenamingSubstitution.renˢ-List-id
d_ren'738''45'List'45'id_1294 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'List'45'id_1294 = erased
-- Algorithmic.RenamingSubstitution.renˢ-ConstrArgs-id
d_ren'738''45'ConstrArgs'45'id_1312 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'ConstrArgs'45'id_1312 = erased
-- Algorithmic.RenamingSubstitution.renˢ-Cases-id
d_ren'738''45'Cases'45'id_1334 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'Cases'45'id_1334 = erased
-- Algorithmic.RenamingSubstitution.renˢ-comp
d_ren'738''45'comp_1402 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'comp_1402 = erased
-- Algorithmic.RenamingSubstitution.renˢ-List-comp
d_ren'738''45'List'45'comp_1420 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'List'45'comp_1420 = erased
-- Algorithmic.RenamingSubstitution.renˢ-ConstrArgs-comp
d_ren'738''45'ConstrArgs'45'comp_1446 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'ConstrArgs'45'comp_1446 = erased
-- Algorithmic.RenamingSubstitution.renˢ-Cases-comp
d_ren'738''45'Cases'45'comp_1476 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'738''45'Cases'45'comp_1476 = erased
-- Algorithmic.RenamingSubstitution.Subˢ
d_Sub'738'_1530 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 -> ()
d_Sub'738'_1530 = erased
-- Algorithmic.RenamingSubstitution.extsˢ
d_exts'738'_1548 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_exts'738'_1548 v0 ~v1 v2 v3 v4 v5 v6
  = du_exts'738'_1548 v0 v2 v3 v4 v5 v6
du_exts'738'_1548 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  (MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
   MAlonzo.Code.Algorithmic.T__'8715'__16 ->
   MAlonzo.Code.Algorithmic.T__'8866'__178) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du_exts'738'_1548 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Algorithmic.C_Z_22
        -> coe
             MAlonzo.Code.Algorithmic.C_'96'_184
             (coe MAlonzo.Code.Algorithmic.C_Z_22)
      MAlonzo.Code.Algorithmic.C_S_30 v10
        -> coe
             d_weaken'738'_958 (coe v0) (coe v1) (coe v4) (coe v3)
             (coe v2 v4 v10)
      _ -> MAlonzo.RTE.mazUnreachableError
