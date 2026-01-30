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

module MAlonzo.Code.Scoped.Extrication where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Scoped
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Scoped.Extrication.len⋆
d_len'8902'_4 :: MAlonzo.Code.Type.T_Ctx'8902'_2 -> Integer
d_len'8902'_4 v0
  = case coe v0 of
      MAlonzo.Code.Type.C_'8709'_4 -> coe (0 :: Integer)
      MAlonzo.Code.Type.C__'44''8902'__6 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe d_len'8902'_4 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.extricateVar⋆
d_extricateVar'8902'_16 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_extricateVar'8902'_16 v0 ~v1 v2 = du_extricateVar'8902'_16 v0 v2
du_extricateVar'8902'_16 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_extricateVar'8902'_16 v0 v1
  = case coe v1 of
      MAlonzo.Code.Type.C_Z_16
        -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      MAlonzo.Code.Type.C_S_18 v5
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v6 v7
               -> coe
                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                    (coe du_extricateVar'8902'_16 (coe v6) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.extricateNf⋆
d_extricateNf'8902'_26 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Scoped.T_ScopedTy_14
d_extricateNf'8902'_26 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Type.BetaNormal.C_Π_14 v4 v5
        -> coe
             MAlonzo.Code.Scoped.C_Π_22 (coe v4)
             (coe
                d_extricateNf'8902'_26
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v4))
                (coe MAlonzo.Code.Utils.C_'42'_684) (coe v5))
      MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v4 v5
        -> coe
             MAlonzo.Code.Scoped.C__'8658'__20
             (coe
                d_extricateNf'8902'_26 (coe v0) (coe MAlonzo.Code.Utils.C_'42'_684)
                (coe v4))
             (coe
                d_extricateNf'8902'_26 (coe v0) (coe MAlonzo.Code.Utils.C_'42'_684)
                (coe v5))
      MAlonzo.Code.Type.BetaNormal.C_ƛ_18 v6
        -> case coe v1 of
             MAlonzo.Code.Utils.C__'8658'__688 v7 v8
               -> coe
                    MAlonzo.Code.Scoped.C_ƛ_24 (coe v7)
                    (coe
                       d_extricateNf'8902'_26
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v7)) (coe v8)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Type.BetaNormal.C_ne_20 v5
        -> coe d_extricateNe'8902'_34 (coe v0) (coe v1) (coe v5)
      MAlonzo.Code.Type.BetaNormal.C_con_22 v4
        -> case coe v4 of
             MAlonzo.Code.Type.BetaNormal.C_ne_20 v7
               -> coe
                    d_extricateNe'8902'_34 (coe v0)
                    (coe MAlonzo.Code.Utils.C_'9839'_686) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Type.BetaNormal.C_μ_24 v4 v5 v6
        -> coe
             MAlonzo.Code.Scoped.C_μ_32
             (coe
                d_extricateNf'8902'_26 (coe v0)
                (coe
                   MAlonzo.Code.Utils.C__'8658'__688
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__688 (coe v4)
                      (coe MAlonzo.Code.Utils.C_'42'_684))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__688 (coe v4)
                      (coe MAlonzo.Code.Utils.C_'42'_684)))
                (coe v5))
             (coe d_extricateNf'8902'_26 (coe v0) (coe v4) (coe v6))
      MAlonzo.Code.Type.BetaNormal.C_SOP_28 v4 v5
        -> coe
             MAlonzo.Code.Scoped.C_SOP_34
             (coe
                du_extricateNf'8902''45'VecList_56 (coe v0)
                (coe MAlonzo.Code.Utils.C_'42'_684) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.extricateNe⋆
d_extricateNe'8902'_34 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6 ->
  MAlonzo.Code.Scoped.T_ScopedTy_14
d_extricateNe'8902'_34 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Type.BetaNormal.C_'96'_8 v5
        -> coe
             MAlonzo.Code.Scoped.C_'96'_18
             (coe du_extricateVar'8902'_16 (coe v0) (coe v5))
      MAlonzo.Code.Type.BetaNormal.C__'183'__10 v4 v6 v7
        -> coe
             MAlonzo.Code.Scoped.C__'183'__26
             (coe
                d_extricateNe'8902'_34 (coe v0)
                (coe MAlonzo.Code.Utils.C__'8658'__688 (coe v4) (coe v1)) (coe v6))
             (coe d_extricateNf'8902'_26 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Type.BetaNormal.C_'94'_12 v5
        -> coe MAlonzo.Code.Scoped.C_con_30 (coe v1) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.extricateNf⋆-List
d_extricateNf'8902''45'List_42 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.T_List_414 MAlonzo.Code.Scoped.T_ScopedTy_14
d_extricateNf'8902''45'List_42 v0 v1 v2
  = case coe v2 of
      [] -> coe MAlonzo.Code.Utils.C_'91''93'_418
      (:) v3 v4
        -> coe
             MAlonzo.Code.Utils.C__'8759'__420
             (coe d_extricateNf'8902'_26 (coe v0) (coe v1) (coe v3))
             (coe d_extricateNf'8902''45'List_42 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.extricateNf⋆-VecList
d_extricateNf'8902''45'VecList_56 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.T_List_414
    (MAlonzo.Code.Utils.T_List_414 MAlonzo.Code.Scoped.T_ScopedTy_14)
d_extricateNf'8902''45'VecList_56 v0 v1 ~v2 v3
  = du_extricateNf'8902''45'VecList_56 v0 v1 v3
du_extricateNf'8902''45'VecList_56 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Utils.T_List_414
    (MAlonzo.Code.Utils.T_List_414 MAlonzo.Code.Scoped.T_ScopedTy_14)
du_extricateNf'8902''45'VecList_56 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe MAlonzo.Code.Utils.C_'91''93'_418
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
        -> coe
             MAlonzo.Code.Utils.C__'8759'__420
             (coe d_extricateNf'8902''45'List_42 (coe v0) (coe v1) (coe v4))
             (coe du_extricateNf'8902''45'VecList_56 (coe v0) (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.len
d_len_94 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 -> MAlonzo.Code.Scoped.T_Weirdℕ_42
d_len_94 v0 v1
  = case coe v1 of
      MAlonzo.Code.Algorithmic.C_'8709'_4
        -> coe MAlonzo.Code.Scoped.C_Z_44
      MAlonzo.Code.Algorithmic.C__'44''8902'__8 v3
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v5 v6
               -> coe MAlonzo.Code.Scoped.C_T_52 (d_len_94 (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'44'__12 v3 v4
        -> coe MAlonzo.Code.Scoped.C_S_48 (d_len_94 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.extricateVar
d_extricateVar_110 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Scoped.T_WeirdFin_56
d_extricateVar_110 v0 v1 ~v2 v3 = du_extricateVar_110 v0 v1 v3
du_extricateVar_110 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Scoped.T_WeirdFin_56
du_extricateVar_110 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Algorithmic.C_Z_22 -> coe MAlonzo.Code.Scoped.C_Z_62
      MAlonzo.Code.Algorithmic.C_S_30 v7
        -> case coe v1 of
             MAlonzo.Code.Algorithmic.C__'44'__12 v9 v10
               -> coe
                    MAlonzo.Code.Scoped.C_S_68
                    (coe du_extricateVar_110 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_T_38 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Algorithmic.C__'44''8902'__8 v11
                      -> coe
                           MAlonzo.Code.Scoped.C_T_74
                           (coe du_extricateVar_110 (coe v8) (coe v11) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.extricateSub
d_extricateSub_122 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_extricateSub_122 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Type.C_'8709'_4
        -> coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
      MAlonzo.Code.Type.C__'44''8902'__6 v3 v4
        -> coe
             MAlonzo.Code.Data.Vec.Base.du__'43''43'__188
             (coe
                d_extricateSub_122 (coe v0) (coe v3)
                (coe (\ v5 v6 -> coe v2 v5 (coe MAlonzo.Code.Type.C_S_18 v6))))
             (coe
                MAlonzo.Code.Data.Vec.Base.du_'91'_'93'_438
                (coe
                   d_extricateNf'8902'_26 (coe v0) (coe v4)
                   (coe v2 v4 (coe MAlonzo.Code.Type.C_Z_16))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.extricate
d_extricate_140 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Scoped.T_ScopedTm_522
d_extricate_140 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Algorithmic.C_'96'_184 v5
        -> coe
             MAlonzo.Code.Scoped.C_'96'_528
             (coe du_extricateVar_110 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Algorithmic.C_ƛ_190 v6
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v8 v9
               -> coe
                    MAlonzo.Code.Scoped.C_ƛ_534
                    (coe
                       d_extricateNf'8902'_26 (coe v0) (coe MAlonzo.Code.Utils.C_'42'_684)
                       (coe v8))
                    (coe
                       d_extricate_140 (coe v0)
                       (coe MAlonzo.Code.Algorithmic.C__'44'__12 v1 v8) (coe v9) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183'__196 v4 v6 v7
        -> coe
             MAlonzo.Code.Scoped.C__'183'__536
             (coe
                d_extricate_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v4 v2) (coe v6))
             (coe d_extricate_140 (coe v0) (coe v1) (coe v4) (coe v7))
      MAlonzo.Code.Algorithmic.C_Λ_202 v6
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C_Π_14 v8 v9
               -> coe
                    MAlonzo.Code.Scoped.C_Λ_530 (coe v8)
                    (coe
                       d_extricate_140
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                       (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v1) (coe v9)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v4 v6 v7 v8
        -> coe
             MAlonzo.Code.Scoped.C__'183''8902'__532
             (coe
                d_extricate_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v4 v6) (coe v7))
             (coe d_extricateNf'8902'_26 (coe v0) (coe v4) (coe v8))
      MAlonzo.Code.Algorithmic.C_wrap_220 v7
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v9 v10 v11
               -> coe
                    MAlonzo.Code.Scoped.C_wrap_546
                    (coe
                       d_extricateNf'8902'_26 (coe v0)
                       (coe
                          MAlonzo.Code.Utils.C__'8658'__688
                          (coe
                             MAlonzo.Code.Utils.C__'8658'__688 (coe v9)
                             (coe MAlonzo.Code.Utils.C_'42'_684))
                          (coe
                             MAlonzo.Code.Utils.C__'8658'__688 (coe v9)
                             (coe MAlonzo.Code.Utils.C_'42'_684)))
                       (coe v10))
                    (coe d_extricateNf'8902'_26 (coe v0) (coe v9) (coe v11))
                    (coe
                       d_extricate_140 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v0)
                          (coe MAlonzo.Code.Utils.C_'42'_684)
                          (coe
                             MAlonzo.Code.Type.C__'183'__30 v9
                             (coe
                                MAlonzo.Code.Type.C__'183'__30
                                (coe
                                   MAlonzo.Code.Utils.C__'8658'__688 (coe v9)
                                   (coe MAlonzo.Code.Utils.C_'42'_684))
                                (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                   (coe v0)
                                   (coe
                                      MAlonzo.Code.Utils.C__'8658'__688
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__688 (coe v9)
                                         (coe MAlonzo.Code.Utils.C_'42'_684))
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__688 (coe v9)
                                         (coe MAlonzo.Code.Utils.C_'42'_684)))
                                   (coe v10))
                                (coe
                                   MAlonzo.Code.Type.C_ƛ_28
                                   (coe
                                      MAlonzo.Code.Type.C_μ_32 v9
                                      (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                         (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v9))
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__688
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__688 (coe v9)
                                               (coe MAlonzo.Code.Utils.C_'42'_684))
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__688 (coe v9)
                                               (coe MAlonzo.Code.Utils.C_'42'_684)))
                                         (coe
                                            MAlonzo.Code.Type.BetaNormal.d_weakenNf_122 v0
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__688
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__688 (coe v9)
                                                  (coe MAlonzo.Code.Utils.C_'42'_684))
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__688 (coe v9)
                                                  (coe MAlonzo.Code.Utils.C_'42'_684)))
                                            v9 v10))
                                      (coe
                                         MAlonzo.Code.Type.C_'96'_22
                                         (coe MAlonzo.Code.Type.C_Z_16)))))
                             (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                (coe v0) (coe v9) (coe v11))))
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_unwrap_230 v4 v6 v7 v8
        -> coe
             MAlonzo.Code.Scoped.C_unwrap_548
             (coe
                d_extricate_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v4 v6 v7) (coe v8))
      MAlonzo.Code.Algorithmic.C_constr_240 v5 v7 v9
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C_SOP_28 v11 v12
               -> coe
                    MAlonzo.Code.Scoped.C_constr_556
                    (coe
                       d_extricateNf'8902'_26 (coe v0) (coe MAlonzo.Code.Utils.C_'42'_684)
                       (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v11 v12))
                    (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v5))
                    (coe
                       d_extricate'45'ConstrArgs_148 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v12) (coe v5))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_case_252 v4 v5 v7 v8
        -> coe
             MAlonzo.Code.Scoped.C_case_564
             (coe
                d_extricateNf'8902'_26 (coe v0) (coe MAlonzo.Code.Utils.C_'42'_684)
                (coe v2))
             (coe
                d_extricate_140 (coe v0) (coe v1)
                (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v4 v5) (coe v7))
             (coe
                du_extricate'45'Cases_166 (coe v0) (coe v1) (coe v2) (coe v5)
                (coe v8))
      MAlonzo.Code.Algorithmic.C_con_258 v4 v6
        -> coe
             MAlonzo.Code.Scoped.C_con_538
             (coe
                MAlonzo.Code.RawU.C_tmCon_206
                (coe MAlonzo.Code.Algorithmic.d_ty2sty_64 (coe v4)) (coe v6))
      MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v5
        -> coe MAlonzo.Code.Scoped.C_builtin_544 (coe v5)
      MAlonzo.Code.Algorithmic.C_error_268
        -> coe
             MAlonzo.Code.Scoped.C_error_540
             (coe
                d_extricateNf'8902'_26 (coe v0) (coe MAlonzo.Code.Utils.C_'42'_684)
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.extricate-ConstrArgs
d_extricate'45'ConstrArgs_148 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.T_List_414 MAlonzo.Code.Scoped.T_ScopedTm_522
d_extricate'45'ConstrArgs_148 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Utils.List.C_'91''93'_308
        -> coe MAlonzo.Code.Utils.C_'91''93'_418
      MAlonzo.Code.Utils.List.C__'8759'__314 v6 v7
        -> case coe v2 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Utils.C__'8759'__420
                    (coe d_extricate_140 (coe v0) (coe v1) (coe v8) (coe v6))
                    (coe
                       d_extricate'45'ConstrArgs_148 (coe v0) (coe v1) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.Extrication.extricate-Cases
d_extricate'45'Cases_166 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Utils.T_List_414 MAlonzo.Code.Scoped.T_ScopedTm_522
d_extricate'45'Cases_166 v0 v1 v2 ~v3 v4 v5
  = du_extricate'45'Cases_166 v0 v1 v2 v4 v5
du_extricate'45'Cases_166 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Utils.T_List_414 MAlonzo.Code.Scoped.T_ScopedTm_522
du_extricate'45'Cases_166 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Algorithmic.C_'91''93'_278
        -> coe MAlonzo.Code.Utils.C_'91''93'_418
      MAlonzo.Code.Algorithmic.C__'8759'__290 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
               -> coe
                    MAlonzo.Code.Utils.C__'8759'__420
                    (coe
                       d_extricate_140 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Algorithmic.du_mkCaseType_156 v2 v11) (coe v8))
                    (coe
                       du_extricate'45'Cases_166 (coe v0) (coe v1) (coe v2) (coe v12)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
