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

module MAlonzo.Code.Algorithmic.Erasure where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Declarative
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Algorithmic.Erasure.len⋆
d_len'8902'_4 :: MAlonzo.Code.Type.T_Ctx'8902'_2 -> Integer
d_len'8902'_4 v0
  = case coe v0 of
      MAlonzo.Code.Type.C_'8709'_4 -> coe (0 :: Integer)
      MAlonzo.Code.Type.C__'44''8902'__6 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe d_len'8902'_4 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Erasure.len
d_len_12 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 -> Integer
d_len_12 v0 v1
  = case coe v1 of
      MAlonzo.Code.Algorithmic.C_'8709'_4 -> coe (0 :: Integer)
      MAlonzo.Code.Algorithmic.C__'44''8902'__8 v3
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v5 v6
               -> coe d_len_12 (coe v5) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'44'__12 v3 v4
        -> coe addInt (coe (1 :: Integer)) (coe d_len_12 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Erasure.eraseVar
d_eraseVar_28 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_eraseVar_28 v0 v1 ~v2 v3 = du_eraseVar_28 v0 v1 v3
du_eraseVar_28 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_eraseVar_28 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Algorithmic.C_Z_22
        -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      MAlonzo.Code.Algorithmic.C_S_30 v7
        -> case coe v1 of
             MAlonzo.Code.Algorithmic.C__'44'__12 v9 v10
               -> coe
                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                    (coe du_eraseVar_28 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_T_38 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Algorithmic.C__'44''8902'__8 v11
                      -> coe du_eraseVar_28 (coe v8) (coe v11) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Erasure.eraseTC
d_eraseTC_36 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  AgdaAny -> MAlonzo.Code.RawU.T_TmCon_202
d_eraseTC_36 v0 v1
  = coe
      MAlonzo.Code.RawU.C_tmCon_206
      (coe MAlonzo.Code.Algorithmic.d_ty2sty_64 (coe v0)) (coe v1)
-- Algorithmic.Erasure.erase
d_erase_48 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_erase_48 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Algorithmic.C_'96'_184 v5
        -> coe
             MAlonzo.Code.Untyped.C_'96'_18
             (coe du_eraseVar_28 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Algorithmic.C_ƛ_190 v6
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v8 v9
               -> coe
                    MAlonzo.Code.Untyped.C_ƛ_20
                    (coe
                       d_erase_48 (coe v0)
                       (coe MAlonzo.Code.Algorithmic.C__'44'__12 v1 v8) (coe v9) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183'__196 v4 v6 v7
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22
             (coe
                d_erase_48 (coe v0) (coe v1)
                (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v4 v2) (coe v6))
             (coe d_erase_48 (coe v0) (coe v1) (coe v4) (coe v7))
      MAlonzo.Code.Algorithmic.C_Λ_202 v6
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C_Π_14 v8 v9
               -> coe
                    MAlonzo.Code.Untyped.C_delay_26
                    (coe
                       d_erase_48
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                       (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v1) (coe v9)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v4 v6 v7 v8
        -> coe
             MAlonzo.Code.Untyped.C_force_24
             (coe
                d_erase_48 (coe v0) (coe v1)
                (coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v4 v6) (coe v7))
      MAlonzo.Code.Algorithmic.C_wrap_220 v7
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v9 v10 v11
               -> coe
                    d_erase_48 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v0)
                       (coe MAlonzo.Code.Utils.C_'42'_756)
                       (coe
                          MAlonzo.Code.Type.C__'183'__30 v9
                          (coe
                             MAlonzo.Code.Type.C__'183'__30
                             (coe
                                MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                (coe MAlonzo.Code.Utils.C_'42'_756))
                             (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                (coe v0)
                                (coe
                                   MAlonzo.Code.Utils.C__'8658'__760
                                   (coe
                                      MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                      (coe MAlonzo.Code.Utils.C_'42'_756))
                                   (coe
                                      MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                      (coe MAlonzo.Code.Utils.C_'42'_756)))
                                (coe v10))
                             (coe
                                MAlonzo.Code.Type.C_ƛ_28
                                (coe
                                   MAlonzo.Code.Type.C_μ_32 v9
                                   (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v9))
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__760
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                            (coe MAlonzo.Code.Utils.C_'42'_756))
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                            (coe MAlonzo.Code.Utils.C_'42'_756)))
                                      (coe
                                         MAlonzo.Code.Type.BetaNormal.d_weakenNf_122 v0
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__760
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                               (coe MAlonzo.Code.Utils.C_'42'_756))
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                               (coe MAlonzo.Code.Utils.C_'42'_756)))
                                         v9 v10))
                                   (coe
                                      MAlonzo.Code.Type.C_'96'_22 (coe MAlonzo.Code.Type.C_Z_16)))))
                          (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                             (coe v0) (coe v9) (coe v11))))
                    (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_unwrap_230 v4 v6 v7 v8
        -> coe
             d_erase_48 (coe v0) (coe v1)
             (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v4 v6 v7) (coe v8)
      MAlonzo.Code.Algorithmic.C_constr_240 v5 v7 v9
        -> coe
             MAlonzo.Code.Untyped.C_constr_34
             (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v5))
             (coe d_erase'45'ConstrArgs_58 (coe v0) (coe v1) (coe v7) (coe v9))
      MAlonzo.Code.Algorithmic.C_case_252 v4 v5 v7 v8
        -> coe
             MAlonzo.Code.Untyped.C_case_40
             (coe
                d_erase_48 (coe v0) (coe v1)
                (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v4 v5) (coe v7))
             (coe
                du_erase'45'Cases_76 (coe v0) (coe v1) (coe v2) (coe v5) (coe v8))
      MAlonzo.Code.Algorithmic.C_con_258 v4 v6
        -> coe
             MAlonzo.Code.Untyped.C_con_28 (coe d_eraseTC_36 (coe v4) (coe v6))
      MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v5
        -> coe MAlonzo.Code.Untyped.C_builtin_44 (coe v5)
      MAlonzo.Code.Algorithmic.C_error_268
        -> coe MAlonzo.Code.Untyped.C_error_46
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Erasure.erase-ConstrArgs
d_erase'45'ConstrArgs_58 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_erase'45'ConstrArgs_58 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Utils.List.C_'91''93'_308
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Utils.List.C__'8759'__314 v6 v7
        -> case coe v2 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe d_erase_48 (coe v0) (coe v1) (coe v8) (coe v6))
                    (coe d_erase'45'ConstrArgs_58 (coe v0) (coe v1) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Erasure.erase-Cases
d_erase'45'Cases_76 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_erase'45'Cases_76 v0 v1 v2 ~v3 v4 v5
  = du_erase'45'Cases_76 v0 v1 v2 v4 v5
du_erase'45'Cases_76 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
du_erase'45'Cases_76 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Algorithmic.C_'91''93'_278
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Algorithmic.C__'8759'__290 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       d_erase_48 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Algorithmic.du_mkCaseType_156 v2 v11) (coe v8))
                    (coe
                       du_erase'45'Cases_76 (coe v0) (coe v1) (coe v2) (coe v12) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Erasure.lenLemma
d_lenLemma_130 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lenLemma_130 = erased
-- Algorithmic.Erasure.lenLemma⋆
d_lenLemma'8902'_142 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lenLemma'8902'_142 = erased
-- Algorithmic.Erasure.lemzero
d_lemzero_154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemzero_154 = erased
-- Algorithmic.Erasure.lemsuc
d_lemsuc_166 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemsuc_166 = erased
-- Algorithmic.Erasure.lem≡Ctx
d_lem'8801'Ctx_176 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8801'Ctx_176 = erased
-- Algorithmic.Erasure.lem-conv∋
d_lem'45'conv'8715'_194 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45'conv'8715'_194 = erased
-- Algorithmic.Erasure.sameVar
d_sameVar_206 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sameVar_206 = erased
-- Algorithmic.Erasure.lemVar
d_lemVar_228 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemVar_228 = erased
-- Algorithmic.Erasure.lemƛ
d_lemƛ_242 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemƛ_242 = erased
-- Algorithmic.Erasure.lem·
d_lem'183'_256 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'183'_256 = erased
-- Algorithmic.Erasure.lem-delay
d_lem'45'delay_270 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45'delay_270 = erased
-- Algorithmic.Erasure.lem-force
d_lem'45'force_282 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45'force_282 = erased
-- Algorithmic.Erasure.lemcon'
d_lemcon''_294 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.RawU.T_TmCon_202 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemcon''_294 = erased
-- Algorithmic.Erasure.lemerror
d_lemerror_304 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemerror_304 = erased
-- Algorithmic.Erasure.lembuiltin
d_lembuiltin_314 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lembuiltin_314 = erased
-- Algorithmic.Erasure.lemConstr
d_lemConstr_328 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemConstr_328 = erased
-- Algorithmic.Erasure.lemCase
d_lemCase_350 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemCase_350 = erased
-- Algorithmic.Erasure.lem-erase
d_lem'45'erase_372 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45'erase_372 = erased
-- Algorithmic.Erasure.lem-subst
d_lem'45'subst_382 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45'subst_382 = erased
-- Algorithmic.Erasure.lem-erase'
d_lem'45'erase''_398 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45'erase''_398 = erased
-- Algorithmic.Erasure.lem-erase''
d_lem'45'erase''''_420 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45'erase''''_420 = erased
-- Algorithmic.Erasure.same
d_same_432 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same_432 = erased
-- Algorithmic.Erasure.+cancel
d_'43'cancel_442 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43'cancel_442 = erased
-- Algorithmic.Erasure.same-ConstrArgs
d_same'45'ConstrArgs_454 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same'45'ConstrArgs_454 = erased
-- Algorithmic.Erasure.same-mkCaseType
d_same'45'mkCaseType_478 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same'45'mkCaseType_478 = erased
-- Algorithmic.Erasure.same-Cases
d_same'45'Cases_494 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Declarative.T_Cases_104 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same'45'Cases_494 = erased
-- Algorithmic.Erasure.same'Len
d_same''Len_596 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same''Len_596 = erased
-- Algorithmic.Erasure.lem-Dconv∋
d_lem'45'Dconv'8715'_622 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Declarative.T__'8715'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45'Dconv'8715'_622 = erased
-- Algorithmic.Erasure.same'Var
d_same''Var_634 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same''Var_634 = erased
-- Algorithmic.Erasure.same'TC
d_same''TC_656 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same''TC_656 = erased
-- Algorithmic.Erasure.same'
d_same''_674 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same''_674 = erased
-- Algorithmic.Erasure.same'ConstrArgs
d_same''ConstrArgs_684 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same''ConstrArgs_684 = erased
-- Algorithmic.Erasure.same-subst
d_same'45'subst_702 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Declarative.T__'8866'__110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same'45'subst_702 = erased
-- Algorithmic.Erasure.same'Case
d_same''Case_718 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_same''Case_718 = erased
