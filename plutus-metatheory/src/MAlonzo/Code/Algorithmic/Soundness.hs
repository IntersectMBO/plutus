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

module MAlonzo.Code.Algorithmic.Soundness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Declarative
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNBE.Soundness
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Type.Equality
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Algorithmic.Soundness.embCtx
d_embCtx_6 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Declarative.T_Ctx_16
d_embCtx_6 v0 v1
  = case coe v1 of
      MAlonzo.Code.Algorithmic.C_'8709'_4
        -> coe MAlonzo.Code.Declarative.C_'8709'_18
      MAlonzo.Code.Algorithmic.C__'44''8902'__8 v3
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v5 v6
               -> coe
                    MAlonzo.Code.Declarative.C__'44''8902'__22
                    (d_embCtx_6 (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'44'__12 v3 v4
        -> coe
             MAlonzo.Code.Declarative.C__'44'__26 (d_embCtx_6 (coe v0) (coe v3))
             (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Soundness.embVar
d_embVar_22 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Declarative.T__'8715'__34
d_embVar_22 v0 v1 ~v2 v3 = du_embVar_22 v0 v1 v3
du_embVar_22 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Algorithmic.T__'8715'__16 ->
  MAlonzo.Code.Declarative.T__'8715'__34
du_embVar_22 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Algorithmic.C_Z_22
        -> coe MAlonzo.Code.Declarative.C_Z_36
      MAlonzo.Code.Algorithmic.C_S_30 v7
        -> case coe v1 of
             MAlonzo.Code.Algorithmic.C__'44'__12 v9 v10
               -> coe
                    MAlonzo.Code.Declarative.C_S_38
                    (coe du_embVar_22 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_T_38 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Type.C__'44''8902'__6 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Algorithmic.C__'44''8902'__8 v11
                      -> coe
                           MAlonzo.Code.Declarative.C_T_40
                           (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                              (coe v8) (coe MAlonzo.Code.Utils.C_'42'_756) (coe v6))
                           (coe du_embVar_22 (coe v8) (coe v11) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Soundness.emb[]
d_emb'91''93'_38 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
d_emb'91''93'_38 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Type.Equality.C_trans'8801'β_18
      (MAlonzo.Code.Type.BetaNormal.d_embNf_128
         (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
         (coe
            MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v0)
            (coe MAlonzo.Code.Utils.C_'42'_756)
            (coe
               MAlonzo.Code.Type.RenamingSubstitution.d__'91'_'93'_432 (coe v0)
               (coe v1) (coe MAlonzo.Code.Utils.C_'42'_756)
               (coe
                  MAlonzo.Code.Type.BetaNormal.d_embNf_128
                  (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v1))
                  (coe MAlonzo.Code.Utils.C_'42'_756) (coe v3))
               (coe
                  MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v1)
                  (coe v2)))))
      (MAlonzo.Code.Type.BetaNBE.Soundness.d_soundness_470
         (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
         (coe
            MAlonzo.Code.Type.RenamingSubstitution.d__'91'_'93'_432 (coe v0)
            (coe v1) (coe MAlonzo.Code.Utils.C_'42'_756)
            (coe
               MAlonzo.Code.Type.BetaNormal.d_embNf_128
               (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v1))
               (coe MAlonzo.Code.Utils.C_'42'_756) (coe v3))
            (coe
               MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v1)
               (coe v2))))
      (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
-- Algorithmic.Soundness.soundness-μ
d_soundness'45'μ_60 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
d_soundness'45'μ_60 v0 ~v1 v2 ~v3 v4 v5
  = du_soundness'45'μ_60 v0 v2 v4 v5
du_soundness'45'μ_60 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_754 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
du_soundness'45'μ_60 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Type.Equality.C_trans'8801'β_18
      (MAlonzo.Code.Type.BetaNormal.d_embNf_128
         (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
         (coe
            MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v0)
            (coe MAlonzo.Code.Utils.C_'42'_756)
            (coe
               MAlonzo.Code.Type.C__'183'__30 v1
               (coe
                  MAlonzo.Code.Type.C__'183'__30
                  (coe
                     MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                     (coe MAlonzo.Code.Utils.C_'42'_756))
                  (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                     (coe v0)
                     (coe
                        MAlonzo.Code.Utils.C__'8658'__760
                        (coe
                           MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                           (coe MAlonzo.Code.Utils.C_'42'_756))
                        (coe
                           MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                           (coe MAlonzo.Code.Utils.C_'42'_756)))
                     (coe v2))
                  (coe
                     MAlonzo.Code.Type.C_ƛ_28
                     (coe
                        MAlonzo.Code.Type.C_μ_32 v1
                        (coe
                           MAlonzo.Code.Type.RenamingSubstitution.d_weaken_98 v0
                           (coe
                              MAlonzo.Code.Utils.C__'8658'__760
                              (coe
                                 MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                                 (coe MAlonzo.Code.Utils.C_'42'_756))
                              (coe
                                 MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                                 (coe MAlonzo.Code.Utils.C_'42'_756)))
                           v1
                           (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Utils.C__'8658'__760
                                 (coe
                                    MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                                    (coe MAlonzo.Code.Utils.C_'42'_756))
                                 (coe
                                    MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                                    (coe MAlonzo.Code.Utils.C_'42'_756)))
                              (coe v2)))
                        (coe MAlonzo.Code.Type.C_'96'_22 (coe MAlonzo.Code.Type.C_Z_16)))))
               (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                  (coe v0) (coe v1) (coe v3)))))
      (MAlonzo.Code.Type.BetaNBE.Soundness.d_soundness_470
         (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
         (coe
            MAlonzo.Code.Type.C__'183'__30 v1
            (coe
               MAlonzo.Code.Type.C__'183'__30
               (coe
                  MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                  (coe MAlonzo.Code.Utils.C_'42'_756))
               (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                  (coe v0)
                  (coe
                     MAlonzo.Code.Utils.C__'8658'__760
                     (coe
                        MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                        (coe MAlonzo.Code.Utils.C_'42'_756))
                     (coe
                        MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                        (coe MAlonzo.Code.Utils.C_'42'_756)))
                  (coe v2))
               (coe
                  MAlonzo.Code.Type.C_ƛ_28
                  (coe
                     MAlonzo.Code.Type.C_μ_32 v1
                     (coe
                        MAlonzo.Code.Type.RenamingSubstitution.d_weaken_98 v0
                        (coe
                           MAlonzo.Code.Utils.C__'8658'__760
                           (coe
                              MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                              (coe MAlonzo.Code.Utils.C_'42'_756))
                           (coe
                              MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                              (coe MAlonzo.Code.Utils.C_'42'_756)))
                        v1
                        (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                           (coe v0)
                           (coe
                              MAlonzo.Code.Utils.C__'8658'__760
                              (coe
                                 MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                                 (coe MAlonzo.Code.Utils.C_'42'_756))
                              (coe
                                 MAlonzo.Code.Utils.C__'8658'__760 (coe v1)
                                 (coe MAlonzo.Code.Utils.C_'42'_756)))
                           (coe v2)))
                     (coe MAlonzo.Code.Type.C_'96'_22 (coe MAlonzo.Code.Type.C_Z_16)))))
            (MAlonzo.Code.Type.BetaNormal.d_embNf_128
               (coe v0) (coe v1) (coe v3))))
      (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
-- Algorithmic.Soundness.lemσ'
d_lemσ''_108 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
d_lemσ''_108 v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10
  = du_lemσ''_108 v0 v2 v6 v9
du_lemσ''_108 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
du_lemσ''_108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Type.Equality.C_trans'8801'β_18
      (MAlonzo.Code.Type.BetaNormal.d_embNf_128
         (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
         (coe
            MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v0)
            (coe MAlonzo.Code.Utils.C_'42'_756)
            (coe
               MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v1) (coe v0)
               (coe
                  (\ v4 v5 ->
                     MAlonzo.Code.Type.BetaNormal.d_embNf_128
                       (coe v0) (coe v4) (coe v3 v4 v5)))
               (coe MAlonzo.Code.Utils.C_'42'_756) (coe v2))))
      (MAlonzo.Code.Type.BetaNBE.Soundness.d_soundness_470
         (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
         (coe
            MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v1) (coe v0)
            (coe
               (\ v4 v5 ->
                  MAlonzo.Code.Type.BetaNormal.d_embNf_128
                    (coe v0) (coe v4) (coe v3 v4 v5)))
            (coe MAlonzo.Code.Utils.C_'42'_756) (coe v2)))
      (coe
         MAlonzo.Code.Type.Equality.C_trans'8801'β_18
         (MAlonzo.Code.Type.BetaNormal.d_embNf_128
            (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
            (coe
               MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v1)
               (coe MAlonzo.Code.Utils.C_'42'_756) (coe v2)
               (coe
                  (\ v4 v5 ->
                     MAlonzo.Code.Type.BetaNBE.d_eval_166
                       (coe v0) (coe v0) (coe v4)
                       (coe
                          MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v4)
                          (coe v3 v4 v5))
                       (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))))
         (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
         (coe
            MAlonzo.Code.Type.Equality.C_trans'8801'β_18
            (MAlonzo.Code.Type.BetaNormal.d_embNf_128
               (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
               (coe
                  MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v1)
                  (coe MAlonzo.Code.Utils.C_'42'_756)
                  (coe
                     MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v1)
                     (coe MAlonzo.Code.Utils.C_'42'_756)
                     (coe
                        MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v1)
                        (coe MAlonzo.Code.Utils.C_'42'_756) (coe v2)))
                  (coe
                     (\ v4 v5 ->
                        MAlonzo.Code.Type.BetaNBE.d_eval_166
                          (coe v0) (coe v0) (coe v4)
                          (coe
                             MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v4)
                             (coe v3 v4 v5))
                          (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))))
            (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
            (coe
               MAlonzo.Code.Type.Equality.C_trans'8801'β_18
               (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                  (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
                  (coe
                     MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0)
                     (coe MAlonzo.Code.Utils.C_'42'_756)
                     (coe
                        MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v1) (coe v0)
                        (coe
                           (\ v4 v5 ->
                              MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                (coe v0) (coe v4) (coe v3 v4 v5)))
                        (coe MAlonzo.Code.Utils.C_'42'_756)
                        (coe
                           MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v1)
                           (coe MAlonzo.Code.Utils.C_'42'_756)
                           (coe
                              MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v1)
                              (coe MAlonzo.Code.Utils.C_'42'_756) (coe v2))))
                     (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
               (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
               (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76))))
-- Algorithmic.Soundness._≡βL_
d__'8801'βL__128 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] -> ()
d__'8801'βL__128 = erased
-- Algorithmic.Soundness.refl≡βL
d_refl'8801'βL_150 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] -> AgdaAny
d_refl'8801'βL_150 ~v0 v1 = du_refl'8801'βL_150 v1
du_refl'8801'βL_150 ::
  [MAlonzo.Code.Type.T__'8866''8902'__20] -> AgdaAny
du_refl'8801'βL_150 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Type.Equality.C_refl'8801'β_14)
             (coe du_refl'8801'βL_150 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Soundness.embList
d_embList_158 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  [MAlonzo.Code.Type.T__'8866''8902'__20]
d_embList_158 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0)
                (coe MAlonzo.Code.Utils.C_'42'_756) (coe v2))
             (coe d_embList_158 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Soundness.lemsub
d_lemsub_180 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
d_lemsub_180 v0 v1 v2 v3 v4 ~v5 = du_lemsub_180 v0 v1 v2 v3 v4
du_lemsub_180 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_754 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
du_lemsub_180 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Type.Equality.C_trans'8801'β_18
      (MAlonzo.Code.Type.BetaNormal.d_embNf_128
         (coe v0) (coe MAlonzo.Code.Utils.C_'9839'_758)
         (coe
            MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0)
            (coe MAlonzo.Code.Utils.C_'9839'_758)
            (coe
               MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v1) (coe v0)
               (coe
                  (\ v5 v6 ->
                     MAlonzo.Code.Type.BetaNormal.d_embNf_128
                       (coe v0) (coe v5) (coe v4 v5 v6)))
               (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v3))
            (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
      (coe
         MAlonzo.Code.Type.Equality.C_trans'8801'β_18
         (MAlonzo.Code.Type.BetaNormal.d_embNf_128
            (coe v0) (coe MAlonzo.Code.Utils.C_'9839'_758)
            (coe
               MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v1)
               (coe MAlonzo.Code.Utils.C_'9839'_758)
               (coe
                  MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v1)
                  (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v2))
               (coe
                  (\ v5 v6 ->
                     MAlonzo.Code.Type.BetaNBE.d_eval_166
                       (coe v0) (coe v0) (coe v5)
                       (coe
                          MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v5)
                          (coe v4 v5 v6))
                       (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))))
         (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
         (coe
            MAlonzo.Code.Type.Equality.C_trans'8801'β_18
            (MAlonzo.Code.Type.BetaNormal.d_embNf_128
               (coe v0) (coe MAlonzo.Code.Utils.C_'9839'_758)
               (coe
                  MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v1)
                  (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v3)
                  (coe
                     (\ v5 v6 ->
                        MAlonzo.Code.Type.BetaNBE.d_eval_166
                          (coe v0) (coe v0) (coe v5)
                          (coe
                             MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v5)
                             (coe v4 v5 v6))
                          (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))))
            (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
            (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)))
      (coe
         MAlonzo.Code.Type.Equality.C_sym'8801'β_16
         (MAlonzo.Code.Type.BetaNBE.Soundness.d_soundness_470
            (coe v0) (coe MAlonzo.Code.Utils.C_'9839'_758)
            (coe
               MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v1) (coe v0)
               (coe
                  (\ v5 v6 ->
                     MAlonzo.Code.Type.BetaNormal.d_embNf_128
                       (coe v0) (coe v5) (coe v4 v5 v6)))
               (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v3))))
-- Algorithmic.Soundness.subNf-sub∅-lem
d_subNf'45'sub'8709''45'lem_196 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
d_subNf'45'sub'8709''45'lem_196 v0 v1
  = coe
      MAlonzo.Code.Type.Equality.C_trans'8801'β_18
      (MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
         (coe MAlonzo.Code.Type.C_'8709'_4) (coe v0)
         (coe
            (\ v2 v3 ->
               MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v2) erased))
         (coe MAlonzo.Code.Utils.C_'9839'_758)
         (coe
            MAlonzo.Code.Type.BetaNormal.d_embNf_128
            (coe MAlonzo.Code.Type.C_'8709'_4)
            (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v1)))
      (coe
         du_lemsub_180 (coe v0) (coe MAlonzo.Code.Type.C_'8709'_4) (coe v1)
         (coe
            MAlonzo.Code.Type.BetaNormal.d_embNf_128
            (coe MAlonzo.Code.Type.C_'8709'_4)
            (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v1))
         erased)
      (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
-- Algorithmic.Soundness.subNf∅-sub∅-lem
d_subNf'8709''45'sub'8709''45'lem_210 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
d_subNf'8709''45'sub'8709''45'lem_210 v0 v1
  = coe d_subNf'45'sub'8709''45'lem_196 (coe v0) (coe v1)
-- Algorithmic.Soundness.btype-lem≡β
d_btype'45'lem'8801'β_224 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
d_btype'45'lem'8801'β_224 v0 v1
  = coe
      MAlonzo.Code.Type.BetaNBE.Soundness.d_soundness_470 (coe v0)
      (coe MAlonzo.Code.Utils.C_'42'_756)
      (coe MAlonzo.Code.Declarative.d_btype_42 (coe v0) (coe v1))
-- Algorithmic.Soundness.emb
d_emb_240 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d_emb_240 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Algorithmic.C_'96'_184 v5
        -> coe
             MAlonzo.Code.Declarative.C_'96'_114
             (coe du_embVar_22 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Algorithmic.C_ƛ_190 v6
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v8 v9
               -> coe
                    MAlonzo.Code.Declarative.C_ƛ_116
                    (d_emb_240
                       (coe v0) (coe MAlonzo.Code.Algorithmic.C__'44'__12 v1 v8) (coe v9)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183'__196 v4 v6 v7
        -> coe
             MAlonzo.Code.Declarative.C__'183'__118
             (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756) (coe v4))
             (d_emb_240
                (coe v0) (coe v1)
                (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v4 v2) (coe v6))
             (d_emb_240 (coe v0) (coe v1) (coe v4) (coe v7))
      MAlonzo.Code.Algorithmic.C_Λ_202 v6
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C_Π_14 v8 v9
               -> coe
                    MAlonzo.Code.Declarative.C_Λ_120
                    (d_emb_240
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                       (coe MAlonzo.Code.Algorithmic.C__'44''8902'__8 v1) (coe v9)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v4 v6 v7 v8
        -> coe
             MAlonzo.Code.Declarative.C_conv_156
             (MAlonzo.Code.Type.RenamingSubstitution.d__'91'_'93'_432
                (coe v0) (coe v4) (coe MAlonzo.Code.Utils.C_'42'_756)
                (coe
                   MAlonzo.Code.Type.BetaNormal.d_embNf_128
                   (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v4))
                   (coe MAlonzo.Code.Utils.C_'42'_756) (coe v6))
                (coe
                   MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v4)
                   (coe v8)))
             (d_emb'91''93'_38 (coe v0) (coe v4) (coe v8) (coe v6))
             (coe
                MAlonzo.Code.Declarative.C__'183''8902'__124 (coe v4)
                (coe
                   MAlonzo.Code.Type.BetaNormal.d_embNf_128
                   (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v4))
                   (coe MAlonzo.Code.Utils.C_'42'_756) (coe v6))
                (coe
                   d_emb_240 (coe v0) (coe v1)
                   (coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v4 v6) (coe v7))
                (coe
                   MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v4)
                   (coe v8)))
      MAlonzo.Code.Algorithmic.C_wrap_220 v7
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v9 v10 v11
               -> coe
                    MAlonzo.Code.Declarative.C_wrap_130
                    (coe
                       MAlonzo.Code.Declarative.C_conv_156
                       (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                          (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
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
                                            (coe
                                               MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v9))
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
                                            MAlonzo.Code.Type.C_'96'_22
                                            (coe MAlonzo.Code.Type.C_Z_16)))))
                                (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                   (coe v0) (coe v9) (coe v11)))))
                       (coe
                          MAlonzo.Code.Type.Equality.C_sym'8801'β_16
                          (coe du_soundness'45'μ_60 (coe v0) (coe v9) (coe v10) (coe v11)))
                       (d_emb_240
                          (coe v0) (coe v1)
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
                                            (coe
                                               MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v9))
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
                                            MAlonzo.Code.Type.C_'96'_22
                                            (coe MAlonzo.Code.Type.C_Z_16)))))
                                (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                   (coe v0) (coe v9) (coe v11))))
                          (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_unwrap_230 v4 v6 v7 v8
        -> coe
             MAlonzo.Code.Declarative.C_conv_156
             (coe
                MAlonzo.Code.Type.C__'183'__30 v4
                (coe
                   MAlonzo.Code.Type.C__'183'__30
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                      (coe MAlonzo.Code.Utils.C_'42'_756))
                   (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                      (coe v0)
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__760
                         (coe
                            MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                            (coe MAlonzo.Code.Utils.C_'42'_756))
                         (coe
                            MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                            (coe MAlonzo.Code.Utils.C_'42'_756)))
                      (coe v6))
                   (coe
                      MAlonzo.Code.Type.C_ƛ_28
                      (coe
                         MAlonzo.Code.Type.C_μ_32 v4
                         (coe
                            MAlonzo.Code.Type.RenamingSubstitution.d_weaken_98 v0
                            (coe
                               MAlonzo.Code.Utils.C__'8658'__760
                               (coe
                                  MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                                  (coe MAlonzo.Code.Utils.C_'42'_756))
                               (coe
                                  MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                                  (coe MAlonzo.Code.Utils.C_'42'_756)))
                            v4
                            (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                               (coe v0)
                               (coe
                                  MAlonzo.Code.Utils.C__'8658'__760
                                  (coe
                                     MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                                     (coe MAlonzo.Code.Utils.C_'42'_756))
                                  (coe
                                     MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                                     (coe MAlonzo.Code.Utils.C_'42'_756)))
                               (coe v6)))
                         (coe MAlonzo.Code.Type.C_'96'_22 (coe MAlonzo.Code.Type.C_Z_16)))))
                (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                   (coe v0) (coe v4) (coe v7)))
             (coe du_soundness'45'μ_60 (coe v0) (coe v4) (coe v6) (coe v7))
             (coe
                MAlonzo.Code.Declarative.C_unwrap_132
                (d_emb_240
                   (coe v0) (coe v1)
                   (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v4 v6 v7) (coe v8)))
      MAlonzo.Code.Algorithmic.C_constr_240 v5 v7 v9
        -> case coe v2 of
             MAlonzo.Code.Type.BetaNormal.C_SOP_28 v11 v12
               -> coe
                    MAlonzo.Code.Declarative.C_constr_142 v5
                    (MAlonzo.Code.Type.BetaNormal.d_embNf'45'List_140
                       (coe v0) (coe MAlonzo.Code.Utils.C_'42'_756)
                       (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v12) (coe v5)))
                    (d_emb'45'ConstrArgs_250
                       (coe v0) (coe v1)
                       (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v12) (coe v5))
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_case_252 v4 v5 v7 v8
        -> coe
             MAlonzo.Code.Declarative.C_case_154 v4
             (coe
                MAlonzo.Code.Type.BetaNormal.du_embNf'45'VecList_148 (coe v0)
                (coe MAlonzo.Code.Utils.C_'42'_756) (coe v5))
             (d_emb_240
                (coe v0) (coe v1) (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v4 v5)
                (coe v7))
             (coe
                du_emb'45'Cases_282 (coe v0) (coe v1) (coe v2) (coe v5) (coe v8))
      MAlonzo.Code.Algorithmic.C_con_258 v4 v6
        -> coe
             MAlonzo.Code.Declarative.C_con_162
             (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                (coe MAlonzo.Code.Type.C_'8709'_4)
                (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v4))
             v6 (d_subNf'8709''45'sub'8709''45'lem_210 (coe v0) (coe v4))
      MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v5
        -> coe
             MAlonzo.Code.Declarative.C_conv_156
             (MAlonzo.Code.Declarative.d_btype_42 (coe v0) (coe v5))
             (d_btype'45'lem'8801'β_224 (coe v0) (coe v5))
             (coe MAlonzo.Code.Declarative.C_builtin_166 (coe v5))
      MAlonzo.Code.Algorithmic.C_error_268
        -> coe MAlonzo.Code.Declarative.C_error_170
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Soundness.emb-ConstrArgs
d_emb'45'ConstrArgs_250 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302
d_emb'45'ConstrArgs_250 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Utils.List.C_'91''93'_308 -> coe v3
      MAlonzo.Code.Utils.List.C__'8759'__314 v6 v7
        -> case coe v2 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Utils.List.C__'8759'__314
                    (d_emb_240 (coe v0) (coe v1) (coe v8) (coe v6))
                    (d_emb'45'ConstrArgs_250 (coe v0) (coe v1) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Soundness.lema-mkCaseType
d_lema'45'mkCaseType_262 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lema'45'mkCaseType_262 = erased
-- Algorithmic.Soundness.emb-Cases
d_emb'45'Cases_282 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Declarative.T_Cases_104
d_emb'45'Cases_282 v0 v1 v2 ~v3 v4 v5
  = du_emb'45'Cases_282 v0 v1 v2 v4 v5
du_emb'45'Cases_282 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Algorithmic.T_Cases_172 ->
  MAlonzo.Code.Declarative.T_Cases_104
du_emb'45'Cases_282 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Algorithmic.C_'91''93'_278
        -> coe MAlonzo.Code.Declarative.C_'91''93'_180
      MAlonzo.Code.Algorithmic.C__'8759'__290 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
               -> coe
                    MAlonzo.Code.Declarative.C__'8759'__192
                    (d_emb_240
                       (coe v0) (coe v1)
                       (coe MAlonzo.Code.Algorithmic.du_mkCaseType_156 v2 v11) (coe v8))
                    (coe
                       du_emb'45'Cases_282 (coe v0) (coe v1) (coe v2) (coe v12) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Soundness.soundnessT
d_soundnessT_354 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Algorithmic.T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Declarative.T__'8866'__110
d_soundnessT_354 v0 v1 v2
  = coe d_emb_240 (coe v0) (coe v1) (coe v2)
