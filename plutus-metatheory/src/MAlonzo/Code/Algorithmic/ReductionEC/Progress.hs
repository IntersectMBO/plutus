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

module MAlonzo.Code.Algorithmic.ReductionEC.Progress where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Algorithmic.ReductionEC
import qualified MAlonzo.Code.Algorithmic.RenamingSubstitution
import qualified MAlonzo.Code.Algorithmic.Signature
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNBE.RenamingSubstitution
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Algorithmic.ReductionEC.Progress.Progress
d_Progress_10 a0 a1 = ()
data T_Progress_10
  = C_step_18 MAlonzo.Code.Algorithmic.T__'8866'__178
              MAlonzo.Code.Algorithmic.ReductionEC.T__'8212''8594'__750 |
    C_done_20 MAlonzo.Code.Algorithmic.ReductionEC.T_Value_28
-- Algorithmic.ReductionEC.Progress.FocusedProgDissect
d_FocusedProgDissect_28 a0 a1 = ()
data T_FocusedProgDissect_28
  = C_done_48 MAlonzo.Code.Utils.List.T_Bwd_6
              MAlonzo.Code.Utils.List.T_IBwd_396
              MAlonzo.Code.Utils.List.T__'8803'_'60''62''62'__684
              MAlonzo.Code.Utils.List.T__'8803'I_'60''62''62'__1110
              MAlonzo.Code.Utils.List.T_IIBwd_832 |
    C_step_80 MAlonzo.Code.Utils.List.T_Bwd_6
              MAlonzo.Code.Utils.List.T_IBwd_396
              MAlonzo.Code.Utils.List.T_IIBwd_832
              MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
              MAlonzo.Code.Algorithmic.T__'8866'__178
              MAlonzo.Code.Algorithmic.T__'8866'__178
              MAlonzo.Code.Algorithmic.ReductionEC.T__'8212''8594'__750
              [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4]
              MAlonzo.Code.Utils.List.T_IList_302
              MAlonzo.Code.Utils.List.T__'8803'_'60''62''62'__684
              MAlonzo.Code.Utils.List.T__'8803'I_'60''62''62'__1110
-- Algorithmic.ReductionEC.Progress.progress
d_progress_86 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 -> T_Progress_10
d_progress_86 v0 v1
  = case coe v1 of
      MAlonzo.Code.Algorithmic.C_ƛ_190 v4
        -> coe
             C_done_20 (coe MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'ƛ_138)
      MAlonzo.Code.Algorithmic.C__'183'__196 v2 v4 v5
        -> let v6
                 = d_progress_86
                     (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v2 v0) (coe v4) in
           coe
             (case coe v6 of
                C_step_18 v7 v8
                  -> case coe v8 of
                       MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v10 v11 v12 v13 v14
                         -> coe
                              C_step_18
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                 (coe v0)
                                 (coe MAlonzo.Code.Algorithmic.ReductionEC.C__l'183'__490 v2 v13 v5)
                                 (coe v12))
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v10 v11 v12
                                 (coe MAlonzo.Code.Algorithmic.ReductionEC.C__l'183'__490 v2 v13 v5)
                                 v14)
                       MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v9 v11
                         -> coe
                              C_step_18 (coe MAlonzo.Code.Algorithmic.C_error_268)
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v9
                                 (coe
                                    MAlonzo.Code.Algorithmic.ReductionEC.C__l'183'__490 v2 v11 v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_done_20 v7
                  -> let v8 = d_progress_86 (coe v2) (coe v5) in
                     coe
                       (case coe v8 of
                          C_step_18 v9 v10
                            -> case coe v10 of
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v12 v13 v14 v15 v16
                                   -> coe
                                        C_step_18
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                           (coe v0)
                                           (coe
                                              MAlonzo.Code.Algorithmic.ReductionEC.C__'183'r__500 v2
                                              v4 v7 v15)
                                           (coe v14))
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v12 v13
                                           v14
                                           (coe
                                              MAlonzo.Code.Algorithmic.ReductionEC.C__'183'r__500 v2
                                              v4 v7 v15)
                                           v16)
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v11 v13
                                   -> coe
                                        C_step_18 (coe MAlonzo.Code.Algorithmic.C_error_268)
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v11
                                           (coe
                                              MAlonzo.Code.Algorithmic.ReductionEC.C__'183'r__500 v2
                                              v4 v7 v13))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          C_done_20 v9
                            -> case coe v7 of
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'ƛ_138
                                   -> case coe v4 of
                                        MAlonzo.Code.Algorithmic.C_ƛ_190 v15
                                          -> coe
                                               C_step_18
                                               (coe
                                                  MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                                  (coe v0)
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.RenamingSubstitution.d__'91'_'93'_702
                                                     (coe MAlonzo.Code.Type.C_'8709'_4)
                                                     (coe MAlonzo.Code.Algorithmic.C_'8709'_4)
                                                     (coe v0) (coe v2) (coe v15) (coe v5)))
                                               (coe
                                                  MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766
                                                  v0
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.C__'183'__196 v2
                                                     (coe MAlonzo.Code.Algorithmic.C_ƛ_190 v15) v5)
                                                  (MAlonzo.Code.Algorithmic.RenamingSubstitution.d__'91'_'93'_702
                                                     (coe MAlonzo.Code.Type.C_'8709'_4)
                                                     (coe MAlonzo.Code.Algorithmic.C_'8709'_4)
                                                     (coe v0) (coe v2) (coe v15) (coe v5))
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.ReductionEC.C_β'45'ƛ_662
                                                     v9))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'I'8658'_184 v10 v13 v14 v15 v16 v17 v18 v20
                                   -> case coe v16 of
                                        0 -> coe
                                               C_step_18
                                               (coe
                                                  MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                                  (coe v0)
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.ReductionEC.du_BUILTIN''_326
                                                     (coe v10) (coe v0)
                                                     (coe
                                                        MAlonzo.Code.Algorithmic.C__'183'__196 v2 v4
                                                        v5)
                                                     (coe v14)
                                                     (coe MAlonzo.Code.Utils.C_bubble_180 v17)
                                                     (coe
                                                        MAlonzo.Code.Algorithmic.ReductionEC.C_step_100
                                                        v20 v9)))
                                               (coe
                                                  MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766
                                                  v0
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.C__'183'__196 v2 v4
                                                     v5)
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.ReductionEC.du_BUILTIN''_326
                                                     (coe v10) (coe v0)
                                                     (coe
                                                        MAlonzo.Code.Algorithmic.C__'183'__196 v2 v4
                                                        v5)
                                                     (coe v14)
                                                     (coe MAlonzo.Code.Utils.C_bubble_180 v17)
                                                     (coe
                                                        MAlonzo.Code.Algorithmic.ReductionEC.C_step_100
                                                        v20 v9))
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.ReductionEC.C_β'45'builtin_720
                                                     v13 v10 v14 v15 v17 v18 v20 v9))
                                        _ -> let v21 = subInt (coe v16) (coe (1 :: Integer)) in
                                             coe
                                               (coe
                                                  C_done_20
                                                  (coe
                                                     MAlonzo.Code.Algorithmic.ReductionEC.du_V'45'I_818
                                                     (coe v10) (coe v13) (coe (0 :: Integer))
                                                     (coe v14)
                                                     (coe addInt (coe (1 :: Integer)) (coe v15))
                                                     (coe v21)
                                                     (coe MAlonzo.Code.Utils.C_bubble_180 v17)
                                                     (coe v18)
                                                     (coe
                                                        MAlonzo.Code.Algorithmic.ReductionEC.C_step_100
                                                        v20 v9)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Algorithmic.C_Λ_202 v4
        -> coe
             C_done_20 (coe MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'Λ_146)
      MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v2 v4 v5 v6
        -> let v8
                 = d_progress_86
                     (coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v2 v4) (coe v5) in
           coe
             (case coe v8 of
                C_step_18 v9 v10
                  -> case coe v10 of
                       MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v12 v13 v14 v15 v16
                         -> coe
                              C_step_18
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                 (coe
                                    MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d__'91'_'93'Nf_236
                                    (coe MAlonzo.Code.Type.C_'8709'_4)
                                    (coe MAlonzo.Code.Utils.C_'42'_756) (coe v2) (coe v4) (coe v6))
                                 (coe
                                    MAlonzo.Code.Algorithmic.ReductionEC.C__'183''8902'_'47'__512 v2
                                    v4 v15 v6)
                                 (coe v14))
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v12 v13 v14
                                 (coe
                                    MAlonzo.Code.Algorithmic.ReductionEC.C__'183''8902'_'47'__512 v2
                                    v4 v15 v6)
                                 v16)
                       MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v11 v13
                         -> coe
                              C_step_18 (coe MAlonzo.Code.Algorithmic.C_error_268)
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v11
                                 (coe
                                    MAlonzo.Code.Algorithmic.ReductionEC.C__'183''8902'_'47'__512 v2
                                    v4 v13 v6))
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_done_20 v9
                  -> case coe v9 of
                       MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'Λ_146
                         -> case coe v5 of
                              MAlonzo.Code.Algorithmic.C_Λ_202 v15
                                -> coe
                                     C_step_18
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                        (coe
                                           MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d__'91'_'93'Nf_236
                                           (coe MAlonzo.Code.Type.C_'8709'_4)
                                           (coe MAlonzo.Code.Utils.C_'42'_756) (coe v2) (coe v4)
                                           (coe v6))
                                        (coe MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                        (coe
                                           MAlonzo.Code.Algorithmic.RenamingSubstitution.d__'91'_'93''8902'_740
                                           (coe MAlonzo.Code.Type.C_'8709'_4)
                                           (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v2)
                                           (coe v4) (coe v15) (coe v6)))
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766
                                        (MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d__'91'_'93'Nf_236
                                           (coe MAlonzo.Code.Type.C_'8709'_4)
                                           (coe MAlonzo.Code.Utils.C_'42'_756) (coe v2) (coe v4)
                                           (coe v6))
                                        (coe
                                           MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v2 v4
                                           (coe MAlonzo.Code.Algorithmic.C_Λ_202 v15) v6)
                                        (MAlonzo.Code.Algorithmic.RenamingSubstitution.d__'91'_'93''8902'_740
                                           (coe MAlonzo.Code.Type.C_'8709'_4)
                                           (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v2)
                                           (coe v4) (coe v15) (coe v6))
                                        (coe MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                        (coe MAlonzo.Code.Algorithmic.ReductionEC.C_β'45'Λ_678))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'IΠ_208 v10 v13 v14 v15 v16 v17 v18 v19 v21
                         -> coe
                              seq (coe v14)
                              (coe
                                 C_done_20
                                 (coe
                                    MAlonzo.Code.Algorithmic.ReductionEC.du_V'45'I_818 (coe v10)
                                    (coe addInt (coe (1 :: Integer)) (coe v13)) (coe v14)
                                    (coe MAlonzo.Code.Utils.C_bubble_180 v15) (coe v16) (coe v17)
                                    (coe v18)
                                    (coe
                                       MAlonzo.Code.Algorithmic.Signature.du__'91'_'93'SigTy_150
                                       (coe MAlonzo.Code.Type.C_'8709'_4) (coe v2) (coe v19)
                                       (coe v6))
                                    (coe
                                       MAlonzo.Code.Algorithmic.ReductionEC.C_step'8902'_130 v19
                                       v21)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Algorithmic.C_wrap_220 v5
        -> case coe v0 of
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v7 v8 v9
               -> let v10
                        = d_progress_86
                            (coe
                               MAlonzo.Code.Type.BetaNBE.d__'183'V__150
                               (coe MAlonzo.Code.Type.C_'8709'_4) (coe v7)
                               (coe MAlonzo.Code.Utils.C_'42'_756)
                               (coe
                                  MAlonzo.Code.Type.BetaNBE.d__'183'V__150
                                  (coe MAlonzo.Code.Type.C_'8709'_4)
                                  (coe
                                     MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                     (coe MAlonzo.Code.Utils.C_'42'_756))
                                  (coe
                                     MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                     (coe MAlonzo.Code.Utils.C_'42'_756))
                                  (coe
                                     MAlonzo.Code.Type.BetaNBE.d_eval_166
                                     (coe MAlonzo.Code.Type.C_'8709'_4)
                                     (coe MAlonzo.Code.Type.C_'8709'_4)
                                     (coe
                                        MAlonzo.Code.Utils.C__'8658'__760
                                        (coe
                                           MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                           (coe MAlonzo.Code.Utils.C_'42'_756))
                                        (coe
                                           MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                           (coe MAlonzo.Code.Utils.C_'42'_756)))
                                     (coe
                                        MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                        (coe MAlonzo.Code.Type.C_'8709'_4)
                                        (coe
                                           MAlonzo.Code.Utils.C__'8658'__760
                                           (coe
                                              MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                              (coe MAlonzo.Code.Utils.C_'42'_756))
                                           (coe
                                              MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                              (coe MAlonzo.Code.Utils.C_'42'_756)))
                                        (coe v8))
                                     (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
                                  (coe
                                     MAlonzo.Code.Type.BetaNBE.d_eval_166
                                     (coe MAlonzo.Code.Type.C_'8709'_4)
                                     (coe MAlonzo.Code.Type.C_'8709'_4)
                                     (coe
                                        MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                        (coe MAlonzo.Code.Utils.C_'42'_756))
                                     (coe
                                        MAlonzo.Code.Type.C_ƛ_28
                                        (coe
                                           MAlonzo.Code.Type.C_μ_32 v7
                                           (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                              (coe
                                                 MAlonzo.Code.Type.C__'44''8902'__6
                                                 (coe MAlonzo.Code.Type.C_'8709'_4) (coe v7))
                                              (coe
                                                 MAlonzo.Code.Utils.C__'8658'__760
                                                 (coe
                                                    MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                                    (coe MAlonzo.Code.Utils.C_'42'_756))
                                                 (coe
                                                    MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                                    (coe MAlonzo.Code.Utils.C_'42'_756)))
                                              (coe
                                                 MAlonzo.Code.Type.BetaNormal.d_weakenNf_122
                                                 (coe MAlonzo.Code.Type.C_'8709'_4)
                                                 (coe
                                                    MAlonzo.Code.Utils.C__'8658'__760
                                                    (coe
                                                       MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                                       (coe MAlonzo.Code.Utils.C_'42'_756))
                                                    (coe
                                                       MAlonzo.Code.Utils.C__'8658'__760 (coe v7)
                                                       (coe MAlonzo.Code.Utils.C_'42'_756)))
                                                 v7 v8))
                                           (coe
                                              MAlonzo.Code.Type.C_'96'_22
                                              (coe MAlonzo.Code.Type.C_Z_16))))
                                     (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
                               (coe
                                  MAlonzo.Code.Type.BetaNBE.d_eval_166
                                  (coe MAlonzo.Code.Type.C_'8709'_4)
                                  (coe MAlonzo.Code.Type.C_'8709'_4) (coe v7)
                                  (coe
                                     MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                     (coe MAlonzo.Code.Type.C_'8709'_4) (coe v7) (coe v9))
                                  (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
                            (coe v5) in
                  coe
                    (case coe v10 of
                       C_step_18 v11 v12
                         -> case coe v12 of
                              MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v14 v15 v16 v17 v18
                                -> coe
                                     C_step_18
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                        (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v7 v8 v9)
                                        (coe MAlonzo.Code.Algorithmic.ReductionEC.C_wrap_522 v17)
                                        (coe v16))
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v14 v15
                                        v16
                                        (coe MAlonzo.Code.Algorithmic.ReductionEC.C_wrap_522 v17)
                                        v18)
                              MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v13 v15
                                -> coe
                                     C_step_18 (coe MAlonzo.Code.Algorithmic.C_error_268)
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v13
                                        (coe MAlonzo.Code.Algorithmic.ReductionEC.C_wrap_522 v15))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_done_20 v11
                         -> coe
                              C_done_20
                              (coe MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'wrap_156 v11)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_unwrap_230 v2 v4 v5 v6
        -> let v8
                 = d_progress_86
                     (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v2 v4 v5) (coe v6) in
           coe
             (case coe v8 of
                C_step_18 v9 v10
                  -> case coe v10 of
                       MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v12 v13 v14 v15 v16
                         -> coe
                              C_step_18
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                 (coe
                                    MAlonzo.Code.Type.BetaNBE.d_nf_258
                                    (coe MAlonzo.Code.Type.C_'8709'_4)
                                    (coe MAlonzo.Code.Utils.C_'42'_756)
                                    (coe
                                       MAlonzo.Code.Type.C__'183'__30 v2
                                       (coe
                                          MAlonzo.Code.Type.C__'183'__30
                                          (coe
                                             MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                             (coe MAlonzo.Code.Utils.C_'42'_756))
                                          (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                             (coe MAlonzo.Code.Type.C_'8709'_4)
                                             (coe
                                                MAlonzo.Code.Utils.C__'8658'__760
                                                (coe
                                                   MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                                   (coe MAlonzo.Code.Utils.C_'42'_756))
                                                (coe
                                                   MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                                   (coe MAlonzo.Code.Utils.C_'42'_756)))
                                             (coe v4))
                                          (coe
                                             MAlonzo.Code.Type.C_ƛ_28
                                             (coe
                                                MAlonzo.Code.Type.C_μ_32 v2
                                                (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                                   (coe
                                                      MAlonzo.Code.Type.C__'44''8902'__6
                                                      (coe MAlonzo.Code.Type.C_'8709'_4) (coe v2))
                                                   (coe
                                                      MAlonzo.Code.Utils.C__'8658'__760
                                                      (coe
                                                         MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                                         (coe MAlonzo.Code.Utils.C_'42'_756))
                                                      (coe
                                                         MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                                         (coe MAlonzo.Code.Utils.C_'42'_756)))
                                                   (coe
                                                      MAlonzo.Code.Type.BetaNormal.d_weakenNf_122
                                                      (coe MAlonzo.Code.Type.C_'8709'_4)
                                                      (coe
                                                         MAlonzo.Code.Utils.C__'8658'__760
                                                         (coe
                                                            MAlonzo.Code.Utils.C__'8658'__760
                                                            (coe v2)
                                                            (coe MAlonzo.Code.Utils.C_'42'_756))
                                                         (coe
                                                            MAlonzo.Code.Utils.C__'8658'__760
                                                            (coe v2)
                                                            (coe MAlonzo.Code.Utils.C_'42'_756)))
                                                      v2 v4))
                                                (coe
                                                   MAlonzo.Code.Type.C_'96'_22
                                                   (coe MAlonzo.Code.Type.C_Z_16)))))
                                       (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                          (coe MAlonzo.Code.Type.C_'8709'_4) (coe v2) (coe v5))))
                                 (coe
                                    MAlonzo.Code.Algorithmic.ReductionEC.C_unwrap_'47'__534 v2 v4 v5
                                    v15)
                                 (coe v14))
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v12 v13 v14
                                 (coe
                                    MAlonzo.Code.Algorithmic.ReductionEC.C_unwrap_'47'__534 v2 v4 v5
                                    v15)
                                 v16)
                       MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v11 v13
                         -> coe
                              C_step_18 (coe MAlonzo.Code.Algorithmic.C_error_268)
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v11
                                 (coe
                                    MAlonzo.Code.Algorithmic.ReductionEC.C_unwrap_'47'__534 v2 v4 v5
                                    v13))
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_done_20 v9
                  -> case coe v9 of
                       MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'wrap_156 v14
                         -> case coe v6 of
                              MAlonzo.Code.Algorithmic.C_wrap_220 v18
                                -> coe
                                     C_step_18
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                        (coe
                                           MAlonzo.Code.Type.BetaNBE.d_nf_258
                                           (coe MAlonzo.Code.Type.C_'8709'_4)
                                           (coe MAlonzo.Code.Utils.C_'42'_756)
                                           (coe
                                              MAlonzo.Code.Type.C__'183'__30 v2
                                              (coe
                                                 MAlonzo.Code.Type.C__'183'__30
                                                 (coe
                                                    MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                                    (coe MAlonzo.Code.Utils.C_'42'_756))
                                                 (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                                    (coe MAlonzo.Code.Type.C_'8709'_4)
                                                    (coe
                                                       MAlonzo.Code.Utils.C__'8658'__760
                                                       (coe
                                                          MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                                          (coe MAlonzo.Code.Utils.C_'42'_756))
                                                       (coe
                                                          MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                                          (coe MAlonzo.Code.Utils.C_'42'_756)))
                                                    (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Type.C_ƛ_28
                                                    (coe
                                                       MAlonzo.Code.Type.C_μ_32 v2
                                                       (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                                          (coe
                                                             MAlonzo.Code.Type.C__'44''8902'__6
                                                             (coe MAlonzo.Code.Type.C_'8709'_4)
                                                             (coe v2))
                                                          (coe
                                                             MAlonzo.Code.Utils.C__'8658'__760
                                                             (coe
                                                                MAlonzo.Code.Utils.C__'8658'__760
                                                                (coe v2)
                                                                (coe MAlonzo.Code.Utils.C_'42'_756))
                                                             (coe
                                                                MAlonzo.Code.Utils.C__'8658'__760
                                                                (coe v2)
                                                                (coe
                                                                   MAlonzo.Code.Utils.C_'42'_756)))
                                                          (coe
                                                             MAlonzo.Code.Type.BetaNormal.d_weakenNf_122
                                                             (coe MAlonzo.Code.Type.C_'8709'_4)
                                                             (coe
                                                                MAlonzo.Code.Utils.C__'8658'__760
                                                                (coe
                                                                   MAlonzo.Code.Utils.C__'8658'__760
                                                                   (coe v2)
                                                                   (coe
                                                                      MAlonzo.Code.Utils.C_'42'_756))
                                                                (coe
                                                                   MAlonzo.Code.Utils.C__'8658'__760
                                                                   (coe v2)
                                                                   (coe
                                                                      MAlonzo.Code.Utils.C_'42'_756)))
                                                             v2 v4))
                                                       (coe
                                                          MAlonzo.Code.Type.C_'96'_22
                                                          (coe MAlonzo.Code.Type.C_Z_16)))))
                                              (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                                 (coe MAlonzo.Code.Type.C_'8709'_4) (coe v2)
                                                 (coe v5))))
                                        (coe MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                        (coe v18))
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766
                                        (MAlonzo.Code.Type.BetaNBE.d_nf_258
                                           (coe MAlonzo.Code.Type.C_'8709'_4)
                                           (coe MAlonzo.Code.Utils.C_'42'_756)
                                           (coe
                                              MAlonzo.Code.Type.C__'183'__30 v2
                                              (coe
                                                 MAlonzo.Code.Type.C__'183'__30
                                                 (coe
                                                    MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                                    (coe MAlonzo.Code.Utils.C_'42'_756))
                                                 (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                                    (coe MAlonzo.Code.Type.C_'8709'_4)
                                                    (coe
                                                       MAlonzo.Code.Utils.C__'8658'__760
                                                       (coe
                                                          MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                                          (coe MAlonzo.Code.Utils.C_'42'_756))
                                                       (coe
                                                          MAlonzo.Code.Utils.C__'8658'__760 (coe v2)
                                                          (coe MAlonzo.Code.Utils.C_'42'_756)))
                                                    (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Type.C_ƛ_28
                                                    (coe
                                                       MAlonzo.Code.Type.C_μ_32 v2
                                                       (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                                          (coe
                                                             MAlonzo.Code.Type.C__'44''8902'__6
                                                             (coe MAlonzo.Code.Type.C_'8709'_4)
                                                             (coe v2))
                                                          (coe
                                                             MAlonzo.Code.Utils.C__'8658'__760
                                                             (coe
                                                                MAlonzo.Code.Utils.C__'8658'__760
                                                                (coe v2)
                                                                (coe MAlonzo.Code.Utils.C_'42'_756))
                                                             (coe
                                                                MAlonzo.Code.Utils.C__'8658'__760
                                                                (coe v2)
                                                                (coe
                                                                   MAlonzo.Code.Utils.C_'42'_756)))
                                                          (coe
                                                             MAlonzo.Code.Type.BetaNormal.d_weakenNf_122
                                                             (coe MAlonzo.Code.Type.C_'8709'_4)
                                                             (coe
                                                                MAlonzo.Code.Utils.C__'8658'__760
                                                                (coe
                                                                   MAlonzo.Code.Utils.C__'8658'__760
                                                                   (coe v2)
                                                                   (coe
                                                                      MAlonzo.Code.Utils.C_'42'_756))
                                                                (coe
                                                                   MAlonzo.Code.Utils.C__'8658'__760
                                                                   (coe v2)
                                                                   (coe
                                                                      MAlonzo.Code.Utils.C_'42'_756)))
                                                             v2 v4))
                                                       (coe
                                                          MAlonzo.Code.Type.C_'96'_22
                                                          (coe MAlonzo.Code.Type.C_Z_16)))))
                                              (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                                 (coe MAlonzo.Code.Type.C_'8709'_4) (coe v2)
                                                 (coe v5))))
                                        (coe
                                           MAlonzo.Code.Algorithmic.C_unwrap_230 v2 v4 v5
                                           (coe MAlonzo.Code.Algorithmic.C_wrap_220 v18))
                                        v18
                                        (coe MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.C_β'45'wrap_694
                                           v14))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Algorithmic.C_constr_240 v3 v5 v7
        -> case coe v0 of
             MAlonzo.Code.Type.BetaNormal.C_SOP_28 v9 v10
               -> let v11
                        = coe
                            du_progress'45'focus_110
                            (coe MAlonzo.Code.Utils.List.C_'91''93'_10)
                            (coe MAlonzo.Code.Utils.List.C_'91''93'_402)
                            (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v10) (coe v3))
                            (coe MAlonzo.Code.Utils.List.C_start_690) (coe v7)
                            (coe MAlonzo.Code.Utils.List.C_start_1120)
                            (coe MAlonzo.Code.Utils.List.C_'91''93'_840) in
                  coe
                    (case coe v11 of
                       C_done_48 v12 v13 v16 v17 v18
                         -> coe
                              C_done_20
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'constr_234
                                 (coe
                                    MAlonzo.Code.Utils.List.du__'60''62''60'__54 (coe v12)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                 v13 v18)
                       C_step_80 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24
                         -> case coe v20 of
                              MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v26 v27 v28 v29 v30
                                -> coe
                                     C_step_18
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                        (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v9 v10)
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.C_constr_558 v14 v17
                                           v21 v3
                                           (coe
                                              MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v10)
                                              (coe v3))
                                           v23 v15 v16 v22 v29)
                                        (coe v28))
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v26 v27
                                        v28
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.C_constr_558 v14 v17
                                           v21 v3
                                           (coe
                                              MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v10)
                                              (coe v3))
                                           v23 v15 v16 v22 v29)
                                        v30)
                              MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v25 v27
                                -> coe
                                     C_step_18 (coe MAlonzo.Code.Algorithmic.C_error_268)
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v25
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.C_constr_558 v14 v17
                                           v21 v3
                                           (coe
                                              MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v10)
                                              (coe v3))
                                           v23 v15 v16 v22 v27))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Algorithmic.C_case_252 v2 v3 v5 v6
        -> let v7
                 = d_progress_86
                     (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v2 v3) (coe v5) in
           coe
             (case coe v7 of
                C_step_18 v8 v9
                  -> case coe v9 of
                       MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v11 v12 v13 v14 v15
                         -> coe
                              C_step_18
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                 (coe v0)
                                 (coe MAlonzo.Code.Algorithmic.ReductionEC.C_case_568 v2 v3 v6 v14)
                                 (coe v13))
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v11 v12 v13
                                 (coe MAlonzo.Code.Algorithmic.ReductionEC.C_case_568 v2 v3 v6 v14)
                                 v15)
                       MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v10 v12
                         -> coe
                              C_step_18 (coe MAlonzo.Code.Algorithmic.C_error_268)
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v10
                                 (coe MAlonzo.Code.Algorithmic.ReductionEC.C_case_568 v2 v3 v6 v12))
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_done_20 v8
                  -> case coe v8 of
                       MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'constr_234 v14 v16 v17
                         -> case coe v5 of
                              MAlonzo.Code.Algorithmic.C_constr_240 v21 v23 v25
                                -> coe
                                     C_step_18
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                        (coe v0)
                                        (coe MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.du_applyCase_640
                                           (coe
                                              MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v3)
                                              (coe v21))
                                           (coe
                                              MAlonzo.Code.Algorithmic.du_lookupCase_328 (coe v3)
                                              (coe v21) (coe v6))
                                           (coe
                                              MAlonzo.Code.Utils.List.du_IBwd2IList_538
                                              (coe
                                                 MAlonzo.Code.Utils.List.du__'60''62''60'__54
                                                 (coe MAlonzo.Code.Utils.List.C_'91''93'_10)
                                                 (coe
                                                    MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v3)
                                                    (coe v21)))
                                              (coe v16))))
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.C_ruleEC_766 v0
                                        (coe
                                           MAlonzo.Code.Algorithmic.C_case_252 v2 v3
                                           (coe
                                              MAlonzo.Code.Algorithmic.C_constr_240 v21
                                              (coe
                                                 MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v3)
                                                 (coe v21))
                                              (coe
                                                 MAlonzo.Code.Utils.List.du_IBwd2IList_538
                                                 (coe
                                                    MAlonzo.Code.Utils.List.du__'60''62''60'__54
                                                    (coe MAlonzo.Code.Utils.List.C_'91''93'_10)
                                                    (coe
                                                       MAlonzo.Code.Data.Vec.Base.du_lookup_82
                                                       (coe v3) (coe v21)))
                                                 (coe v16)))
                                           v6)
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.du_applyCase_640
                                           (coe
                                              MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v3)
                                              (coe v21))
                                           (coe
                                              MAlonzo.Code.Algorithmic.du_lookupCase_328 (coe v3)
                                              (coe v21) (coe v6))
                                           (coe
                                              MAlonzo.Code.Utils.List.du_IBwd2IList_538
                                              (coe
                                                 MAlonzo.Code.Utils.List.du__'60''62''60'__54
                                                 (coe MAlonzo.Code.Utils.List.C_'91''93'_10)
                                                 (coe
                                                    MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v3)
                                                    (coe v21)))
                                              (coe v16)))
                                        (coe MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.C_β'45'case_746
                                           (coe
                                              MAlonzo.Code.Utils.List.du__'60''62''60'__54
                                              (coe MAlonzo.Code.Utils.List.C_'91''93'_10)
                                              (coe
                                                 MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v3)
                                                 (coe v21)))
                                           v16 v17))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Algorithmic.C_con_258 v2 v4
        -> coe
             C_done_20 (coe MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'con_162)
      MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v3
        -> coe
             C_done_20
             (coe MAlonzo.Code.Algorithmic.ReductionEC.d_ival_838 (coe v3))
      MAlonzo.Code.Algorithmic.C_error_268
        -> coe
             C_step_18 (coe MAlonzo.Code.Algorithmic.C_error_268)
             (coe
                MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v0
                (coe MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.ReductionEC.Progress.progress-focus
d_progress'45'focus_110 ::
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_Bwd_6 ->
  MAlonzo.Code.Utils.List.T_IBwd_396 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T__'8803'_'60''62''62'__684 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T__'8803'I_'60''62''62'__1110 ->
  MAlonzo.Code.Utils.List.T_IIBwd_832 -> T_FocusedProgDissect_28
d_progress'45'focus_110 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_progress'45'focus_110 v2 v3 v4 v5 v6 v7 v8
du_progress'45'focus_110 ::
  MAlonzo.Code.Utils.List.T_Bwd_6 ->
  MAlonzo.Code.Utils.List.T_IBwd_396 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Utils.List.T__'8803'_'60''62''62'__684 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T__'8803'I_'60''62''62'__1110 ->
  MAlonzo.Code.Utils.List.T_IIBwd_832 -> T_FocusedProgDissect_28
du_progress'45'focus_110 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Utils.List.C_'91''93'_308
        -> coe C_done_48 v0 v1 v3 v5 v6
      MAlonzo.Code.Utils.List.C__'8759'__314 v9 v10
        -> case coe v2 of
             (:) v11 v12
               -> let v13 = d_progress_86 (coe v11) (coe v9) in
                  coe
                    (case coe v13 of
                       C_step_18 v14 v15
                         -> coe C_step_80 v0 v1 v6 v11 v9 v14 v15 v12 v10 v3 v5
                       C_done_20 v14
                         -> coe
                              du_progress'45'focus_110
                              (coe MAlonzo.Code.Utils.List.C__'58''60'__12 (coe v0) (coe v11))
                              (coe MAlonzo.Code.Utils.List.C__'58''60'__408 v1 v9) (coe v12)
                              (coe MAlonzo.Code.Utils.List.C_bubble_700 v3) (coe v10)
                              (coe MAlonzo.Code.Utils.List.C_bubble_1136 v5)
                              (coe MAlonzo.Code.Utils.List.C__'58''60'__850 v6 v14)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
