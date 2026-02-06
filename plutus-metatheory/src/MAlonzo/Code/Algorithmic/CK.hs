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

module MAlonzo.Code.Algorithmic.CK where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
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

-- Algorithmic.CK.Stack
d_Stack_18 a0 a1 = ()
data T_Stack_18
  = C_ε_22 |
    C__'44'__30 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                T_Stack_18 MAlonzo.Code.Algorithmic.ReductionEC.T_Frame_352
-- Algorithmic.CK.State
d_State_34 a0 = ()
data T_State_34
  = C__'9659'__40 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                  T_Stack_18 MAlonzo.Code.Algorithmic.T__'8866'__178 |
    C__'9669'__46 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                  T_Stack_18 MAlonzo.Code.Algorithmic.T__'8866'__178
                  MAlonzo.Code.Algorithmic.ReductionEC.T_Value_28 |
    C_'9633'_50 MAlonzo.Code.Algorithmic.T__'8866'__178
                MAlonzo.Code.Algorithmic.ReductionEC.T_Value_28 |
    C_'9670'_54 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
-- Algorithmic.CK.closeStack
d_closeStack_60 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_Stack_18 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_closeStack_60 ~v0 v1 v2 v3 = du_closeStack_60 v1 v2 v3
du_closeStack_60 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_Stack_18 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du_closeStack_60 v0 v1 v2
  = case coe v1 of
      C_ε_22 -> coe v2
      C__'44'__30 v4 v6 v7
        -> coe
             du_closeStack_60 (coe v4) (coe v6)
             (coe
                MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7584'_434
                (coe v0) (coe v7) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.CK.closeState
d_closeState_72 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_State_34 -> MAlonzo.Code.Algorithmic.T__'8866'__178
d_closeState_72 ~v0 v1 = du_closeState_72 v1
du_closeState_72 ::
  T_State_34 -> MAlonzo.Code.Algorithmic.T__'8866'__178
du_closeState_72 v0
  = case coe v0 of
      C__'9659'__40 v1 v2 v3
        -> coe du_closeStack_60 (coe v1) (coe v2) (coe v3)
      C__'9669'__46 v1 v2 v3 v4
        -> coe du_closeStack_60 (coe v1) (coe v2) (coe v3)
      C_'9633'_50 v1 v2 -> coe v1
      C_'9670'_54 v1 -> coe MAlonzo.Code.Algorithmic.C_error_268
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.CK.discharge
d_discharge_94 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.ReductionEC.T_Value_28 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_discharge_94 ~v0 v1 ~v2 = du_discharge_94 v1
du_discharge_94 ::
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du_discharge_94 v0 = coe v0
-- Algorithmic.CK.pushValueFrames
d_pushValueFrames_110 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Utils.List.T_Bwd_6 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_Stack_18 ->
  MAlonzo.Code.Utils.List.T_IBwd_396 ->
  MAlonzo.Code.Utils.List.T_IIBwd_832 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Stack_18
d_pushValueFrames_110 ~v0 v1 v2 ~v3 v4 v5 v6 ~v7
  = du_pushValueFrames_110 v1 v2 v4 v5 v6
du_pushValueFrames_110 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Utils.List.T_Bwd_6 ->
  T_Stack_18 ->
  MAlonzo.Code.Utils.List.T_IBwd_396 ->
  MAlonzo.Code.Utils.List.T_IIBwd_832 -> T_Stack_18
du_pushValueFrames_110 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Utils.List.C_'91''93'_840 -> coe v2
      MAlonzo.Code.Utils.List.C__'58''60'__850 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Utils.List.C__'58''60'__12 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Utils.List.C__'58''60'__408 v15 v16
                      -> coe
                           du_pushValueFrames_110
                           (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v12 v0) (coe v11)
                           (coe
                              C__'44'__30 v0 v2
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.C_'45''183'v_366 v16 v10))
                           (coe v15) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.CK.step
d_step_122 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_State_34 -> T_State_34
d_step_122 ~v0 v1 = du_step_122 v1
du_step_122 :: T_State_34 -> T_State_34
du_step_122 v0
  = case coe v0 of
      C__'9659'__40 v1 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Algorithmic.C_ƛ_190 v6
               -> case coe v1 of
                    MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v8 v9
                      -> coe
                           C__'9669'__46
                           (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v8 v9) (coe v2)
                           (coe MAlonzo.Code.Algorithmic.C_ƛ_190 v6)
                           (coe MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'ƛ_138)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Algorithmic.C__'183'__196 v4 v6 v7
               -> coe
                    C__'9659'__40
                    (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v4 v1)
                    (coe
                       C__'44'__30 v1 v2
                       (coe MAlonzo.Code.Algorithmic.ReductionEC.C_'45''183'__358 v7))
                    (coe v6)
             MAlonzo.Code.Algorithmic.C_Λ_202 v6
               -> case coe v1 of
                    MAlonzo.Code.Type.BetaNormal.C_Π_14 v8 v9
                      -> coe
                           C__'9669'__46 (coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v8 v9)
                           (coe v2) (coe MAlonzo.Code.Algorithmic.C_Λ_202 v6)
                           (coe MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'Λ_146)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v4 v6 v7 v8
               -> coe
                    C__'9659'__40 (coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v4 v6)
                    (coe
                       C__'44'__30
                       (MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d__'91'_'93'Nf_236
                          (coe MAlonzo.Code.Type.C_'8709'_4)
                          (coe MAlonzo.Code.Utils.C_'42'_756) (coe v4) (coe v6) (coe v8))
                       v2
                       (coe
                          MAlonzo.Code.Algorithmic.ReductionEC.C_'45''183''8902'_382 v8))
                    (coe v7)
             MAlonzo.Code.Algorithmic.C_wrap_220 v7
               -> case coe v1 of
                    MAlonzo.Code.Type.BetaNormal.C_μ_24 v9 v10 v11
                      -> coe
                           C__'9659'__40
                           (coe
                              MAlonzo.Code.Type.BetaNBE.d_nf_258
                              (coe MAlonzo.Code.Type.C_'8709'_4)
                              (coe MAlonzo.Code.Utils.C_'42'_756)
                              (coe
                                 MAlonzo.Code.Type.C__'183'__30 v9
                                 (coe
                                    MAlonzo.Code.Type.C__'183'__30
                                    (coe
                                       MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                       (coe MAlonzo.Code.Utils.C_'42'_756))
                                    (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                       (coe MAlonzo.Code.Type.C_'8709'_4)
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
                                                MAlonzo.Code.Type.C__'44''8902'__6
                                                (coe MAlonzo.Code.Type.C_'8709'_4) (coe v9))
                                             (coe
                                                MAlonzo.Code.Utils.C__'8658'__760
                                                (coe
                                                   MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                                   (coe MAlonzo.Code.Utils.C_'42'_756))
                                                (coe
                                                   MAlonzo.Code.Utils.C__'8658'__760 (coe v9)
                                                   (coe MAlonzo.Code.Utils.C_'42'_756)))
                                             (coe
                                                MAlonzo.Code.Type.BetaNormal.d_weakenNf_122
                                                (coe MAlonzo.Code.Type.C_'8709'_4)
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
                                    (coe MAlonzo.Code.Type.C_'8709'_4) (coe v9) (coe v11))))
                           (coe
                              C__'44'__30 (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v9 v10 v11) v2
                              (coe MAlonzo.Code.Algorithmic.ReductionEC.C_wrap'45'_390))
                           (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Algorithmic.C_unwrap_230 v4 v6 v7 v8
               -> coe
                    C__'9659'__40 (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v4 v6 v7)
                    (coe
                       C__'44'__30
                       (MAlonzo.Code.Type.BetaNBE.d_nf_258
                          (coe MAlonzo.Code.Type.C_'8709'_4)
                          (coe MAlonzo.Code.Utils.C_'42'_756)
                          (coe
                             MAlonzo.Code.Type.C__'183'__30 v4
                             (coe
                                MAlonzo.Code.Type.C__'183'__30
                                (coe
                                   MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                                   (coe MAlonzo.Code.Utils.C_'42'_756))
                                (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                   (coe MAlonzo.Code.Type.C_'8709'_4)
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
                                      (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                         (coe
                                            MAlonzo.Code.Type.C__'44''8902'__6
                                            (coe MAlonzo.Code.Type.C_'8709'_4) (coe v4))
                                         (coe
                                            MAlonzo.Code.Utils.C__'8658'__760
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                                               (coe MAlonzo.Code.Utils.C_'42'_756))
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                                               (coe MAlonzo.Code.Utils.C_'42'_756)))
                                         (coe
                                            MAlonzo.Code.Type.BetaNormal.d_weakenNf_122
                                            (coe MAlonzo.Code.Type.C_'8709'_4)
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__760
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                                                  (coe MAlonzo.Code.Utils.C_'42'_756))
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__760 (coe v4)
                                                  (coe MAlonzo.Code.Utils.C_'42'_756)))
                                            v4 v6))
                                      (coe
                                         MAlonzo.Code.Type.C_'96'_22
                                         (coe MAlonzo.Code.Type.C_Z_16)))))
                             (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                (coe MAlonzo.Code.Type.C_'8709'_4) (coe v4) (coe v7))))
                       v2 (coe MAlonzo.Code.Algorithmic.ReductionEC.C_unwrap'45'_398))
                    (coe v8)
             MAlonzo.Code.Algorithmic.C_constr_240 v5 v7 v9
               -> case coe v1 of
                    MAlonzo.Code.Type.BetaNormal.C_SOP_28 v11 v12
                      -> let v13
                               = coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v12) (coe v5) in
                         coe
                           (case coe v13 of
                              []
                                -> coe
                                     seq (coe v9)
                                     (coe
                                        C__'9669'__46
                                        (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v11 v12) (coe v2)
                                        (coe
                                           MAlonzo.Code.Algorithmic.C_constr_240 v5 v13
                                           (coe
                                              MAlonzo.Code.Utils.List.du_IBwd2IList_538
                                              (coe
                                                 MAlonzo.Code.Utils.List.du__'60''62''60'__54
                                                 (coe MAlonzo.Code.Utils.List.C_'91''93'_10)
                                                 (coe v13))
                                              (coe MAlonzo.Code.Utils.List.C_'91''93'_402)))
                                        (coe
                                           MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'constr_234
                                           (coe
                                              MAlonzo.Code.Utils.List.du__'60''62''60'__54
                                              (coe MAlonzo.Code.Utils.List.C_'91''93'_10) (coe v13))
                                           (coe MAlonzo.Code.Utils.List.C_'91''93'_402)
                                           (coe MAlonzo.Code.Utils.List.C_'91''93'_840)))
                              (:) v14 v15
                                -> case coe v9 of
                                     MAlonzo.Code.Utils.List.C__'8759'__314 v18 v19
                                       -> coe
                                            C__'9659'__40 (coe v14)
                                            (coe
                                               C__'44'__30
                                               (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v11 v12)
                                               v2
                                               (coe
                                                  MAlonzo.Code.Algorithmic.ReductionEC.C_constr'45'_420
                                                  (coe MAlonzo.Code.Utils.List.C_'91''93'_10) v15 v5
                                                  v13 (coe MAlonzo.Code.Utils.List.C_start_690)
                                                  (coe MAlonzo.Code.Utils.List.C_'91''93'_402)
                                                  (coe MAlonzo.Code.Utils.List.C_'91''93'_840) v19))
                                            (coe v18)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Algorithmic.C_case_252 v4 v5 v7 v8
               -> coe
                    C__'9659'__40 (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v4 v5)
                    (coe
                       C__'44'__30 v1 v2
                       (coe MAlonzo.Code.Algorithmic.ReductionEC.C_case'45'_428 v8))
                    (coe v7)
             MAlonzo.Code.Algorithmic.C_con_258 v4 v6
               -> coe
                    C__'9669'__46
                    (coe
                       MAlonzo.Code.Type.BetaNormal.C_con_22
                       (MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d_subNf'8709'_566
                          (coe MAlonzo.Code.Type.C_'8709'_4)
                          (coe MAlonzo.Code.Utils.C_'9839'_758) (coe v4)))
                    (coe v2) (coe MAlonzo.Code.Algorithmic.C_con_258 v4 v6)
                    (coe MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'con_162)
             MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v5
               -> coe
                    C__'9669'__46
                    (coe
                       MAlonzo.Code.Algorithmic.Signature.d_btype_30
                       (coe MAlonzo.Code.Type.C_'8709'_4) (coe v5))
                    (coe v2) (coe MAlonzo.Code.Algorithmic.C_builtin_'47'__264 v5)
                    (coe MAlonzo.Code.Algorithmic.ReductionEC.d_ival_838 (coe v5))
             MAlonzo.Code.Algorithmic.C_error_268 -> coe C_'9670'_54 (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'9669'__46 v1 v2 v3 v4
        -> case coe v2 of
             C_ε_22 -> coe C_'9633'_50 (coe v3) (coe v4)
             C__'44'__30 v6 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Algorithmic.ReductionEC.C_'45''183'__358 v12
                      -> case coe v1 of
                           MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v14 v15
                             -> coe
                                  C__'9659'__40 (coe v14)
                                  (coe
                                     C__'44'__30 v6 v8
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.C__'183''45'_374 v3
                                        v4))
                                  (coe v12)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Algorithmic.ReductionEC.C_'45''183'v_366 v12 v13
                      -> case coe v1 of
                           MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v15 v16
                             -> coe
                                  C__'9669'__46 (coe v15)
                                  (coe
                                     C__'44'__30 v6 v8
                                     (coe
                                        MAlonzo.Code.Algorithmic.ReductionEC.C__'183''45'_374 v3
                                        v4))
                                  (coe v12) (coe v13)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Algorithmic.ReductionEC.C__'183''45'_374 v12 v13
                      -> case coe v13 of
                           MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'ƛ_138
                             -> case coe v12 of
                                  MAlonzo.Code.Algorithmic.C_ƛ_190 v19
                                    -> coe
                                         C__'9659'__40 (coe v6) (coe v8)
                                         (coe
                                            MAlonzo.Code.Algorithmic.RenamingSubstitution.d__'91'_'93'_702
                                            (coe MAlonzo.Code.Type.C_'8709'_4)
                                            (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v6)
                                            (coe v1) (coe v19) (coe v3))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'I'8658'_184 v14 v17 v18 v19 v20 v21 v22 v24
                             -> case coe v20 of
                                  0 -> coe
                                         C__'9659'__40 (coe v6) (coe v8)
                                         (coe
                                            MAlonzo.Code.Algorithmic.ReductionEC.du_BUILTIN''_326
                                            (coe v14) (coe v6)
                                            (coe MAlonzo.Code.Algorithmic.C__'183'__196 v1 v12 v3)
                                            (coe v18) (coe MAlonzo.Code.Utils.C_bubble_180 v21)
                                            (coe
                                               MAlonzo.Code.Algorithmic.ReductionEC.C_step_100 v24
                                               v4))
                                  _ -> let v25 = subInt (coe v20) (coe (1 :: Integer)) in
                                       coe
                                         (coe
                                            C__'9669'__46 (coe v6) (coe v8)
                                            (coe MAlonzo.Code.Algorithmic.C__'183'__196 v1 v12 v3)
                                            (coe
                                               MAlonzo.Code.Algorithmic.ReductionEC.du_V'45'I_818
                                               (coe v14) (coe v17) (coe (0 :: Integer)) (coe v18)
                                               (coe addInt (coe (1 :: Integer)) (coe v19)) (coe v25)
                                               (coe MAlonzo.Code.Utils.C_bubble_180 v21) (coe v22)
                                               (coe
                                                  MAlonzo.Code.Algorithmic.ReductionEC.C_step_100
                                                  v24 v4)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Algorithmic.ReductionEC.C_'45''183''8902'_382 v12
                      -> case coe v1 of
                           MAlonzo.Code.Type.BetaNormal.C_Π_14 v14 v15
                             -> case coe v4 of
                                  MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'Λ_146
                                    -> case coe v3 of
                                         MAlonzo.Code.Algorithmic.C_Λ_202 v21
                                           -> coe
                                                C__'9659'__40
                                                (coe
                                                   MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d__'91'_'93'Nf_236
                                                   (coe MAlonzo.Code.Type.C_'8709'_4)
                                                   (coe MAlonzo.Code.Utils.C_'42'_756) (coe v14)
                                                   (coe v15) (coe v12))
                                                (coe v8)
                                                (coe
                                                   MAlonzo.Code.Algorithmic.RenamingSubstitution.d__'91'_'93''8902'_740
                                                   (coe MAlonzo.Code.Type.C_'8709'_4)
                                                   (coe MAlonzo.Code.Algorithmic.C_'8709'_4)
                                                   (coe v14) (coe v15) (coe v21) (coe v12))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'IΠ_208 v16 v19 v20 v21 v22 v23 v24 v25 v27
                                    -> coe
                                         C__'9669'__46
                                         (coe
                                            MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d__'91'_'93'Nf_236
                                            (coe MAlonzo.Code.Type.C_'8709'_4)
                                            (coe MAlonzo.Code.Utils.C_'42'_756) (coe v14) (coe v15)
                                            (coe v12))
                                         (coe v8)
                                         (coe
                                            MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v14
                                            v15 v3 v12)
                                         (coe
                                            MAlonzo.Code.Algorithmic.ReductionEC.du_V'45'I_818
                                            (coe v16) (coe addInt (coe (1 :: Integer)) (coe v19))
                                            (coe v20) (coe MAlonzo.Code.Utils.C_bubble_180 v21)
                                            (coe v22) (coe v23) (coe v24)
                                            (coe
                                               MAlonzo.Code.Algorithmic.Signature.du__'91'_'93'SigTy_150
                                               (coe MAlonzo.Code.Type.C_'8709'_4) (coe v14)
                                               (coe v25) (coe v12))
                                            (coe
                                               MAlonzo.Code.Algorithmic.ReductionEC.C_step'8902'_130
                                               v25 v27))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Algorithmic.ReductionEC.C_wrap'45'_390
                      -> case coe v6 of
                           MAlonzo.Code.Type.BetaNormal.C_μ_24 v14 v15 v16
                             -> coe
                                  C__'9669'__46
                                  (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v14 v15 v16) (coe v8)
                                  (coe MAlonzo.Code.Algorithmic.C_wrap_220 v3)
                                  (coe MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'wrap_156 v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Algorithmic.ReductionEC.C_unwrap'45'_398
                      -> case coe v1 of
                           MAlonzo.Code.Type.BetaNormal.C_μ_24 v14 v15 v16
                             -> coe
                                  seq (coe v4)
                                  (case coe v3 of
                                     MAlonzo.Code.Algorithmic.C_wrap_220 v20
                                       -> coe
                                            C__'9659'__40
                                            (coe
                                               MAlonzo.Code.Type.BetaNBE.d_nf_258
                                               (coe MAlonzo.Code.Type.C_'8709'_4)
                                               (coe MAlonzo.Code.Utils.C_'42'_756)
                                               (coe
                                                  MAlonzo.Code.Type.C__'183'__30 v14
                                                  (coe
                                                     MAlonzo.Code.Type.C__'183'__30
                                                     (coe
                                                        MAlonzo.Code.Utils.C__'8658'__760 (coe v14)
                                                        (coe MAlonzo.Code.Utils.C_'42'_756))
                                                     (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                                        (coe MAlonzo.Code.Type.C_'8709'_4)
                                                        (coe
                                                           MAlonzo.Code.Utils.C__'8658'__760
                                                           (coe
                                                              MAlonzo.Code.Utils.C__'8658'__760
                                                              (coe v14)
                                                              (coe MAlonzo.Code.Utils.C_'42'_756))
                                                           (coe
                                                              MAlonzo.Code.Utils.C__'8658'__760
                                                              (coe v14)
                                                              (coe MAlonzo.Code.Utils.C_'42'_756)))
                                                        (coe v15))
                                                     (coe
                                                        MAlonzo.Code.Type.C_ƛ_28
                                                        (coe
                                                           MAlonzo.Code.Type.C_μ_32 v14
                                                           (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                                              (coe
                                                                 MAlonzo.Code.Type.C__'44''8902'__6
                                                                 (coe MAlonzo.Code.Type.C_'8709'_4)
                                                                 (coe v14))
                                                              (coe
                                                                 MAlonzo.Code.Utils.C__'8658'__760
                                                                 (coe
                                                                    MAlonzo.Code.Utils.C__'8658'__760
                                                                    (coe v14)
                                                                    (coe
                                                                       MAlonzo.Code.Utils.C_'42'_756))
                                                                 (coe
                                                                    MAlonzo.Code.Utils.C__'8658'__760
                                                                    (coe v14)
                                                                    (coe
                                                                       MAlonzo.Code.Utils.C_'42'_756)))
                                                              (coe
                                                                 MAlonzo.Code.Type.BetaNormal.d_weakenNf_122
                                                                 (coe MAlonzo.Code.Type.C_'8709'_4)
                                                                 (coe
                                                                    MAlonzo.Code.Utils.C__'8658'__760
                                                                    (coe
                                                                       MAlonzo.Code.Utils.C__'8658'__760
                                                                       (coe v14)
                                                                       (coe
                                                                          MAlonzo.Code.Utils.C_'42'_756))
                                                                    (coe
                                                                       MAlonzo.Code.Utils.C__'8658'__760
                                                                       (coe v14)
                                                                       (coe
                                                                          MAlonzo.Code.Utils.C_'42'_756)))
                                                                 v14 v15))
                                                           (coe
                                                              MAlonzo.Code.Type.C_'96'_22
                                                              (coe MAlonzo.Code.Type.C_Z_16)))))
                                                  (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                                     (coe MAlonzo.Code.Type.C_'8709'_4) (coe v14)
                                                     (coe v16))))
                                            (coe v8) (coe v20)
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Algorithmic.ReductionEC.C_constr'45'_420 v11 v13 v14 v16 v18 v19 v20 v21
                      -> case coe v6 of
                           MAlonzo.Code.Type.BetaNormal.C_SOP_28 v23 v24
                             -> let v25
                                      = coe
                                          MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v24)
                                          (coe v14) in
                                coe
                                  (coe
                                     seq (coe v25)
                                     (case coe v21 of
                                        MAlonzo.Code.Utils.List.C_'91''93'_308
                                          -> coe
                                               C__'9669'__46
                                               (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v23 v24)
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Algorithmic.C_constr_240 v14 v25
                                                  (coe
                                                     MAlonzo.Code.Utils.List.du_IBwd2IList_538
                                                     (coe
                                                        MAlonzo.Code.Utils.List.du__'60''62''60'__54
                                                        (coe v11)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe v1)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                     (coe
                                                        MAlonzo.Code.Utils.List.C__'58''60'__408 v19
                                                        v3)))
                                               (coe
                                                  MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'constr_234
                                                  (coe
                                                     MAlonzo.Code.Utils.List.du__'60''62''60'__54
                                                     (coe v11)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe v1)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                  (coe
                                                     MAlonzo.Code.Utils.List.C__'58''60'__408 v19
                                                     v3)
                                                  (coe
                                                     MAlonzo.Code.Utils.List.C__'58''60'__850 v20
                                                     v4))
                                        MAlonzo.Code.Utils.List.C__'8759'__314 v28 v29
                                          -> case coe v13 of
                                               (:) v30 v31
                                                 -> coe
                                                      C__'9659'__40 (coe v30)
                                                      (coe
                                                         C__'44'__30
                                                         (coe
                                                            MAlonzo.Code.Type.BetaNormal.C_SOP_28
                                                            v23 v24)
                                                         v8
                                                         (coe
                                                            MAlonzo.Code.Algorithmic.ReductionEC.C_constr'45'_420
                                                            (coe
                                                               MAlonzo.Code.Utils.List.C__'58''60'__12
                                                               (coe v11) (coe v1))
                                                            v31 v14 v25
                                                            (coe
                                                               MAlonzo.Code.Utils.List.C_bubble_700
                                                               v18)
                                                            (coe
                                                               MAlonzo.Code.Utils.List.C__'58''60'__408
                                                               v19 v3)
                                                            (coe
                                                               MAlonzo.Code.Utils.List.C__'58''60'__850
                                                               v20 v4)
                                                            v29))
                                                      (coe v28)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Algorithmic.ReductionEC.C_case'45'_428 v13
                      -> case coe v1 of
                           MAlonzo.Code.Type.BetaNormal.C_SOP_28 v15 v16
                             -> case coe v4 of
                                  MAlonzo.Code.Algorithmic.ReductionEC.C_V'45'constr_234 v22 v24 v25
                                    -> case coe v3 of
                                         MAlonzo.Code.Algorithmic.C_constr_240 v29 v31 v33
                                           -> coe
                                                C__'9659'__40
                                                (coe
                                                   MAlonzo.Code.Algorithmic.du_mkCaseType_156 v6
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.du_lookup_82
                                                      (coe v16) (coe v29)))
                                                (coe
                                                   du_pushValueFrames_110 (coe v6)
                                                   (coe
                                                      MAlonzo.Code.Utils.List.du__'60''62''60'__54
                                                      (coe MAlonzo.Code.Utils.List.C_'91''93'_10)
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.du_lookup_82
                                                         (coe v16) (coe v29)))
                                                   (coe v8) (coe v24) (coe v25))
                                                (coe
                                                   MAlonzo.Code.Algorithmic.du_lookupCase_328
                                                   (coe v16) (coe v29) (coe v13))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'9633'_50 v1 v2 -> coe v0
      C_'9670'_54 v1 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.CK.stepper
d_stepper_372 ::
  Integer ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_State_34 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Utils.T_RuntimeError_396 T_State_34
d_stepper_372 v0 ~v1 v2 = du_stepper_372 v0 v2
du_stepper_372 ::
  Integer ->
  T_State_34 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Utils.T_RuntimeError_396 T_State_34
du_stepper_372 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Utils.C_inj'8321'_12
             (coe MAlonzo.Code.Utils.C_gasError_398)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v3 = coe du_step_122 (coe v1) in
              coe
                (case coe v3 of
                   C__'9659'__40 v4 v5 v6 -> coe du_stepper_372 (coe v2) (coe v3)
                   C__'9669'__46 v4 v5 v6 v7 -> coe du_stepper_372 (coe v2) (coe v3)
                   C_'9633'_50 v4 v5 -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v3)
                   C_'9670'_54 v4 -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v3)
                   _ -> MAlonzo.RTE.mazUnreachableError))
