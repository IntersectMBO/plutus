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

module MAlonzo.Code.Untyped.CEKWithCost where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Cost.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Utils

-- Untyped.CEKWithCost.CekM
d_CekM_26 ::
  () -> MAlonzo.Code.Cost.Base.T_MachineParameters_46 -> () -> ()
d_CekM_26 = erased
-- Untyped.CEKWithCost.spend
d_spend_28 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Cost.Base.T_StepKind_6 ->
  MAlonzo.Code.Utils.T_Writer_352
d_spend_28 ~v0 v1 v2 = du_spend_28 v1 v2
du_spend_28 ::
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Cost.Base.T_StepKind_6 ->
  MAlonzo.Code.Utils.T_Writer_352
du_spend_28 v0 v1
  = coe
      MAlonzo.Code.Utils.du_tell_392
      (coe
         MAlonzo.Code.Cost.Base.d_cekMachineCost_58 v0
         (coe MAlonzo.Code.Cost.Base.C_BStep_36 (coe v1)))
-- Untyped.CEKWithCost.spendStartupCost
d_spendStartupCost_32 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Utils.T_Writer_352
d_spendStartupCost_32 ~v0 v1 = du_spendStartupCost_32 v1
du_spendStartupCost_32 ::
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Utils.T_Writer_352
du_spendStartupCost_32 v0
  = coe
      MAlonzo.Code.Utils.du_tell_392
      (coe MAlonzo.Code.Cost.Base.du_startupCost_66 (coe v0))
-- Untyped.CEKWithCost.extractConstants
d_extractConstants_48 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__168 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__168 ->
  MAlonzo.Code.Untyped.CEK.T_BApp_42 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_extractConstants_48 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9
  = du_extractConstants_48 v5 v8 v9
du_extractConstants_48 ::
  MAlonzo.Code.Utils.T__'8724'_'8803'__168 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__168 ->
  MAlonzo.Code.Untyped.CEK.T_BApp_42 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_extractConstants_48 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Untyped.CEK.C_base_94
        -> coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
      MAlonzo.Code.Untyped.CEK.C_app_106 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Utils.C_bubble_180 v13
               -> coe
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                    (coe du_extractConstants_48 (coe v0) (coe v13) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.CEK.C_app'8902'_120 v9
        -> case coe v0 of
             MAlonzo.Code.Utils.C_bubble_180 v13
               -> coe du_extractConstants_48 (coe v13) (coe v1) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.CEKWithCost.spendBuiltin
d_spendBuiltin_58 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Untyped.CEK.T_BApp_42 ->
  MAlonzo.Code.Utils.T_Writer_352
d_spendBuiltin_58 ~v0 v1 v2 v3 = du_spendBuiltin_58 v1 v2 v3
du_spendBuiltin_58 ::
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Untyped.CEK.T_BApp_42 ->
  MAlonzo.Code.Utils.T_Writer_352
du_spendBuiltin_58 v0 v1 v2
  = coe
      MAlonzo.Code.Utils.du_tell_392
      (coe
         MAlonzo.Code.Cost.Base.d_cekMachineCost_58 v0
         (coe
            MAlonzo.Code.Cost.Base.C_BBuiltinApp_40 (coe v1)
            (coe du_argsizes_68 (coe v1) (coe v2))))
-- Untyped.CEKWithCost._.argsizes
d_argsizes_68 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Untyped.CEK.T_BApp_42 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_argsizes_68 ~v0 ~v1 v2 v3 = du_argsizes_68 v2 v3
du_argsizes_68 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Untyped.CEK.T_BApp_42 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_argsizes_68 v0 v1
  = coe
      MAlonzo.Code.Data.Vec.Base.du_reverse_616
      (coe
         du_extractConstants_48
         (coe
            MAlonzo.Code.Utils.d_alldone_228
            (coe
               MAlonzo.Code.Builtin.Signature.d_fv_96
               (coe MAlonzo.Code.Builtin.d_signature_298 (coe v0))))
         (coe
            MAlonzo.Code.Utils.d_alldone_228
            (coe
               MAlonzo.Code.Builtin.Signature.d_args'9839'_92
               (coe MAlonzo.Code.Builtin.d_signature_298 (coe v0))))
         (coe v1))
-- Untyped.CEKWithCost.stepC
d_stepC_70 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Utils.T_Writer_352
d_stepC_70 ~v0 v1 v2 = du_stepC_70 v1 v2
du_stepC_70 ::
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Utils.T_Writer_352
du_stepC_70 v0 v1
  = case coe v1 of
      MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222 v2 v3 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Untyped.C_'96'_18 v6
               -> coe
                    MAlonzo.Code.Utils.du__'62''62'__262
                    (coe
                       MAlonzo.Code.Utils.du_WriterMonad_376
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                       (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                    (coe du_spend_28 (coe v0) (coe MAlonzo.Code.Cost.Base.C_BVar_10))
                    (coe
                       MAlonzo.Code.Utils.C__'44'__366
                       (coe
                          MAlonzo.Code.Untyped.CEK.C__'9669'__224 (coe v3)
                          (coe MAlonzo.Code.Untyped.CEK.du_lookup_232 (coe v4) (coe v6)))
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
             MAlonzo.Code.Untyped.C_ƛ_20 v6
               -> coe
                    MAlonzo.Code.Utils.du__'62''62'__262
                    (coe
                       MAlonzo.Code.Utils.du_WriterMonad_376
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                       (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                    (coe
                       du_spend_28 (coe v0) (coe MAlonzo.Code.Cost.Base.C_BLamAbs_12))
                    (coe
                       MAlonzo.Code.Utils.C__'44'__366
                       (coe
                          MAlonzo.Code.Untyped.CEK.C__'9669'__224 (coe v3)
                          (coe
                             MAlonzo.Code.Untyped.CEK.C_V'45'ƛ_46 (coe v2) (coe v4) (coe v6)))
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
             MAlonzo.Code.Untyped.C__'183'__22 v6 v7
               -> coe
                    MAlonzo.Code.Utils.du__'62''62'__262
                    (coe
                       MAlonzo.Code.Utils.du_WriterMonad_376
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                       (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                    (coe du_spend_28 (coe v0) (coe MAlonzo.Code.Cost.Base.C_BApply_14))
                    (coe
                       MAlonzo.Code.Utils.C__'44'__366
                       (coe
                          MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222 (coe v2)
                          (coe
                             MAlonzo.Code.Untyped.CEK.C__'44'__12 (coe v3)
                             (coe
                                MAlonzo.Code.Untyped.CEK.C_'45''183'_200 (coe v2) (coe v4)
                                (coe v7)))
                          (coe v4) (coe v6))
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
             MAlonzo.Code.Untyped.C_force_24 v6
               -> coe
                    MAlonzo.Code.Utils.du__'62''62'__262
                    (coe
                       MAlonzo.Code.Utils.du_WriterMonad_376
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                       (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                    (coe du_spend_28 (coe v0) (coe MAlonzo.Code.Cost.Base.C_BForce_18))
                    (coe
                       MAlonzo.Code.Utils.C__'44'__366
                       (coe
                          MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222 (coe v2)
                          (coe
                             MAlonzo.Code.Untyped.CEK.C__'44'__12 (coe v3)
                             (coe MAlonzo.Code.Untyped.CEK.C_force'45'_206))
                          (coe v4) (coe v6))
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
             MAlonzo.Code.Untyped.C_delay_26 v6
               -> coe
                    MAlonzo.Code.Utils.du__'62''62'__262
                    (coe
                       MAlonzo.Code.Utils.du_WriterMonad_376
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                       (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                    (coe du_spend_28 (coe v0) (coe MAlonzo.Code.Cost.Base.C_BDelay_16))
                    (coe
                       MAlonzo.Code.Utils.C__'44'__366
                       (coe
                          MAlonzo.Code.Untyped.CEK.C__'9669'__224 (coe v3)
                          (coe
                             MAlonzo.Code.Untyped.CEK.C_V'45'delay_54 (coe v2) (coe v4)
                             (coe v6)))
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
             MAlonzo.Code.Untyped.C_con_28 v6
               -> case coe v6 of
                    MAlonzo.Code.RawU.C_tmCon_206 v7 v8
                      -> coe
                           MAlonzo.Code.Utils.du__'62''62'__262
                           (coe
                              MAlonzo.Code.Utils.du_WriterMonad_376
                              (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                              (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                           (coe du_spend_28 (coe v0) (coe MAlonzo.Code.Cost.Base.C_BConst_8))
                           (coe
                              MAlonzo.Code.Utils.C__'44'__366
                              (coe
                                 MAlonzo.Code.Untyped.CEK.C__'9669'__224 (coe v3)
                                 (coe MAlonzo.Code.Untyped.CEK.C_V'45'con_50 (coe v7) (coe v8)))
                              (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Untyped.C_constr_34 v6 v7
               -> case coe v7 of
                    []
                      -> coe
                           MAlonzo.Code.Utils.du__'62''62'__262
                           (coe
                              MAlonzo.Code.Utils.du_WriterMonad_376
                              (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                              (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                           (coe
                              du_spend_28 (coe v0) (coe MAlonzo.Code.Cost.Base.C_BConstr_22))
                           (coe
                              MAlonzo.Code.Utils.C__'44'__366
                              (coe
                                 MAlonzo.Code.Untyped.CEK.C__'9669'__224 (coe v3)
                                 (coe
                                    MAlonzo.Code.Untyped.CEK.C_V'45'constr_60 (coe v6)
                                    (coe MAlonzo.Code.Untyped.CEK.C_ε_10)))
                              (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
                    (:) v8 v9
                      -> coe
                           MAlonzo.Code.Utils.du__'62''62'__262
                           (coe
                              MAlonzo.Code.Utils.du_WriterMonad_376
                              (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                              (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                           (coe
                              du_spend_28 (coe v0) (coe MAlonzo.Code.Cost.Base.C_BConstr_22))
                           (coe
                              MAlonzo.Code.Utils.C__'44'__366
                              (coe
                                 MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222 (coe v2)
                                 (coe
                                    MAlonzo.Code.Untyped.CEK.C__'44'__12 (coe v3)
                                    (coe
                                       MAlonzo.Code.Untyped.CEK.C_constr'45'_210 (coe v2) (coe v6)
                                       (coe MAlonzo.Code.Untyped.CEK.C_ε_10) (coe v4) (coe v9)))
                                 (coe v4) (coe v8))
                              (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Untyped.C_case_40 v6 v7
               -> coe
                    MAlonzo.Code.Utils.du__'62''62'__262
                    (coe
                       MAlonzo.Code.Utils.du_WriterMonad_376
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                       (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                    (coe du_spend_28 (coe v0) (coe MAlonzo.Code.Cost.Base.C_BCase_24))
                    (coe
                       MAlonzo.Code.Utils.C__'44'__366
                       (coe
                          MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222 (coe v2)
                          (coe
                             MAlonzo.Code.Untyped.CEK.C__'44'__12 (coe v3)
                             (coe
                                MAlonzo.Code.Untyped.CEK.C_case'45'_216 (coe v2) (coe v4)
                                (coe v7)))
                          (coe v4) (coe v6))
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
             MAlonzo.Code.Untyped.C_builtin_44 v6
               -> coe
                    MAlonzo.Code.Utils.du__'62''62'__262
                    (coe
                       MAlonzo.Code.Utils.du_WriterMonad_376
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                       (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                    (coe
                       du_spend_28 (coe v0) (coe MAlonzo.Code.Cost.Base.C_BBuiltin_20))
                    (coe
                       MAlonzo.Code.Utils.C__'44'__366
                       (coe
                          MAlonzo.Code.Untyped.CEK.C__'9669'__224 (coe v3)
                          (coe MAlonzo.Code.Untyped.CEK.d_ival_972 (coe v6)))
                       (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Utils.C__'44'__366
                    (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                    (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.CEK.C__'9669'__224 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Untyped.CEK.C_ε_10
               -> coe
                    MAlonzo.Code.Utils.C__'44'__366
                    (coe MAlonzo.Code.Untyped.CEK.C_'9633'_226 (coe v3))
                    (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
             MAlonzo.Code.Untyped.CEK.C__'44'__12 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Untyped.CEK.C_'45''183'_200 v6 v7 v8
                      -> coe
                           MAlonzo.Code.Utils.C__'44'__366
                           (coe
                              MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222 (coe v6)
                              (coe
                                 MAlonzo.Code.Untyped.CEK.C__'44'__12 (coe v4)
                                 (coe MAlonzo.Code.Untyped.CEK.C__'183''45'_204 (coe v3)))
                              (coe v7) (coe v8))
                           (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                    MAlonzo.Code.Untyped.CEK.C_'45''183'v_202 v6
                      -> coe
                           MAlonzo.Code.Utils.C__'44'__366
                           (coe
                              MAlonzo.Code.Untyped.CEK.C__'9669'__224
                              (coe
                                 MAlonzo.Code.Untyped.CEK.C__'44'__12 (coe v4)
                                 (coe MAlonzo.Code.Untyped.CEK.C__'183''45'_204 (coe v3)))
                              (coe v6))
                           (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                    MAlonzo.Code.Untyped.CEK.C__'183''45'_204 v6
                      -> case coe v6 of
                           MAlonzo.Code.Untyped.CEK.C_V'45'ƛ_46 v7 v8 v9
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe
                                     MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222
                                     (coe addInt (coe (1 :: Integer)) (coe v7)) (coe v4)
                                     (coe MAlonzo.Code.Untyped.CEK.C__'8759'__22 v8 v3) (coe v9))
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'con_50 v7 v8
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'delay_54 v7 v8 v9
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'constr_60 v7 v8
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'I'8658'_74 v7 v8 v9 v10 v11 v12 v13
                             -> case coe v11 of
                                  0 -> coe
                                         MAlonzo.Code.Utils.du__'62''62'__262
                                         (coe
                                            MAlonzo.Code.Utils.du_WriterMonad_376
                                            (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                                            (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
                                         (coe
                                            du_spendBuiltin_58 (coe v0) (coe v7)
                                            (coe MAlonzo.Code.Untyped.CEK.C_app_106 v13 v3))
                                         (coe
                                            MAlonzo.Code.Utils.C__'44'__366
                                            (coe
                                               MAlonzo.Code.Utils.du_either_22
                                               (coe
                                                  MAlonzo.Code.Untyped.CEK.d_BUILTIN_278 v7
                                                  (coe MAlonzo.Code.Untyped.CEK.C_app_106 v13 v3))
                                               (coe
                                                  (\ v14 ->
                                                     coe MAlonzo.Code.Untyped.CEK.C_'9670'_228))
                                               (coe
                                                  MAlonzo.Code.Untyped.CEK.C__'9669'__224 (coe v4)))
                                            (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
                                  _ -> let v14 = subInt (coe v11) (coe (1 :: Integer)) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Utils.C__'44'__366
                                            (coe
                                               MAlonzo.Code.Untyped.CEK.C__'9669'__224 (coe v4)
                                               (coe
                                                  MAlonzo.Code.Untyped.CEK.d_V'45'I_258 (coe v7)
                                                  (coe v8) (coe (0 :: Integer)) (coe v9)
                                                  (coe addInt (coe (1 :: Integer)) (coe v10))
                                                  (coe v14)
                                                  (coe MAlonzo.Code.Utils.C_bubble_180 v12)
                                                  (coe MAlonzo.Code.Untyped.CEK.C_app_106 v13 v3)))
                                            (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0)))
                           MAlonzo.Code.Untyped.CEK.C_V'45'IΠ_90 v7 v8 v9 v10 v11 v12 v13 v14
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Untyped.CEK.C_force'45'_206
                      -> case coe v3 of
                           MAlonzo.Code.Untyped.CEK.C_V'45'ƛ_46 v6 v7 v8
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'con_50 v6 v7
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'delay_54 v6 v7 v8
                             -> coe
                                  du_stepC_70 (coe v0)
                                  (coe
                                     MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222 (coe v6) (coe v4)
                                     (coe v7) (coe v8))
                           MAlonzo.Code.Untyped.CEK.C_V'45'constr_60 v6 v7
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'I'8658'_74 v6 v7 v8 v9 v10 v11 v12
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'IΠ_90 v6 v7 v8 v9 v10 v11 v12 v13
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe
                                     MAlonzo.Code.Untyped.CEK.C__'9669'__224 (coe v4)
                                     (coe
                                        MAlonzo.Code.Untyped.CEK.d_V'45'I_258 (coe v6)
                                        (coe addInt (coe (1 :: Integer)) (coe v7)) (coe v8)
                                        (coe MAlonzo.Code.Utils.C_bubble_180 v9) (coe v10) (coe v11)
                                        (coe v12)
                                        (coe MAlonzo.Code.Untyped.CEK.C_app'8902'_120 v13)))
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Untyped.CEK.C_constr'45'_210 v6 v7 v8 v9 v10
                      -> case coe v10 of
                           []
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe
                                     MAlonzo.Code.Untyped.CEK.C__'9669'__224 (coe v4)
                                     (coe
                                        MAlonzo.Code.Untyped.CEK.C_V'45'constr_60 (coe v7)
                                        (coe
                                           MAlonzo.Code.Untyped.CEK.C__'44'__12 (coe v8) (coe v3))))
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           (:) v11 v12
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe
                                     MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222 (coe v6)
                                     (coe
                                        MAlonzo.Code.Untyped.CEK.C__'44'__12 (coe v4)
                                        (coe
                                           MAlonzo.Code.Untyped.CEK.C_constr'45'_210 (coe v6)
                                           (coe v7)
                                           (coe
                                              MAlonzo.Code.Untyped.CEK.C__'44'__12 (coe v8)
                                              (coe v3))
                                           (coe v9) (coe v12)))
                                     (coe v9) (coe v11))
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Untyped.CEK.C_case'45'_216 v6 v7 v8
                      -> case coe v3 of
                           MAlonzo.Code.Untyped.CEK.C_V'45'ƛ_46 v9 v10 v11
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'con_50 v9 v10
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'delay_54 v9 v10 v11
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'constr_60 v9 v10
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe
                                     MAlonzo.Code.Data.Maybe.Base.du_maybe_32
                                     (coe
                                        MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222 (coe v6)
                                        (coe
                                           MAlonzo.Code.Untyped.CEK.d_pushValueFrames_976 (coe v4)
                                           (coe v10))
                                        (coe v7))
                                     (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                     (coe
                                        MAlonzo.Code.Untyped.CEK.du_lookup'63'_988 (coe v9)
                                        (coe v8)))
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'I'8658'_74 v9 v10 v11 v12 v13 v14 v15
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           MAlonzo.Code.Untyped.CEK.C_V'45'IΠ_90 v9 v10 v11 v12 v13 v14 v15 v16
                             -> coe
                                  MAlonzo.Code.Utils.C__'44'__366
                                  (coe MAlonzo.Code.Untyped.CEK.C_'9670'_228)
                                  (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.CEK.C_'9633'_226 v2
        -> coe
             MAlonzo.Code.Utils.C__'44'__366 (coe v1)
             (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
      MAlonzo.Code.Untyped.CEK.C_'9670'_228
        -> coe
             MAlonzo.Code.Utils.C__'44'__366 (coe v1)
             (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.CEKWithCost.stepperC-internal
d_stepperC'45'internal_314 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  Integer ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Utils.T_Writer_352
d_stepperC'45'internal_314 ~v0 v1 v2 v3
  = du_stepperC'45'internal_314 v1 v2 v3
du_stepperC'45'internal_314 ::
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  Integer ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Utils.T_Writer_352
du_stepperC'45'internal_314 v0 v1 v2
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Utils.C__'44'__366
             (coe
                MAlonzo.Code.Utils.C_inj'8321'_12
                (coe MAlonzo.Code.Utils.C_gasError_398))
             (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Utils.C__'44'__366
                (coe
                   MAlonzo.Code.Utils.d_wrvalue_362
                   (coe
                      du_go_328 (coe v0) (coe v3)
                      (coe
                         MAlonzo.Code.Utils.d_wrvalue_362
                         (coe du_stepC_70 (coe v0) (coe v2)))))
                (coe
                   MAlonzo.Code.Cost.Base.d__'8729'__62 v0
                   (MAlonzo.Code.Utils.d_accum_364
                      (coe du_stepC_70 (coe v0) (coe v2)))
                   (MAlonzo.Code.Utils.d_accum_364
                      (coe
                         du_go_328 (coe v0) (coe v3)
                         (coe
                            MAlonzo.Code.Utils.d_wrvalue_362
                            (coe du_stepC_70 (coe v0) (coe v2)))))))
-- Untyped.CEKWithCost._.go
d_go_328 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  Integer ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Utils.T_Writer_352
d_go_328 ~v0 v1 v2 ~v3 v4 = du_go_328 v1 v2 v4
du_go_328 ::
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  Integer ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Utils.T_Writer_352
du_go_328 v0 v1 v2
  = let v3
          = coe du_stepperC'45'internal_314 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v2 of
         MAlonzo.Code.Untyped.CEK.C_'9633'_226 v4
           -> coe
                MAlonzo.Code.Utils.C__'44'__366
                (coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v2))
                (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
         MAlonzo.Code.Untyped.CEK.C_'9670'_228
           -> coe
                MAlonzo.Code.Utils.C__'44'__366
                (coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v2))
                (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
         _ -> coe v3)
-- Untyped.CEKWithCost.stepperC
d_stepperC_338 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  Integer ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Utils.T_Writer_352
d_stepperC_338 ~v0 v1 v2 v3 = du_stepperC_338 v1 v2 v3
du_stepperC_338 ::
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  Integer ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Utils.T_Writer_352
du_stepperC_338 v0 v1 v2
  = coe
      MAlonzo.Code.Utils.du__'62''62'__262
      (coe
         MAlonzo.Code.Utils.du_WriterMonad_376
         (coe MAlonzo.Code.Cost.Base.d_ε_60 (coe v0))
         (coe MAlonzo.Code.Cost.Base.d__'8729'__62 (coe v0)))
      (coe du_spendStartupCost_32 (coe v0))
      (coe du_stepperC'45'internal_314 (coe v0) (coe v1) (coe v2))
-- Untyped.CEKWithCost.cekStepEquivalence
d_cekStepEquivalence_346 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cekStepEquivalence_346 = erased
-- Untyped.CEKWithCost.cekStepperEquivalence
d_cekStepperEquivalence_472 ::
  () ->
  MAlonzo.Code.Cost.Base.T_MachineParameters_46 ->
  Integer ->
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cekStepperEquivalence_472 = erased
