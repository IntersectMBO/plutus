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

module MAlonzo.Code.Algorithmic.ReductionEC where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Algorithmic.CEK
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Algorithmic.ReductionEC._.SigTy
d_SigTy_6 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Algorithmic.ReductionEC._.sig2SigTy
d_sig2SigTy_12 ::
  MAlonzo.Code.Builtin.Signature.T_Sig_72 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266
d_sig2SigTy_12
  = coe
      MAlonzo.Code.Builtin.Signature.du_sig2SigTy_398
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v2)
      (coe
         (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v3))
      (\ v0 v1 v2 v3 v4 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_'94'_12))
      (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_con_22 v1)
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v1 v2)
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v1 v2)
-- Algorithmic.ReductionEC.Value
d_Value_28 a0 a1 = ()
data T_Value_28
  = C_V'45'ƛ_138 | C_V'45'Λ_146 | C_V'45'wrap_156 T_Value_28 |
    C_V'45'con_162 |
    C_V'45'I'8658'_184 MAlonzo.Code.Builtin.T_Builtin_2 Integer
                       MAlonzo.Code.Utils.T__'8724'_'8803'__120 Integer Integer
                       MAlonzo.Code.Utils.T__'8724'_'8803'__120
                       MAlonzo.Code.Builtin.Signature.T_SigTy_266 T_BApp_74 |
    C_V'45'IΠ_208 MAlonzo.Code.Builtin.T_Builtin_2 Integer Integer
                  MAlonzo.Code.Utils.T__'8724'_'8803'__120 Integer Integer
                  MAlonzo.Code.Utils.T__'8724'_'8803'__120
                  MAlonzo.Code.Builtin.Signature.T_SigTy_266 T_BApp_74 |
    C_V'45'constr_234 MAlonzo.Code.Utils.List.T_Bwd_6
                      MAlonzo.Code.Utils.List.T_IBwd_396
                      MAlonzo.Code.Utils.List.T_IIBwd_832
-- Algorithmic.ReductionEC.VList
d_VList_34 ::
  MAlonzo.Code.Utils.List.T_Bwd_6 ->
  MAlonzo.Code.Utils.List.T_IBwd_396 -> ()
d_VList_34 = erased
-- Algorithmic.ReductionEC.deval
d_deval_40 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  T_Value_28 -> MAlonzo.Code.Algorithmic.T__'8866'__178
d_deval_40 ~v0 v1 ~v2 = du_deval_40 v1
du_deval_40 ::
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du_deval_40 v0 = coe v0
-- Algorithmic.ReductionEC.deval-VecList
d_deval'45'VecList_48 ::
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_deval'45'VecList_48 ~v0 v1 = du_deval'45'VecList_48 v1
du_deval'45'VecList_48 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_deval'45'VecList_48 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe v0
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> coe
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe (\ v4 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                (coe v2))
             (coe du_deval'45'VecList_48 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.ReductionEC.BApp
d_BApp_74 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
data T_BApp_74
  = C_base_78 | C_step_100 T_BApp_74 T_Value_28 |
    C_step'8902'_130 MAlonzo.Code.Builtin.Signature.T_SigTy_266
                     T_BApp_74
-- Algorithmic.ReductionEC.red2cekVal
d_red2cekVal_240 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  T_Value_28 -> MAlonzo.Code.Algorithmic.CEK.T_Value_52
d_red2cekVal_240 v0 v1 v2
  = case coe v2 of
      C_V'45'ƛ_138
        -> case coe v1 of
             MAlonzo.Code.Algorithmic.C_ƛ_190 v8
               -> coe
                    MAlonzo.Code.Algorithmic.CEK.C_V'45'ƛ_64
                    (coe MAlonzo.Code.Algorithmic.C_'8709'_4) v8
                    (coe MAlonzo.Code.Algorithmic.CEK.C_'91''93'_202)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_V'45'Λ_146
        -> case coe v1 of
             MAlonzo.Code.Algorithmic.C_Λ_202 v8
               -> coe
                    MAlonzo.Code.Algorithmic.CEK.C_V'45'Λ_74
                    (coe MAlonzo.Code.Algorithmic.C_'8709'_4) v8
                    (coe MAlonzo.Code.Algorithmic.CEK.C_'91''93'_202)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_V'45'wrap_156 v7
        -> case coe v0 of
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v9 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Algorithmic.C_wrap_220 v15
                      -> coe
                           MAlonzo.Code.Algorithmic.CEK.C_V'45'wrap_82
                           (d_red2cekVal_240
                              (coe
                                 MAlonzo.Code.Type.BetaNBE.d_nf_258
                                 (coe MAlonzo.Code.Type.C_'8709'_4)
                                 (coe MAlonzo.Code.Utils.C_'42'_654)
                                 (coe
                                    MAlonzo.Code.Type.C__'183'__30 v9
                                    (coe
                                       MAlonzo.Code.Type.C__'183'__30
                                       (coe
                                          MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                          (coe MAlonzo.Code.Utils.C_'42'_654))
                                       (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                          (coe MAlonzo.Code.Type.C_'8709'_4)
                                          (coe
                                             MAlonzo.Code.Utils.C__'8658'__658
                                             (coe
                                                MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                                (coe MAlonzo.Code.Utils.C_'42'_654))
                                             (coe
                                                MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                                (coe MAlonzo.Code.Utils.C_'42'_654)))
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
                                                   MAlonzo.Code.Utils.C__'8658'__658
                                                   (coe
                                                      MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                                      (coe MAlonzo.Code.Utils.C_'42'_654))
                                                   (coe
                                                      MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                                      (coe MAlonzo.Code.Utils.C_'42'_654)))
                                                (coe
                                                   MAlonzo.Code.Type.BetaNormal.d_weakenNf_122
                                                   (coe MAlonzo.Code.Type.C_'8709'_4)
                                                   (coe
                                                      MAlonzo.Code.Utils.C__'8658'__658
                                                      (coe
                                                         MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                                         (coe MAlonzo.Code.Utils.C_'42'_654))
                                                      (coe
                                                         MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                                         (coe MAlonzo.Code.Utils.C_'42'_654)))
                                                   v9 v10))
                                             (coe
                                                MAlonzo.Code.Type.C_'96'_22
                                                (coe MAlonzo.Code.Type.C_Z_16)))))
                                    (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                       (coe MAlonzo.Code.Type.C_'8709'_4) (coe v9) (coe v11))))
                              (coe v15) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_V'45'con_162
        -> case coe v1 of
             MAlonzo.Code.Algorithmic.C_con_258 v5 v7
               -> coe MAlonzo.Code.Algorithmic.CEK.C_V'45'con_86 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      C_V'45'I'8658'_184 v3 v6 v7 v8 v9 v10 v11 v13
        -> coe
             MAlonzo.Code.Algorithmic.CEK.C_V'45'I'8658'_106 v3 v6 v7 v8 v9 v10
             v11 (coe du_red2cekBApp_266 (coe v7) (coe v10) (coe v1) (coe v13))
      C_V'45'IΠ_208 v3 v6 v7 v8 v9 v10 v11 v12 v14
        -> coe
             MAlonzo.Code.Algorithmic.CEK.C_V'45'IΠ_128 v3 v6 v7 v8 v9 v10 v11
             v12 (coe du_red2cekBApp_266 (coe v8) (coe v11) (coe v1) (coe v14))
      C_V'45'constr_234 v8 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Type.BetaNormal.C_SOP_28 v15 v16
               -> case coe v1 of
                    MAlonzo.Code.Algorithmic.C_constr_240 v18 v20 v22
                      -> coe
                           MAlonzo.Code.Algorithmic.CEK.C_V'45'constr_140 v18
                           (coe
                              MAlonzo.Code.Utils.List.du__'60''62''60'__54
                              (coe MAlonzo.Code.Utils.List.C_'91''93'_10)
                              (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v18)))
                           (d_red2cekVal'45'VList_280
                              (coe
                                 MAlonzo.Code.Utils.List.du__'60''62''60'__54
                                 (coe MAlonzo.Code.Utils.List.C_'91''93'_10)
                                 (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v18)))
                              (coe v10) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.ReductionEC.red2cekBApp
d_red2cekBApp_266 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  T_BApp_74 -> MAlonzo.Code.Algorithmic.CEK.T_BApp_48
d_red2cekBApp_266 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 ~v9 v10 ~v11
                  v12
  = du_red2cekBApp_266 v4 v8 v10 v12
du_red2cekBApp_266 ::
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  T_BApp_74 -> MAlonzo.Code.Algorithmic.CEK.T_BApp_48
du_red2cekBApp_266 v0 v1 v2 v3
  = case coe v3 of
      C_base_78 -> coe MAlonzo.Code.Algorithmic.CEK.C_base_144
      C_step_100 v13 v15
        -> case coe v1 of
             MAlonzo.Code.Utils.C_bubble_132 v19
               -> case coe v2 of
                    MAlonzo.Code.Algorithmic.C__'183'__196 v20 v22 v23
                      -> coe
                           MAlonzo.Code.Algorithmic.CEK.C__'36'__162 v20
                           (coe du_red2cekBApp_266 (coe v0) (coe v19) (coe v22) (coe v13))
                           (d_red2cekVal_240 (coe v20) (coe v23) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_step'8902'_130 v13 v15
        -> case coe v0 of
             MAlonzo.Code.Utils.C_bubble_132 v22
               -> case coe v2 of
                    MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v23 v25 v26 v27
                      -> coe
                           MAlonzo.Code.Algorithmic.CEK.C__'36''36'__190 v23 v25 v13
                           (coe du_red2cekBApp_266 (coe v22) (coe v1) (coe v26) (coe v15)) v27
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.ReductionEC.red2cekVal-VList
d_red2cekVal'45'VList_280 ::
  MAlonzo.Code.Utils.List.T_Bwd_6 ->
  MAlonzo.Code.Utils.List.T_IBwd_396 ->
  MAlonzo.Code.Utils.List.T_IIBwd_832 ->
  MAlonzo.Code.Utils.List.T_IBwd_396
d_red2cekVal'45'VList_280 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Utils.List.C_'91''93'_840
        -> coe MAlonzo.Code.Utils.List.C_'91''93'_402
      MAlonzo.Code.Utils.List.C__'58''60'__850 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Utils.List.C__'58''60'__12 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Utils.List.C__'58''60'__408 v13 v14
                      -> coe
                           MAlonzo.Code.Utils.List.C__'58''60'__408
                           (d_red2cekVal'45'VList_280 (coe v9) (coe v13) (coe v7))
                           (d_red2cekVal_240 (coe v10) (coe v14) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.ReductionEC.BUILTIN'
d_BUILTIN''_326 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  T_BApp_74 -> MAlonzo.Code.Algorithmic.T__'8866'__178
d_BUILTIN''_326 v0 v1 v2 ~v3 v4 ~v5 v6 ~v7 v8
  = du_BUILTIN''_326 v0 v1 v2 v4 v6 v8
du_BUILTIN''_326 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  T_BApp_74 -> MAlonzo.Code.Algorithmic.T__'8866'__178
du_BUILTIN''_326 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algorithmic.CEK.du_BUILTIN''_1050 (coe v0) (coe v1)
      (coe du_red2cekBApp_266 (coe v3) (coe v4) (coe v2) (coe v5))
-- Algorithmic.ReductionEC.Error
d_Error_338 a0 a1 a2 a3 = ()
data T_Error_338 = C_E'45'error_346
-- Algorithmic.ReductionEC.Frame
d_Frame_352 a0 a1 = ()
data T_Frame_352
  = C_'45''183'__358 MAlonzo.Code.Algorithmic.T__'8866'__178 |
    C_'45''183'v_366 MAlonzo.Code.Algorithmic.T__'8866'__178
                     T_Value_28 |
    C__'183''45'_374 MAlonzo.Code.Algorithmic.T__'8866'__178
                     T_Value_28 |
    C_'45''183''8902'_382 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 |
    C_wrap'45'_390 | C_unwrap'45'_398 |
    C_constr'45'_420 MAlonzo.Code.Utils.List.T_Bwd_6
                     [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4]
                     MAlonzo.Code.Data.Fin.Base.T_Fin_10
                     [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4]
                     MAlonzo.Code.Utils.List.T__'8803'_'60''62''62'__684
                     MAlonzo.Code.Utils.List.T_IBwd_396
                     MAlonzo.Code.Utils.List.T_IIBwd_832
                     MAlonzo.Code.Utils.List.T_IList_302 |
    C_case'45'_428 MAlonzo.Code.Algorithmic.T_Cases_172
-- Algorithmic.ReductionEC._[_]ᶠ
d__'91'_'93''7584'_434 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_Frame_352 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d__'91'_'93''7584'_434 v0 ~v1 v2 v3
  = du__'91'_'93''7584'_434 v0 v2 v3
du__'91'_'93''7584'_434 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_Frame_352 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du__'91'_'93''7584'_434 v0 v1 v2
  = case coe v1 of
      C_'45''183'__358 v5
        -> case coe v0 of
             MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v7 v8
               -> coe MAlonzo.Code.Algorithmic.C__'183'__196 v7 v2 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'45''183'v_366 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v8 v9
               -> coe MAlonzo.Code.Algorithmic.C__'183'__196 v8 v2 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'183''45'_374 v5 v6
        -> coe MAlonzo.Code.Algorithmic.C__'183'__196 v0 v5 v2
      C_'45''183''8902'_382 v5
        -> case coe v0 of
             MAlonzo.Code.Type.BetaNormal.C_Π_14 v7 v8
               -> coe
                    MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v7 v8 v2 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      C_wrap'45'_390 -> coe MAlonzo.Code.Algorithmic.C_wrap_220 v2
      C_unwrap'45'_398
        -> case coe v0 of
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v7 v8 v9
               -> coe MAlonzo.Code.Algorithmic.C_unwrap_230 v7 v8 v9 v2
             _ -> MAlonzo.RTE.mazUnreachableError
      C_constr'45'_420 v4 v6 v7 v9 v11 v12 v13 v14
        -> coe
             MAlonzo.Code.Algorithmic.C_constr_240 v7
             (coe
                MAlonzo.Code.Utils.List.du__'60''62''62'__42 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v6)))
             (coe
                MAlonzo.Code.Utils.List.du__'60''62''62'I__418 (coe v4) (coe v12)
                (coe MAlonzo.Code.Utils.List.C__'8759'__314 v2 v14))
      C_case'45'_428 v6
        -> case coe v0 of
             MAlonzo.Code.Type.BetaNormal.C_SOP_28 v8 v9
               -> coe MAlonzo.Code.Algorithmic.C_case_252 v8 v9 v2 v6
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.ReductionEC.EC
d_EC_476 a0 a1 = ()
data T_EC_476
  = C_'91''93'_480 |
    C__l'183'__490 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                   T_EC_476 MAlonzo.Code.Algorithmic.T__'8866'__178 |
    C__'183'r__500 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                   MAlonzo.Code.Algorithmic.T__'8866'__178 T_Value_28 T_EC_476 |
    C__'183''8902'_'47'__512 MAlonzo.Code.Utils.T_Kind_652
                             MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 T_EC_476
                             MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 |
    C_wrap_522 T_EC_476 |
    C_unwrap_'47'__534 MAlonzo.Code.Utils.T_Kind_652
                       MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                       MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 T_EC_476 |
    C_constr_558 MAlonzo.Code.Utils.List.T_Bwd_6
                 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                 [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4]
                 MAlonzo.Code.Data.Fin.Base.T_Fin_10
                 [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4]
                 MAlonzo.Code.Utils.List.T__'8803'_'60''62''62'__684
                 MAlonzo.Code.Utils.List.T_IBwd_396
                 MAlonzo.Code.Utils.List.T_IIBwd_832
                 MAlonzo.Code.Utils.List.T_IList_302 T_EC_476 |
    C_case_568 Integer MAlonzo.Code.Data.Vec.Base.T_Vec_28
               MAlonzo.Code.Algorithmic.T_Cases_172 T_EC_476
-- Algorithmic.ReductionEC._[_]ᴱ
d__'91'_'93''7473'_574 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_EC_476 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d__'91'_'93''7473'_574 ~v0 v1 v2 v3
  = du__'91'_'93''7473'_574 v1 v2 v3
du__'91'_'93''7473'_574 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_EC_476 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du__'91'_'93''7473'_574 v0 v1 v2
  = case coe v1 of
      C_'91''93'_480 -> coe v2
      C__l'183'__490 v3 v6 v7
        -> coe
             MAlonzo.Code.Algorithmic.C__'183'__196 v3
             (coe
                du__'91'_'93''7473'_574
                (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v3 v0) (coe v6)
                (coe v2))
             v7
      C__'183'r__500 v3 v6 v7 v8
        -> coe
             MAlonzo.Code.Algorithmic.C__'183'__196 v3 v6
             (coe du__'91'_'93''7473'_574 (coe v3) (coe v8) (coe v2))
      C__'183''8902'_'47'__512 v3 v4 v7 v8
        -> coe
             MAlonzo.Code.Algorithmic.C__'183''8902'_'47'__212 v3 v4
             (coe
                du__'91'_'93''7473'_574
                (coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v3 v4) (coe v7) (coe v2))
             v8
      C_wrap_522 v7
        -> case coe v0 of
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v9 v10 v11
               -> coe
                    MAlonzo.Code.Algorithmic.C_wrap_220
                    (coe
                       du__'91'_'93''7473'_574
                       (coe
                          MAlonzo.Code.Type.BetaNBE.d_nf_258
                          (coe MAlonzo.Code.Type.C_'8709'_4)
                          (coe MAlonzo.Code.Utils.C_'42'_654)
                          (coe
                             MAlonzo.Code.Type.C__'183'__30 v9
                             (coe
                                MAlonzo.Code.Type.C__'183'__30
                                (coe
                                   MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                   (coe MAlonzo.Code.Utils.C_'42'_654))
                                (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                   (coe MAlonzo.Code.Type.C_'8709'_4)
                                   (coe
                                      MAlonzo.Code.Utils.C__'8658'__658
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                         (coe MAlonzo.Code.Utils.C_'42'_654))
                                      (coe
                                         MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                         (coe MAlonzo.Code.Utils.C_'42'_654)))
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
                                            MAlonzo.Code.Utils.C__'8658'__658
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                               (coe MAlonzo.Code.Utils.C_'42'_654))
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                               (coe MAlonzo.Code.Utils.C_'42'_654)))
                                         (coe
                                            MAlonzo.Code.Type.BetaNormal.d_weakenNf_122
                                            (coe MAlonzo.Code.Type.C_'8709'_4)
                                            (coe
                                               MAlonzo.Code.Utils.C__'8658'__658
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                                  (coe MAlonzo.Code.Utils.C_'42'_654))
                                               (coe
                                                  MAlonzo.Code.Utils.C__'8658'__658 (coe v9)
                                                  (coe MAlonzo.Code.Utils.C_'42'_654)))
                                            v9 v10))
                                      (coe
                                         MAlonzo.Code.Type.C_'96'_22
                                         (coe MAlonzo.Code.Type.C_Z_16)))))
                             (MAlonzo.Code.Type.BetaNormal.d_embNf_128
                                (coe MAlonzo.Code.Type.C_'8709'_4) (coe v9) (coe v11))))
                       (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_unwrap_'47'__534 v3 v4 v5 v8
        -> coe
             MAlonzo.Code.Algorithmic.C_unwrap_230 v3 v4 v5
             (coe
                du__'91'_'93''7473'_574
                (coe MAlonzo.Code.Type.BetaNormal.C_μ_24 v3 v4 v5) (coe v8)
                (coe v2))
      C_constr_558 v4 v5 v6 v8 v10 v12 v13 v14 v15 v16
        -> coe
             MAlonzo.Code.Algorithmic.C_constr_240 v8
             (coe
                MAlonzo.Code.Utils.List.du__'60''62''62'__42 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v6)))
             (coe
                MAlonzo.Code.Utils.List.du__'60''62''62'I__418 (coe v4) (coe v13)
                (coe
                   MAlonzo.Code.Utils.List.C__'8759'__314
                   (coe du__'91'_'93''7473'_574 (coe v5) (coe v16) (coe v2)) v15))
      C_case_568 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Algorithmic.C_case_252 v5 v6
             (coe
                du__'91'_'93''7473'_574
                (coe MAlonzo.Code.Type.BetaNormal.C_SOP_28 v5 v6) (coe v8)
                (coe v2))
             v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.ReductionEC.applyCase
d_applyCase_640 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
d_applyCase_640 ~v0 v1 v2 v3 = du_applyCase_640 v1 v2 v3
du_applyCase_640 ::
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178
du_applyCase_640 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Utils.List.C_'91''93'_308 -> coe v1
      MAlonzo.Code.Utils.List.C__'8759'__314 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    du_applyCase_640 (coe v8)
                    (coe MAlonzo.Code.Algorithmic.C__'183'__196 v7 v1 v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.ReductionEC._—→⋆_
d__'8212''8594''8902'__652 a0 a1 a2 = ()
data T__'8212''8594''8902'__652
  = C_β'45'ƛ_662 T_Value_28 | C_β'45'Λ_678 |
    C_β'45'wrap_694 T_Value_28 |
    C_β'45'builtin_720 Integer MAlonzo.Code.Builtin.T_Builtin_2
                       MAlonzo.Code.Utils.T__'8724'_'8803'__120 Integer
                       MAlonzo.Code.Utils.T__'8724'_'8803'__120
                       MAlonzo.Code.Builtin.Signature.T_SigTy_266 T_BApp_74 T_Value_28 |
    C_β'45'case_746 MAlonzo.Code.Utils.List.T_Bwd_6
                    MAlonzo.Code.Utils.List.T_IBwd_396
                    MAlonzo.Code.Utils.List.T_IIBwd_832
-- Algorithmic.ReductionEC._—→_
d__'8212''8594'__750 a0 a1 a2 = ()
data T__'8212''8594'__750
  = C_ruleEC_766 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                 MAlonzo.Code.Algorithmic.T__'8866'__178
                 MAlonzo.Code.Algorithmic.T__'8866'__178 T_EC_476
                 T__'8212''8594''8902'__652 |
    C_ruleErr_776 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                  T_EC_476
-- Algorithmic.ReductionEC._—↠_
d__'8212''8608'__780 a0 a1 a2 = ()
data T__'8212''8608'__780
  = C_refl'8212''8608'_786 |
    C_trans'8212''8608'_796 MAlonzo.Code.Algorithmic.T__'8866'__178
                            T__'8212''8594'__750 T__'8212''8608'__780
-- Algorithmic.ReductionEC.V-I
d_V'45'I_818 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 -> T_BApp_74 -> T_Value_28
d_V'45'I_818 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_V'45'I_818 v0 v2 v3 v4 v5 v6 v7 v8 v10
du_V'45'I_818 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  T_BApp_74 -> T_Value_28
du_V'45'I_818 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v2 of
      0 -> case coe v7 of
             MAlonzo.Code.Builtin.Signature.C__B'8658'__302 v17 v18 v19
               -> coe C_V'45'I'8658'_184 v0 v1 v3 v4 v5 v6 v19 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v9 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (case coe v7 of
                MAlonzo.Code.Builtin.Signature.C_sucΠ_326 v19 v20 v21
                  -> coe C_V'45'IΠ_208 v0 v1 v9 v3 v4 v5 v6 v21 v8
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Algorithmic.ReductionEC.ival
d_ival_838 :: MAlonzo.Code.Builtin.T_Builtin_2 -> T_Value_28
d_ival_838 v0
  = coe
      du_V'45'I_818 (coe v0) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Builtin.Signature.d_fv_96
         (coe MAlonzo.Code.Builtin.d_signature_298 (coe v0)))
      (coe MAlonzo.Code.Utils.C_start_124) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.List.Base.du_foldr_216
         (let v1 = \ v1 -> addInt (coe (1 :: Integer)) (coe v1) in
          coe (coe (\ v2 -> v1)))
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Data.List.NonEmpty.Base.d_tail_32
            (coe
               MAlonzo.Code.Builtin.Signature.d_args_86
               (coe MAlonzo.Code.Builtin.d_signature_298 (coe v0)))))
      (coe MAlonzo.Code.Utils.C_start_124)
      (coe
         MAlonzo.Code.Builtin.Signature.du_sig2SigTy_398
         (\ v1 v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v3)
         (coe
            (\ v1 v2 v3 v4 -> coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v4))
         (\ v1 v2 v3 v4 v5 ->
            coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v2 v4 v5)
         (coe (\ v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_'94'_12))
         (\ v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_con_22 v2)
         (\ v1 v2 v3 ->
            coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v2 v3)
         (\ v1 v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v2 v3)
         (coe MAlonzo.Code.Builtin.d_signature_298 (coe v0)))
      (coe C_base_78)
