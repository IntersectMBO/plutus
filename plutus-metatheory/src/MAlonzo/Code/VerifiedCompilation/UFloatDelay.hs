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

module MAlonzo.Code.VerifiedCompilation.UFloatDelay where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Purity
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UFloatDelay.subs-delay
d_subs'45'delay_18 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_subs'45'delay_18 ~v0 v1 v2 = du_subs'45'delay_18 v1 v2
du_subs'45'delay_18 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_subs'45'delay_18 v0 v1
  = case coe v1 of
      MAlonzo.Code.Untyped.C_'96'_18 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.Fin.Properties.du__'8799'__50 (coe v0)
                     (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then coe
                              seq (coe v5)
                              (coe
                                 MAlonzo.Code.Untyped.C_delay_26
                                 (coe MAlonzo.Code.Untyped.C_'96'_18 (coe v0)))
                       else coe seq (coe v5) (coe v1)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_ƛ_20 v2
        -> coe
             MAlonzo.Code.Untyped.C_ƛ_20
             (coe
                du_subs'45'delay_18 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v0)
                (coe v2))
      MAlonzo.Code.Untyped.C__'183'__22 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22
             (coe du_subs'45'delay_18 (coe v0) (coe v2))
             (coe du_subs'45'delay_18 (coe v0) (coe v3))
      MAlonzo.Code.Untyped.C_force_24 v2
        -> coe
             MAlonzo.Code.Untyped.C_force_24
             (coe du_subs'45'delay_18 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_delay_26 v2
        -> coe
             MAlonzo.Code.Untyped.C_delay_26
             (coe du_subs'45'delay_18 (coe v0) (coe v2))
      MAlonzo.Code.Untyped.C_con_28 v2 -> coe v1
      MAlonzo.Code.Untyped.C_constr_34 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C_constr_34 (coe v2)
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe du_subs'45'delay_18 (coe v0)) (coe v3))
      MAlonzo.Code.Untyped.C_case_40 v2 v3
        -> coe
             MAlonzo.Code.Untyped.C_case_40
             (coe du_subs'45'delay_18 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe du_subs'45'delay_18 (coe v0)) (coe v3))
      MAlonzo.Code.Untyped.C_builtin_44 v2 -> coe v1
      MAlonzo.Code.Untyped.C_error_46 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UFloatDelay.FlD
d_FlD_78 a0 a1 a2 = ()
data T_FlD_78
  = C_floatdelay_90 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8
                    MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8
                    MAlonzo.Code.Untyped.Purity.T_Pure_6
-- VerifiedCompilation.UFloatDelay.FloatDelay
d_FloatDelay_98 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_FloatDelay_98 = erased
-- VerifiedCompilation.UFloatDelay.isFloatDelay?
d_isFloatDelay'63'_102 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_isFloatDelay'63'_102 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_160
      (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Trace.d_FloatDelayT_32)
      (coe d_isFlD'63'_106)
-- VerifiedCompilation.UFloatDelay.isFlD?
d_isFlD'63'_106 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_isFlD'63'_106 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_168
              (coe v0)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_72
                      (coe v3)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_784)))
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isDelay'63'_372
                      (coe v3)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_784)))
              (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_156 v9 v10
                                -> case coe v1 of
                                     MAlonzo.Code.Untyped.C__'183'__22 v11 v12
                                       -> case coe v9 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_64 v14
                                              -> case coe v11 of
                                                   MAlonzo.Code.Untyped.C_ƛ_20 v15
                                                     -> coe
                                                          seq (coe v14)
                                                          (case coe v10 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isdelay_364 v17
                                                               -> case coe v12 of
                                                                    MAlonzo.Code.Untyped.C_delay_26 v18
                                                                      -> coe
                                                                           seq (coe v17)
                                                                           (let v19
                                                                                  = coe
                                                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_168
                                                                                      (coe v0)
                                                                                      (coe
                                                                                         (\ v19 ->
                                                                                            coe
                                                                                              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_72
                                                                                              (coe
                                                                                                 v19)
                                                                                              (\ v20
                                                                                                 v21 ->
                                                                                                 coe
                                                                                                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_784)))
                                                                                      (\ v19 v20 ->
                                                                                         coe
                                                                                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_784)
                                                                                      (coe v2) in
                                                                            coe
                                                                              (case coe v19 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                   -> if coe v20
                                                                                        then case coe
                                                                                                    v21 of
                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                                                                 -> case coe
                                                                                                           v22 of
                                                                                                      MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_156 v25 v26
                                                                                                        -> case coe
                                                                                                                  v2 of
                                                                                                             MAlonzo.Code.Untyped.C__'183'__22 v27 v28
                                                                                                               -> case coe
                                                                                                                         v25 of
                                                                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_64 v30
                                                                                                                      -> case coe
                                                                                                                                v27 of
                                                                                                                           MAlonzo.Code.Untyped.C_ƛ_20 v31
                                                                                                                             -> coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v30)
                                                                                                                                  (coe
                                                                                                                                     seq
                                                                                                                                     (coe
                                                                                                                                        v26)
                                                                                                                                     (let v32
                                                                                                                                            = coe
                                                                                                                                                d_isFloatDelay'63'_102
                                                                                                                                                (addInt
                                                                                                                                                   (coe
                                                                                                                                                      (1 ::
                                                                                                                                                         Integer))
                                                                                                                                                   (coe
                                                                                                                                                      v0))
                                                                                                                                                (coe
                                                                                                                                                   du_subs'45'delay_18
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                                                                                                                   (coe
                                                                                                                                                      v15))
                                                                                                                                                v31 in
                                                                                                                                      coe
                                                                                                                                        (case coe
                                                                                                                                                v32 of
                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v33
                                                                                                                                             -> let v34
                                                                                                                                                      = coe
                                                                                                                                                          d_isFloatDelay'63'_102
                                                                                                                                                          v0
                                                                                                                                                          v18
                                                                                                                                                          v28 in
                                                                                                                                                coe
                                                                                                                                                  (case coe
                                                                                                                                                          v34 of
                                                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 v35
                                                                                                                                                       -> let v36
                                                                                                                                                                = MAlonzo.Code.Untyped.Purity.d_isPure'63'_72
                                                                                                                                                                    (coe
                                                                                                                                                                       v0)
                                                                                                                                                                    (coe
                                                                                                                                                                       v28) in
                                                                                                                                                          coe
                                                                                                                                                            (case coe
                                                                                                                                                                    v36 of
                                                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v37 v38
                                                                                                                                                                 -> if coe
                                                                                                                                                                         v37
                                                                                                                                                                      then case coe
                                                                                                                                                                                  v38 of
                                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v39
                                                                                                                                                                               -> coe
                                                                                                                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44
                                                                                                                                                                                    (coe
                                                                                                                                                                                       C_floatdelay_90
                                                                                                                                                                                       v33
                                                                                                                                                                                       v35
                                                                                                                                                                                       v39)
                                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                      else coe
                                                                                                                                                                             seq
                                                                                                                                                                             (coe
                                                                                                                                                                                v38)
                                                                                                                                                                             (coe
                                                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                                                                                MAlonzo.Code.VerifiedCompilation.Trace.d_FloatDelayT_32
                                                                                                                                                                                v1
                                                                                                                                                                                v2)
                                                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v38 v39 v40
                                                                                                                                                       -> coe
                                                                                                                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                                                            v38
                                                                                                                                                            v39
                                                                                                                                                            v40
                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52 v36 v37 v38
                                                                                                                                             -> coe
                                                                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                                                                  v36
                                                                                                                                                  v37
                                                                                                                                                  v38
                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        else coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v21)
                                                                                               (coe
                                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                                                                                  MAlonzo.Code.VerifiedCompilation.Trace.d_FloatDelayT_32
                                                                                                  v1
                                                                                                  v2)
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                          MAlonzo.Code.VerifiedCompilation.Trace.d_FloatDelayT_32 v1 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UFloatDelay..extendedlambda0
d_'46'extendedlambda0_122 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_144 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FlD_78 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_122 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda1
d_'46'extendedlambda1_152 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_144 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FlD_78 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_152 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda2
d_'46'extendedlambda2_196 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_FlD_78 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda2_196 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda3
d_'46'extendedlambda3_244 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.VerifiedCompilation.Trace.T_UncertifiedOptTag_4
    MAlonzo.Code.VerifiedCompilation.Trace.T_CertifiedOptTag_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
  T_FlD_78 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda3_244 = erased
-- VerifiedCompilation.UFloatDelay..extendedlambda4
d_'46'extendedlambda4_290 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.Untyped.Purity.T_Pure_6 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8 ->
  T_FlD_78 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda4_290 = erased
