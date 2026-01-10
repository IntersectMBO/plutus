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

module MAlonzo.Code.VerifiedCompilation.UInline where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Equality
import qualified MAlonzo.Code.Untyped.RenamingSubstitution
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UInline.pureInline
d_pureInline_4 a0 a1 a2 a3 = ()
data T_pureInline_4
  = C_tr_14 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 |
    C__'10814'__26 MAlonzo.Code.Untyped.T__'8866'_14 T_pureInline_4
                   T_pureInline_4 |
    C_inline_38 T_pureInline_4
-- VerifiedCompilation.UInline.Env
d_Env_46 a0 a1 = ()
data T_Env_46
  = C_'9633'_52 |
    C__'44'__54 T_Env_46 MAlonzo.Code.Untyped.T__'8866'_14
-- VerifiedCompilation.UInline.Inline
d_Inline_60 a0 a1 a2 a3 a4 = ()
data T_Inline_60
  = C_var_74 T_Inline_60 |
    C_last'45'sub_82 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 |
    C_sub_94 T_Inline_60
-- VerifiedCompilation.UInline.Inline→pureInline
d_Inline'8594'pureInline_114
  = error
      "MAlonzo Runtime Error: postulate evaluated: VerifiedCompilation.UInline.Inline\8594pureInline"
-- VerifiedCompilation.UInline.isInline?
d_isInline'63'_124 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_30
d_isInline'63'_124 ~v0 v1 = du_isInline'63'_124 v1
du_isInline'63'_124 ::
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_30
du_isInline'63'_124 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_178
      erased (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
      (coe (\ v1 v2 -> coe du_isIl'63'_136 (coe v2) (coe C_'9633'_52)))
-- VerifiedCompilation.UInline.isIl?
d_isIl'63'_136 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  T_Env_46 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_30
d_isIl'63'_136 ~v0 v1 v2 v3 v4 = du_isIl'63'_136 v1 v2 v3 v4
du_isIl'63'_136 ::
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  T_Env_46 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_30
du_isIl'63'_136 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
              erased
              (\ v4 v5 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
              (\ v4 v5 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
              (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> case coe v7 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v10 v11
                                -> case coe v2 of
                                     MAlonzo.Code.Untyped.C__'183'__22 v12 v13
                                       -> coe
                                            seq (coe v10)
                                            (coe
                                               seq (coe v11)
                                               (let v14
                                                      = coe
                                                          du_isIl'63'_136 (coe v0)
                                                          (coe C__'44'__54 (coe v1) (coe v13))
                                                          (coe v12) (coe v3) in
                                                coe
                                                  (case coe v14 of
                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_36 v15
                                                       -> coe
                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_36
                                                            (coe C_var_74 v15)
                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_44 v18 v19 v20
                                                       -> coe
                                                            MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_44
                                                            v18 v19 v20
                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v6)
                       (let v7
                              = coe
                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_70
                                  (\ v7 v8 ->
                                     coe
                                       MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
                                  (coe v2) in
                        coe
                          (case coe v7 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                               -> if coe v8
                                    then case coe v9 of
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                             -> case coe v10 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_62 v12
                                                    -> case coe v2 of
                                                         MAlonzo.Code.Untyped.C_ƛ_20 v13
                                                           -> coe
                                                                seq (coe v12)
                                                                (case coe v1 of
                                                                   C_'9633'_52
                                                                     -> coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_44
                                                                          (coe
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
                                                                          v2 v3
                                                                   C__'44'__54 v14 v15
                                                                     -> case coe v14 of
                                                                          C_'9633'_52
                                                                            -> let v16
                                                                                     = coe
                                                                                         du_isInline'63'_124
                                                                                         v0
                                                                                         (coe
                                                                                            MAlonzo.Code.Untyped.RenamingSubstitution.du__'91'_'93'_468
                                                                                            (coe
                                                                                               v13)
                                                                                            (coe
                                                                                               v15))
                                                                                         v3 in
                                                                               coe
                                                                                 (case coe v16 of
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_36 v17
                                                                                      -> coe
                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_36
                                                                                           (coe
                                                                                              C_last'45'sub_82
                                                                                              v17)
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_44 v20 v21 v22
                                                                                      -> coe
                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_44
                                                                                           v20 v21
                                                                                           v22
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          C__'44'__54 v16 v17
                                                                            -> let v18
                                                                                     = coe
                                                                                         du_isIl'63'_136
                                                                                         (coe v0)
                                                                                         (coe v14)
                                                                                         (coe
                                                                                            MAlonzo.Code.Untyped.RenamingSubstitution.du__'91'_'93'_468
                                                                                            (coe
                                                                                               v13)
                                                                                            (coe
                                                                                               v15))
                                                                                         (coe v3) in
                                                                               coe
                                                                                 (case coe v18 of
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_36 v19
                                                                                      -> coe
                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_36
                                                                                           (coe
                                                                                              C_sub_94
                                                                                              v19)
                                                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_44 v22 v23 v24
                                                                                      -> coe
                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_44
                                                                                           v22 v23
                                                                                           v24
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    else coe
                                           seq (coe v9)
                                           (coe
                                              seq (coe v1)
                                              (coe
                                                 MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_44
                                                 (coe
                                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
                                                 v2 v3))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UInline..extendedlambda0
d_'46'extendedlambda0_192 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  T_Env_46 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_Inline_60 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  T_Inline_60 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_192 = erased
-- VerifiedCompilation.UInline..extendedlambda1
d_'46'extendedlambda1_216 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isLambda_54 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_Inline_60 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_216 = erased
-- VerifiedCompilation.UInline..extendedlambda2
d_'46'extendedlambda2_232 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isLambda_54 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  T_Env_46 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_Inline_60 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda2_232 = erased
-- VerifiedCompilation.UInline..extendedlambda3
d_'46'extendedlambda3_246 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_Inline_60 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda3_246 = erased
-- VerifiedCompilation.UInline..extendedlambda4
d_'46'extendedlambda4_292 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Inline_60 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda4_292 = erased
-- VerifiedCompilation.UInline..extendedlambda5
d_'46'extendedlambda5_346 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  T_Env_46 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (T_Inline_60 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Inline_60 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda5_346 = erased
-- VerifiedCompilation.UInline.UInline
d_UInline_358 ::
  () ->
  MAlonzo.Code.Untyped.Equality.T_DecEq_6 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_UInline_358 = erased
