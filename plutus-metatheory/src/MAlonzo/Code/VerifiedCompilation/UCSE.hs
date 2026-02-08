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

module MAlonzo.Code.VerifiedCompilation.UCSE where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.RenamingSubstitution
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UCSE.UCSE
d_UCSE_4 a0 a1 a2 = ()
newtype T_UCSE_4
  = C_cse_14 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12
-- VerifiedCompilation.UCSE.UntypedCSE
d_UntypedCSE_22 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_UntypedCSE_22 = erased
-- VerifiedCompilation.UCSE.isUntypedCSE?
d_isUntypedCSE'63'_26 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
d_isUntypedCSE'63'_26 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_164
      (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_cseT_18)
      (coe d_isUCSE'63'_30)
-- VerifiedCompilation.UCSE.isUCSE?
d_isUCSE'63'_30 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
d_isUCSE'63'_30 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isApp'63'_166
              (coe v0)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isLambda'63'_70
                      (coe v3)
                      (\ v4 v5 ->
                         coe
                           MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)))
              (\ v3 v4 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_isTerm'63'_782)
              (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> case coe v6 of
                              MAlonzo.Code.VerifiedCompilation.UntypedViews.C_isapp_154 v9 v10
                                -> case coe v2 of
                                     MAlonzo.Code.Untyped.C__'183'__22 v11 v12
                                       -> case coe v9 of
                                            MAlonzo.Code.VerifiedCompilation.UntypedViews.C_islambda_62 v14
                                              -> case coe v11 of
                                                   MAlonzo.Code.Untyped.C_ƛ_20 v15
                                                     -> coe
                                                          seq (coe v14)
                                                          (coe
                                                             seq (coe v10)
                                                             (let v16
                                                                    = coe
                                                                        d_isUntypedCSE'63'_26 v0 v1
                                                                        (MAlonzo.Code.Untyped.RenamingSubstitution.d__'91'_'93'_468
                                                                           (coe v0) (coe v15)
                                                                           (coe v12)) in
                                                              coe
                                                                (case coe v16 of
                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_92 v17
                                                                     -> coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_92
                                                                          (coe C_cse_14 v17)
                                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100 v20 v21 v22
                                                                     -> coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                                                                          v20 v21 v22
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_100
                          (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_cseT_18) v1 v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCSE..extendedlambda0
d_'46'extendedlambda0_46 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_isApp_142 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_UCSE_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_46 = erased
-- VerifiedCompilation.UCSE..extendedlambda1
d_'46'extendedlambda1_78 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  () ->
  () ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_SimplifierTag_4 ->
  AgdaAny ->
  AgdaAny -> T_UCSE_4 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_78 = erased
