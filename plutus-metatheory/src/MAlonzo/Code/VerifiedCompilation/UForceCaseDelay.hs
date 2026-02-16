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

module MAlonzo.Code.VerifiedCompilation.UForceCaseDelay where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation

-- VerifiedCompilation.UForceCaseDelay.FCD
d_FCD_14 a0 a1 a2 = ()
data T_FCD_14 = C_fcd_16
-- VerifiedCompilation.UForceCaseDelay.isFCD?
d_isFCD'63'_18 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
d_isFCD'63'_18 ~v0 ~v1 ~v2 = du_isFCD'63'_18
du_isFCD'63'_18 ::
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
du_isFCD'63'_18
  = coe
      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_92
      (coe C_fcd_16)
-- VerifiedCompilation.UForceCaseDelay.ForceCaseDelay
d_ForceCaseDelay_28 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_ForceCaseDelay_28 = erased
-- VerifiedCompilation.UForceCaseDelay.isForceCaseDelay?
d_isForceCaseDelay'63'_30 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_86
d_isForceCaseDelay'63'_30 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_164
      (coe v0)
      (coe
         MAlonzo.Code.VerifiedCompilation.Certificate.C_forceCaseDelayT_10)
      (\ v1 v2 v3 -> coe du_isFCD'63'_18)
