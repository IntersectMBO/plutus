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

module MAlonzo.Code.VerifiedCompilation.NotImplemented where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.VerifiedCompilation.Certificate

-- VerifiedCompilation.NotImplemented.Policy
d_Policy_4 = ()
data T_Policy_4 = C_accept_6 | C_reject_8
-- VerifiedCompilation.NotImplemented.NotImplemented
d_NotImplemented_12 a0 a1 a2 a3 = ()
data T_NotImplemented_12 = C_notImplemented_20
-- VerifiedCompilation.NotImplemented.certNotImplemented
d_certNotImplemented_22 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_12
d_certNotImplemented_22 ~v0 ~v1 = du_certNotImplemented_22
du_certNotImplemented_22 ::
  MAlonzo.Code.VerifiedCompilation.Certificate.T_CertResult_12
du_certNotImplemented_22
  = coe
      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_18
      (coe C_notImplemented_20)
