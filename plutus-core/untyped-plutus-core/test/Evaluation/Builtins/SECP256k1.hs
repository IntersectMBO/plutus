{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.SECP256k1 (secp256k1Prop) where

import Cardano.Crypto.DSIGN.Class (rawDeserialiseSigDSIGN, rawDeserialiseVerKeyDSIGN, rawSerialiseSigDSIGN,
                                   rawSerialiseVerKeyDSIGN)
import Cardano.Crypto.DSIGN.SECP256k1 (SECP256k1DSIGN, SigDSIGN (SigSECP256k1), VerKeyDSIGN (VerKeySECP256k1))
import Control.Lens.Extras (is)
import Control.Lens.Prism (Prism', prism')
import Crypto.Secp256k1 qualified as SECP
import Data.ByteString (ByteString)
import Data.Maybe (isNothing)
import Evaluation.Builtins.Common (typecheckEvaluateCek)
import Hedgehog (Gen, PropertyT, annotateShow, cover, failure, forAllWith, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore (DefaultFun (VerifySECP256k1Signature), EvaluationResult (EvaluationFailure, EvaluationSuccess),
                   defaultCekParameters)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterApp)
import Text.Show.Pretty (ppShow)

secp256k1Prop :: PropertyT IO ()
secp256k1Prop = do
  secpCase <- forAllWith ppShow genCase
  cover 14 "malformed pubkey" (is (_ShouldError . _BadPubKey) secpCase)
  cover 14 "malformed message" (is (_ShouldError . _BadMsg) secpCase)
  cover 14 "malformed signature" (is (_ShouldError . _BadSig) secpCase)
  cover 14 "mismatch of signing key and pubkey" (is (_Shouldn'tError . _WrongKey) secpCase)
  cover 14 "mismatch of message and signature" (is (_Shouldn'tError . _WrongSignature) secpCase)
  cover 14 "happy path" (is (_Shouldn'tError . _AllGood) secpCase)
  let actualExp = mkIterApp () (builtin () VerifySECP256k1Signature) [
        mkConstant @ByteString () . getPubKey $ secpCase,
        mkConstant @ByteString () . getSig $ secpCase,
        mkConstant @ByteString () . getMsg $ secpCase
        ]
  let result = typecheckEvaluateCek defaultCekParameters actualExp
  case result of
    Left x -> do
      annotateShow x
      failure
    Right (res, logs) -> do
      annotateShow logs
      res === (case secpCase of
        ShouldError{} -> EvaluationFailure
        Shouldn'tError good -> EvaluationSuccess . mkConstant () $ case good of
          AllGood{} -> True
          _         -> False)

-- All data needed for an erroring case
data SECP256k1ErrorCase =
  BadPubKey ByteString SECP.Msg SECP.Sig |
  BadMsg SECP.PubKey ByteString SECP.Sig |
  BadSig SECP.PubKey SECP.Msg ByteString
  deriving stock (Eq, Show)

_BadPubKey :: Prism' SECP256k1ErrorCase (ByteString, SECP.Msg, SECP.Sig)
_BadPubKey = prism' into outOf
  where
    into :: (ByteString, SECP.Msg, SECP.Sig) -> SECP256k1ErrorCase
    into (pk, msg, sig) = BadPubKey pk msg sig
    outOf :: SECP256k1ErrorCase -> Maybe (ByteString, SECP.Msg, SECP.Sig)
    outOf = \case
      BadPubKey pk msg sig -> pure (pk, msg, sig)
      _                    -> Nothing

_BadMsg :: Prism' SECP256k1ErrorCase (SECP.PubKey, ByteString, SECP.Sig)
_BadMsg = prism' into outOf
  where
    into :: (SECP.PubKey, ByteString, SECP.Sig) -> SECP256k1ErrorCase
    into (pk, msg, sig) = BadMsg pk msg sig
    outOf :: SECP256k1ErrorCase -> Maybe (SECP.PubKey, ByteString, SECP.Sig)
    outOf = \case
      BadMsg pk msg sig -> pure (pk, msg, sig)
      _                 -> Nothing

_BadSig :: Prism' SECP256k1ErrorCase (SECP.PubKey, SECP.Msg, ByteString)
_BadSig = prism' into outOf
  where
    into :: (SECP.PubKey, SECP.Msg, ByteString) -> SECP256k1ErrorCase
    into (pk, msg, sig) = BadSig pk msg sig
    outOf :: SECP256k1ErrorCase -> Maybe (SECP.PubKey, SECP.Msg, ByteString)
    outOf = \case
      BadSig pk msg sig -> pure (pk, msg, sig)
      _                 -> Nothing

genErrorCase :: Gen SECP256k1ErrorCase
genErrorCase = Gen.prune . Gen.choice $ [mkBadPubKey, mkBadMsg, mkBadSig]
  where
    mkBadPubKey :: Gen SECP256k1ErrorCase
    mkBadPubKey = do
      pkBad <- genPubKeyBad
      msg <- genMsg
      sig <- genSig
      pure . BadPubKey pkBad msg $ sig
    mkBadMsg :: Gen SECP256k1ErrorCase
    mkBadMsg = do
      sk <- genSecKey
      msg <- genMsg
      let sig = SECP.signMsg sk msg
      let pk = SECP.derivePubKey sk
      msgBad <- genMsgBad
      pure . BadMsg pk msgBad $ sig
    mkBadSig :: Gen SECP256k1ErrorCase
    mkBadSig = do
      pk <- genPubKey
      msg <- genMsg
      sigBad <- genSigBad
      pure . BadSig pk msg $ sigBad

-- All data needed for a successful case
data SECP256k1NoErrorCase =
  WrongKey SECP.PubKey SECP.Msg SECP.Sig |
  WrongSignature SECP.PubKey SECP.Msg SECP.Sig |
  AllGood SECP.PubKey SECP.Msg SECP.Sig
  deriving stock (Eq, Show)

_WrongKey :: Prism' SECP256k1NoErrorCase (SECP.PubKey, SECP.Msg, SECP.Sig)
_WrongKey = prism' into outOf
  where
    into :: (SECP.PubKey, SECP.Msg, SECP.Sig) ->
            SECP256k1NoErrorCase
    into (pk, msg, sig) = WrongKey pk msg sig
    outOf :: SECP256k1NoErrorCase -> Maybe (SECP.PubKey, SECP.Msg, SECP.Sig)
    outOf = \case
      WrongKey pk msg sig -> pure (pk, msg, sig)
      _                   -> Nothing

_WrongSignature :: Prism' SECP256k1NoErrorCase (SECP.PubKey, SECP.Msg, SECP.Sig)
_WrongSignature = prism' into outOf
  where
    into :: (SECP.PubKey, SECP.Msg, SECP.Sig) ->
            SECP256k1NoErrorCase
    into (pk, msg, sig) = WrongSignature pk msg sig
    outOf :: SECP256k1NoErrorCase -> Maybe (SECP.PubKey, SECP.Msg, SECP.Sig)
    outOf = \case
      WrongSignature pk msg sig -> pure (pk, msg, sig)
      _                         -> Nothing

_AllGood :: Prism' SECP256k1NoErrorCase (SECP.PubKey, SECP.Msg, SECP.Sig)
_AllGood = prism' into outOf
  where
    into :: (SECP.PubKey, SECP.Msg, SECP.Sig) ->
            SECP256k1NoErrorCase
    into (pk, msg, sig) = AllGood pk msg sig
    outOf :: SECP256k1NoErrorCase -> Maybe (SECP.PubKey, SECP.Msg, SECP.Sig)
    outOf = \case
      AllGood pk msg sig -> pure (pk, msg, sig)
      _                  -> Nothing

genNoErrorCase :: Gen SECP256k1NoErrorCase
genNoErrorCase = do
  sk <- genSecKey
  let pk = SECP.derivePubKey sk
  msg <- genMsg
  Gen.prune . Gen.choice $ [mkWrongKey sk pk msg,
                            mkWrongSignature sk pk msg,
                            mkAllGood sk pk msg]
  where
    mkWrongKey ::
      SECP.SecKey ->
      SECP.PubKey ->
      SECP.Msg ->
      Gen SECP256k1NoErrorCase
    mkWrongKey sk pk msg = do
      pkBad <- Gen.filter (/= pk) genPubKey
      let sig = SECP.signMsg sk msg
      pure . WrongKey pkBad msg $ sig
    mkWrongSignature ::
      SECP.SecKey ->
      SECP.PubKey ->
      SECP.Msg ->
      Gen SECP256k1NoErrorCase
    mkWrongSignature sk pk msg = do
      msgBad <- Gen.filter (/= msg) genMsg
      let sig = SECP.signMsg sk msgBad
      pure . WrongSignature pk msg $ sig
    mkAllGood ::
      SECP.SecKey ->
      SECP.PubKey ->
      SECP.Msg ->
      Gen SECP256k1NoErrorCase
    mkAllGood sk pk msg = do
      let sig = SECP.signMsg sk msg
      pure . AllGood pk msg $ sig

-- Case data, irrespective of form
data SECP256k1Case =
  ShouldError SECP256k1ErrorCase |
  Shouldn'tError SECP256k1NoErrorCase
  deriving stock (Eq, Show)

_ShouldError :: Prism' SECP256k1Case SECP256k1ErrorCase
_ShouldError = prism' into outOf
  where
    into :: SECP256k1ErrorCase -> SECP256k1Case
    into = ShouldError
    outOf :: SECP256k1Case -> Maybe SECP256k1ErrorCase
    outOf = \case
      ShouldError x -> pure x
      _             -> Nothing

_Shouldn'tError :: Prism' SECP256k1Case SECP256k1NoErrorCase
_Shouldn'tError = prism' into outOf
  where
    into :: SECP256k1NoErrorCase -> SECP256k1Case
    into = Shouldn'tError
    outOf :: SECP256k1Case -> Maybe SECP256k1NoErrorCase
    outOf = \case
      Shouldn'tError x -> pure x
      _                -> Nothing

getPubKey :: SECP256k1Case -> ByteString
getPubKey = \case
  ShouldError x -> case x of
    BadPubKey pk _ _ -> pk
    BadMsg pk _ _    -> go pk
    BadSig pk _ _    -> go pk
  Shouldn'tError x -> go $ case x of
    WrongKey pk _ _       -> pk
    WrongSignature pk _ _ -> pk
    AllGood pk _ _        -> pk
  where
    go :: SECP.PubKey -> ByteString
    go = rawSerialiseVerKeyDSIGN . VerKeySECP256k1

getMsg :: SECP256k1Case -> ByteString
getMsg = \case
  ShouldError x -> case x of
    BadPubKey _ msg _ -> SECP.getMsg msg
    BadMsg _ msg _    -> msg
    BadSig _ msg _    -> SECP.getMsg msg
  Shouldn'tError x -> SECP.getMsg $ case x of
    WrongKey _ msg _       -> msg
    WrongSignature _ msg _ -> msg
    AllGood _ msg _        -> msg

getSig :: SECP256k1Case -> ByteString
getSig = \case
  ShouldError x -> case x of
    BadPubKey _ _ sig -> go sig
    BadMsg _ _ sig    -> go sig
    BadSig _ _ sig    -> sig
  Shouldn'tError x -> go $ case x of
    WrongKey _ _ sig       -> sig
    WrongSignature _ _ sig -> sig
    AllGood _ _ sig        -> sig
  where
    go :: SECP.Sig -> ByteString
    go = rawSerialiseSigDSIGN . SigSECP256k1

genCase :: Gen SECP256k1Case
genCase = Gen.prune . Gen.choice $ [ShouldError <$> genErrorCase,
                                    Shouldn'tError <$> genNoErrorCase]

genMsg :: Gen SECP.Msg
genMsg = Gen.mapMaybe SECP.msg (Gen.bytes . Range.singleton $ 32)

genSecKey :: Gen SECP.SecKey
genSecKey = Gen.mapMaybe SECP.secKey (Gen.bytes . Range.singleton $ 32)

genPubKey :: Gen SECP.PubKey
genPubKey = SECP.derivePubKey <$> genSecKey

genPubKeyBad :: Gen ByteString
genPubKeyBad = Gen.filter (isNothing . rawDeserialiseVerKeyDSIGN @SECP256k1DSIGN)
                          (Gen.bytes . Range.linear 0 $ 64)

genSig :: Gen SECP.Sig
genSig = do
  sk <- genSecKey
  msg <- genMsg
  pure . SECP.signMsg sk $ msg

genMsgBad :: Gen ByteString
genMsgBad = Gen.filter (isNothing . SECP.msg) (Gen.bytes . Range.linear 0 $ 64)

genSigBad :: Gen ByteString
genSigBad = Gen.filter (isNothing . rawDeserialiseSigDSIGN @SECP256k1DSIGN)
                       (Gen.bytes . Range.linear 0 $ 64)
