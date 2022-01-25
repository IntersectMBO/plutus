{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.SECP256k1 (secp256k1Prop) where

import Control.Lens.Extras (is)
import Control.Lens.Prism (Prism', prism')
import Crypto.Secp256k1 qualified as SECP
import Data.ByteString (ByteString)
import Data.Maybe (isNothing)
import Evaluation.Builtins.Common (typecheckEvaluateCekNoEmit)
import Hedgehog (Gen, PropertyT, cover, forAllWith, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore (DefaultFun (VerifySECP256k1Signature), EvaluationResult (EvaluationFailure, EvaluationSuccess),
                   defaultCekParameters)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterApp)
import Text.Show.Pretty (ppShow)

secp256k1Prop :: PropertyT IO ()
secp256k1Prop = do
  secpCase <- forAllWith ppShow genCase
  cover 15 "malformed pubkey" (is (_ShouldError . _BadPubKey) secpCase)
  cover 15 "malformed message" (is (_ShouldError . _BadMsg) secpCase)
  cover 15 "malformed signature" (is (_ShouldError . _BadSig) secpCase)
  cover 15 "mismatch of signing key and pubkey" (is (_Shouldn'tError . _WrongKey) secpCase)
  cover 15 "mismatch of message and signature" (is (_Shouldn'tError . _WrongSignature) secpCase)
  cover 15 "happy path" (is (_Shouldn'tError . _AllGood) secpCase)
  let actualExp = mkIterApp () (builtin () VerifySECP256k1Signature) [
        mkConstant @ByteString () . getPubKey $ secpCase,
        mkConstant @ByteString () . getSig $ secpCase,
        mkConstant @ByteString () . getMsg $ secpCase
        ]
  let result = typecheckEvaluateCekNoEmit defaultCekParameters actualExp
  result === (Right $ case secpCase of
    ShouldError{} -> EvaluationFailure
    Shouldn'tError good -> EvaluationSuccess . mkConstant () $ case good of
      AllGood{} -> True
      _         -> False)

-- All data needed for an erroring case
data SECP256k1ErrorCase =
  BadPubKey ByteString ByteString ByteString |
  BadMsg ByteString ByteString ByteString |
  BadSig ByteString ByteString ByteString
  deriving stock (Eq, Show)

_BadPubKey :: Prism' SECP256k1ErrorCase (ByteString, ByteString, ByteString)
_BadPubKey = prism' into outOf
  where
    into :: (ByteString, ByteString, ByteString) -> SECP256k1ErrorCase
    into (pk, msg, sig) = BadPubKey pk msg sig
    outOf :: SECP256k1ErrorCase -> Maybe (ByteString, ByteString, ByteString)
    outOf = \case
      BadPubKey pk msg sig -> pure (pk, msg, sig)
      _                    -> Nothing

_BadMsg :: Prism' SECP256k1ErrorCase (ByteString, ByteString, ByteString)
_BadMsg = prism' into outOf
  where
    into :: (ByteString, ByteString, ByteString) -> SECP256k1ErrorCase
    into (pk, msg, sig) = BadMsg pk msg sig
    outOf :: SECP256k1ErrorCase -> Maybe (ByteString, ByteString, ByteString)
    outOf = \case
      BadMsg pk msg sig -> pure (pk, msg, sig)
      _                 -> Nothing

_BadSig :: Prism' SECP256k1ErrorCase (ByteString, ByteString, ByteString)
_BadSig = prism' into outOf
  where
    into :: (ByteString, ByteString, ByteString) -> SECP256k1ErrorCase
    into (pk, msg, sig) = BadSig pk msg sig
    outOf :: SECP256k1ErrorCase -> Maybe (ByteString, ByteString, ByteString)
    outOf = \case
      BadSig pk msg sig -> pure (pk, msg, sig)
      _                 -> Nothing

genErrorCase :: Gen SECP256k1ErrorCase
genErrorCase = Gen.prune . Gen.choice $ [mkBadPubKey, mkBadMsg, mkBadSig]
  where
    mkBadPubKey :: Gen SECP256k1ErrorCase
    mkBadPubKey = do
      pk <- genBadPubKey
      msg <- genGoodMsg
      sig <- genGoodSig
      pure . BadPubKey pk msg $ sig
    mkBadMsg :: Gen SECP256k1ErrorCase
    mkBadMsg = do
      pk <- genGoodPubKey
      msg <- genBadMsg
      sig <- genGoodSig
      pure . BadMsg pk msg $ sig
    mkBadSig :: Gen SECP256k1ErrorCase
    mkBadSig = do
      pk <- genGoodPubKey
      msg <- genGoodMsg
      sig <- genBadSig
      pure . BadSig pk msg $ sig
    genGoodMsg :: Gen ByteString
    genGoodMsg = SECP.getMsg <$> genMsg
    genBadMsg :: Gen ByteString
    genBadMsg = Gen.filter (isNothing . SECP.msg) (Gen.bytes . Range.linear 0 $ 64)
    genBadPubKey :: Gen ByteString
    genBadPubKey = Gen.filter (isNothing . SECP.importPubKey) (Gen.bytes . Range.linear 0 $ 64)
    genGoodSig :: Gen ByteString
    genGoodSig = do
      sk <- genSecKey
      msg <- genMsg
      pure . SECP.exportSig . SECP.signMsg sk $ msg
    genBadSig :: Gen ByteString
    genBadSig = Gen.filter (isNothing . SECP.importSig) (Gen.bytes . Range.linear 0 $ 64)

-- All data needed for a successful case
data SECP256k1NoErrorCase =
  WrongKey ByteString ByteString ByteString |
  WrongSignature ByteString ByteString ByteString |
  AllGood ByteString ByteString ByteString
  deriving stock (Eq, Show)

_WrongKey :: Prism' SECP256k1NoErrorCase (ByteString, ByteString, ByteString)
_WrongKey = prism' into outOf
  where
    into :: (ByteString, ByteString, ByteString) ->
            SECP256k1NoErrorCase
    into (pk, msg, sig) = WrongKey pk msg sig
    outOf :: SECP256k1NoErrorCase -> Maybe (ByteString, ByteString, ByteString)
    outOf = \case
      WrongKey pk msg sig -> pure (pk, msg, sig)
      _                   -> Nothing

_WrongSignature :: Prism' SECP256k1NoErrorCase (ByteString, ByteString, ByteString)
_WrongSignature = prism' into outOf
  where
    into :: (ByteString, ByteString, ByteString) ->
            SECP256k1NoErrorCase
    into (pk, msg, sig) = WrongSignature pk msg sig
    outOf :: SECP256k1NoErrorCase -> Maybe (ByteString, ByteString, ByteString)
    outOf = \case
      WrongSignature pk msg sig -> pure (pk, msg, sig)
      _                         -> Nothing

_AllGood :: Prism' SECP256k1NoErrorCase (ByteString, ByteString, ByteString)
_AllGood = prism' into outOf
  where
    into :: (ByteString, ByteString, ByteString) ->
            SECP256k1NoErrorCase
    into (pk, msg, sig) = AllGood pk msg sig
    outOf :: SECP256k1NoErrorCase -> Maybe (ByteString, ByteString, ByteString)
    outOf = \case
      AllGood pk msg sig -> pure (pk, msg, sig)
      _                  -> Nothing

genNoErrorCase :: Gen SECP256k1NoErrorCase
genNoErrorCase = Gen.prune . Gen.choice $ [mkWrongKey, mkWrongSignature, mkAllGood]
  where
    mkWrongKey :: Gen SECP256k1NoErrorCase
    mkWrongKey = do
      sk <- genSecKey
      let pk = SECP.derivePubKey sk
      msg <- genMsg
      let sig = SECP.signMsg sk msg
      let pkBS = SECP.exportPubKey True pk
      pkBS' <- Gen.filter (/= pkBS) genGoodPubKey
      pure . WrongKey pkBS' (SECP.getMsg msg) . SECP.exportSig $ sig
    mkWrongSignature :: Gen SECP256k1NoErrorCase
    mkWrongSignature = do
      sk <- genSecKey
      let pk = SECP.derivePubKey sk
      msg <- genMsg
      msg' <- Gen.filter (/= msg) genMsg
      let sig = SECP.signMsg sk msg'
      let pkBS = SECP.exportPubKey True pk
      pure . WrongSignature pkBS (SECP.getMsg msg) . SECP.exportSig $ sig
    mkAllGood :: Gen SECP256k1NoErrorCase
    mkAllGood = do
      sk <- genSecKey
      let pk = SECP.derivePubKey sk
      msg <- genMsg
      let sig = SECP.signMsg sk msg
      let pkBS = SECP.exportPubKey True pk
      pure . AllGood pkBS (SECP.getMsg msg) . SECP.exportSig $ sig

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
    BadMsg pk _ _    -> pk
    BadSig pk _ _    -> pk
  Shouldn'tError x -> case x of
    WrongKey pk _ _       -> pk
    WrongSignature pk _ _ -> pk
    AllGood pk _ _        -> pk

getMsg :: SECP256k1Case -> ByteString
getMsg = \case
  ShouldError x -> case x of
    BadPubKey _ msg _ -> msg
    BadMsg _ msg _    -> msg
    BadSig _ msg _    -> msg
  Shouldn'tError x -> case x of
    WrongKey _ msg _       -> msg
    WrongSignature _ msg _ -> msg
    AllGood _ msg _        -> msg

getSig :: SECP256k1Case -> ByteString
getSig = \case
  ShouldError x -> case x of
    BadPubKey _ _ sig -> sig
    BadMsg _ _ sig    -> sig
    BadSig _ _ sig    -> sig
  Shouldn'tError x -> case x of
    WrongKey _ _ sig       -> sig
    WrongSignature _ _ sig -> sig
    AllGood _ _ sig        -> sig

genCase :: Gen SECP256k1Case
genCase = Gen.prune . Gen.choice $ [ShouldError <$> genErrorCase,
                                    Shouldn'tError <$> genNoErrorCase]

genGoodPubKey :: Gen ByteString
genGoodPubKey = Gen.mapMaybe (fmap (SECP.exportPubKey True . SECP.derivePubKey) . SECP.secKey)
                             (Gen.bytes . Range.singleton $ 32)

genMsg :: Gen SECP.Msg
genMsg = Gen.mapMaybe SECP.msg (Gen.bytes . Range.singleton $ 32)

genSecKey :: Gen SECP.SecKey
genSecKey = Gen.mapMaybe SECP.secKey (Gen.bytes . Range.singleton $ 32)
