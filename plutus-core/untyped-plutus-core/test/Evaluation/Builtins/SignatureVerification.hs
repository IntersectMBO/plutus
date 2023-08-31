-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Evaluation.Builtins.SignatureVerification (
  ecdsaSecp256k1Prop,
  ed25519_Variant1Prop,
  ed25519_Variant2Prop,
  schnorrSecp256k1Prop,
  ) where


import Cardano.Crypto.DSIGN.Class (ContextDSIGN, DSIGNAlgorithm, SignKeyDSIGN, Signable,
                                   deriveVerKeyDSIGN, genKeyDSIGN, rawDeserialiseSigDSIGN,
                                   rawDeserialiseVerKeyDSIGN, rawSerialiseSigDSIGN,
                                   rawSerialiseVerKeyDSIGN, signDSIGN)
import Cardano.Crypto.DSIGN.EcdsaSecp256k1 (EcdsaSecp256k1DSIGN, MessageHash, SigDSIGN, VerKeyDSIGN,
                                            fromMessageHash, toMessageHash)
import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Cardano.Crypto.DSIGN.SchnorrSecp256k1 (SchnorrSecp256k1DSIGN)
import Cardano.Crypto.Seed (mkSeedFromBytes)
import Control.Lens.Extras (is)
import Control.Lens.Fold (preview)
import Control.Lens.Prism (Prism', prism')
import Control.Lens.Review (review)
import Data.ByteString (ByteString)
import Data.Kind (Type)
import Evaluation.Builtins.Common (typecheckEvaluateCek)
import Hedgehog (Gen, PropertyT, annotateShow, cover, failure, forAllWith, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore (DefaultFun (VerifyEcdsaSecp256k1Signature, VerifyEd25519Signature, VerifySchnorrSecp256k1Signature),
                   EvaluationResult (EvaluationFailure, EvaluationSuccess))
import PlutusCore.Default as Plutus (BuiltinSemanticsVariant (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults

import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusPrelude
import Text.Show.Pretty (ppShow)

ecdsaSecp256k1Prop :: PropertyT IO ()
ecdsaSecp256k1Prop = do
  testCase <- forAllWith ppShow genEcdsaCase
  cover 14 "malformed verification key" . is (_ShouldError . _BadVerKey) $ testCase
  cover 14 "malformed message" . is (_ShouldError . _BadMessage) $ testCase
  cover 14 "malformed signature" . is (_ShouldError . _BadSignature) $ testCase
  cover 14 "mismatch of signing key and verification key" . is (_Shouldn'tError . _WrongVerKey) $ testCase
  cover 14 "mismatch of message and signature" . is (_Shouldn'tError . _WrongSignature) $ testCase
  cover 14 "happy path" . is (_Shouldn'tError . _AllGood) $ testCase
  runTestDataWith def testCase fromMessageHash VerifyEcdsaSecp256k1Signature

schnorrSecp256k1Prop :: PropertyT IO ()
schnorrSecp256k1Prop = do
  testCase <- forAllWith ppShow genSchnorrCase
  cover 18 "malformed verification key" . is (_ShouldError . _BadVerKey) $ testCase
  cover 18 "malformed signature" . is (_ShouldError . _BadSignature) $ testCase
  cover 18 "mismatch of signing key and verification key" . is (_Shouldn'tError . _WrongVerKey) $ testCase
  cover 18 "mismatch of message and signature" . is (_Shouldn'tError . _WrongSignature) $ testCase
  cover 18 "happy path" . is (_Shouldn'tError . _AllGood) $ testCase
  runTestDataWith def testCase id VerifySchnorrSecp256k1Signature

ed25519Prop :: BuiltinSemanticsVariant DefaultFun -> PropertyT IO ()
ed25519Prop semvar = do
  testCase <- forAllWith ppShow genEd25519Case
  cover 18 "malformed verification key" . is (_ShouldError . _BadVerKey) $ testCase
  cover 18 "malformed signature" . is (_ShouldError . _BadSignature) $ testCase
  cover 18 "mismatch of signing key and verification key" . is (_Shouldn'tError . _WrongVerKey) $ testCase
  cover 18 "mismatch of message and signature" . is (_Shouldn'tError . _WrongSignature) $ testCase
  cover 18 "happy path" . is (_Shouldn'tError . _AllGood) $ testCase
  runTestDataWith semvar testCase id VerifyEd25519Signature

ed25519_Variant1Prop :: PropertyT IO ()
ed25519_Variant1Prop = ed25519Prop DefaultFunSemanticsVariant1

ed25519_Variant2Prop :: PropertyT IO ()
ed25519_Variant2Prop = ed25519Prop DefaultFunSemanticsVariant2

-- Helpers

runTestDataWith :: forall (a :: Type) (msg :: Type) .
  (DSIGNAlgorithm a) =>
  BuiltinSemanticsVariant DefaultFun ->
  Case a msg ->
  (msg -> ByteString) ->
  DefaultFun ->
  PropertyT IO ()
runTestDataWith semvar testData f op = do
  let (vk, msg, sig) = getCaseData f testData
  let actualExp = mkIterAppNoAnn (builtin () op) [
        mkConstant @ByteString () vk,
        mkConstant @ByteString () msg,
        mkConstant @ByteString () sig
        ]
  let result = typecheckEvaluateCek semvar defaultBuiltinCostModel actualExp
  case result of
    Left x -> annotateShow x >> failure
    Right (res, logs) -> do
      annotateShow logs
      case preview _Shouldn'tError testData of
        Nothing -> res === EvaluationFailure
        Just good -> case preview _AllGood good of
          Nothing -> res === (EvaluationSuccess . mkConstant () $ False)
          Just _  -> res === (EvaluationSuccess . mkConstant () $ True)

-- Data for an erroring case
data ErrorCase (a :: Type) (msg :: Type) where
  BadVerKey :: ByteString -> msg -> SigDSIGN a -> ErrorCase a msg
  BadMsg :: VerKeyDSIGN a -> ByteString -> SigDSIGN a -> ErrorCase a msg
  BadSig :: VerKeyDSIGN a -> msg -> ByteString -> ErrorCase a msg

deriving stock instance (Eq msg, DSIGNAlgorithm a) => Eq (ErrorCase a msg)

deriving stock instance (Show msg, DSIGNAlgorithm a) => Show (ErrorCase a msg)

_BadVerKey :: forall (a :: Type) (msg :: Type) .
  Prism' (ErrorCase a msg) (ByteString, msg, SigDSIGN a)
_BadVerKey = prism' into outOf
  where
    into :: (ByteString, msg, SigDSIGN a) -> ErrorCase a msg
    into (bs, message, sig) = BadVerKey bs message sig
    outOf :: ErrorCase a msg -> Maybe (ByteString, msg, SigDSIGN a)
    outOf = \case
      BadVerKey bs message sig -> pure (bs, message, sig)
      _                        -> Nothing

_BadMessage :: forall (a :: Type) (msg :: Type) .
  Prism' (ErrorCase a msg) (VerKeyDSIGN a, ByteString, SigDSIGN a)
_BadMessage = prism' into outOf
  where
    into :: (VerKeyDSIGN a, ByteString, SigDSIGN a) -> ErrorCase a msg
    into (vk, bs, sig) = BadMsg vk bs sig
    outOf :: ErrorCase a msg -> Maybe (VerKeyDSIGN a, ByteString, SigDSIGN a)
    outOf = \case
      BadMsg vk bs sig -> pure (vk, bs, sig)
      _                -> Nothing

_BadSignature :: forall (a :: Type) (msg :: Type) .
  Prism' (ErrorCase a msg) (VerKeyDSIGN a, msg, ByteString)
_BadSignature = prism' into outOf
  where
    into :: (VerKeyDSIGN a, msg, ByteString) -> ErrorCase a msg
    into (vk, message, sig) = BadSig vk message sig
    outOf :: ErrorCase a msg -> Maybe (VerKeyDSIGN a, msg, ByteString)
    outOf = \case
      BadSig vk message bs -> pure (vk, message, bs)
      _                    -> Nothing

-- Data for non-erroring case
data NoErrorCase (a :: Type) (msg :: Type) where
  WrongVerKey :: VerKeyDSIGN a -> msg -> SigDSIGN a -> NoErrorCase a msg
  WrongSignature :: VerKeyDSIGN a -> msg -> SigDSIGN a -> NoErrorCase a msg
  AllGood :: VerKeyDSIGN a -> msg -> SigDSIGN a -> NoErrorCase a msg

deriving stock instance (Eq msg, DSIGNAlgorithm a) => Eq (NoErrorCase a msg)

deriving stock instance (Show msg, DSIGNAlgorithm a) => Show (NoErrorCase a msg)

_WrongVerKey :: forall (a :: Type) (msg :: Type) .
  Prism' (NoErrorCase a msg) (VerKeyDSIGN a, msg, SigDSIGN a)
_WrongVerKey = prism' into outOf
  where
    into :: (VerKeyDSIGN a, msg, SigDSIGN a) -> NoErrorCase a msg
    into (vk, message, sig) = WrongVerKey vk message sig
    outOf :: NoErrorCase a msg -> Maybe (VerKeyDSIGN a, msg, SigDSIGN a)
    outOf = \case
      WrongVerKey vk message sig -> pure (vk, message, sig)
      _                          -> Nothing

_WrongSignature :: forall (a :: Type) (msg :: Type) .
  Prism' (NoErrorCase a msg) (VerKeyDSIGN a, msg, SigDSIGN a)
_WrongSignature = prism' into outOf
  where
    into :: (VerKeyDSIGN a, msg, SigDSIGN a) -> NoErrorCase a msg
    into (vk, message, sig) = WrongSignature vk message sig
    outOf :: NoErrorCase a msg -> Maybe (VerKeyDSIGN a, msg, SigDSIGN a)
    outOf = \case
      WrongSignature vk message sig -> pure (vk, message, sig)
      _                             -> Nothing

_AllGood :: forall (a :: Type) (msg :: Type) .
  Prism' (NoErrorCase a msg) (VerKeyDSIGN a, msg, SigDSIGN a)
_AllGood = prism' into outOf
  where
    into :: (VerKeyDSIGN a, msg, SigDSIGN a) -> NoErrorCase a msg
    into (vk, message, sig) = AllGood vk message sig
    outOf :: NoErrorCase a msg -> Maybe (VerKeyDSIGN a, msg, SigDSIGN a)
    outOf = \case
      AllGood vk message sig -> pure (vk, message, sig)
      _                      -> Nothing

-- Case, irrespective of form
data Case (a :: Type) (msg :: Type) where
  ShouldError :: ErrorCase a msg -> Case a msg
  Shouldn'tError :: NoErrorCase a msg -> Case a msg

deriving stock instance (DSIGNAlgorithm a, Eq msg) => Eq (Case a msg)

deriving stock instance (DSIGNAlgorithm a, Show msg) => Show (Case a msg)

_ShouldError :: forall (a :: Type) (msg :: Type) .
  Prism' (Case a msg) (ErrorCase a msg)
_ShouldError = prism' into outOf
  where
    into :: ErrorCase a msg -> Case a msg
    into = ShouldError
    outOf :: Case a msg -> Maybe (ErrorCase a msg)
    outOf = \case
      ShouldError x -> pure x
      _             -> Nothing

_Shouldn'tError :: forall (a :: Type) (msg :: Type) .
  Prism' (Case a msg) (NoErrorCase a msg)
_Shouldn'tError = prism' into outOf
  where
    into :: NoErrorCase a msg -> Case a msg
    into = Shouldn'tError
    outOf :: Case a msg -> Maybe (NoErrorCase a msg)
    outOf = \case
      Shouldn'tError x -> pure x
      _                -> Nothing

getCaseData :: forall (a :: Type) (msg :: Type) .
  (DSIGNAlgorithm a) =>
  (msg -> ByteString) ->
  Case a msg ->
  (ByteString, ByteString, ByteString)
getCaseData f = \case
  ShouldError x -> case x of
    BadVerKey vk message sig -> (vk, f message, rawSerialiseSigDSIGN sig)
    BadMsg vk message sig -> (rawSerialiseVerKeyDSIGN vk,
                              message,
                              rawSerialiseSigDSIGN sig)
    BadSig vk message sig -> (rawSerialiseVerKeyDSIGN vk, f message, sig)
  Shouldn'tError x -> case x of
    WrongVerKey vk message sig -> (rawSerialiseVerKeyDSIGN vk,
                                   f message,
                                   rawSerialiseSigDSIGN sig)
    WrongSignature vk message sig -> (rawSerialiseVerKeyDSIGN vk,
                                      f message,
                                      rawSerialiseSigDSIGN sig)
    AllGood vk message sig -> (rawSerialiseVerKeyDSIGN vk,
                               f message,
                               rawSerialiseSigDSIGN sig)

-- Generators

genEcdsaErrorCase :: Gen (ErrorCase EcdsaSecp256k1DSIGN MessageHash)
genEcdsaErrorCase =
  Gen.prune . Gen.choice $ [
    review _BadVerKey <$> mkBadVerKeyBits,
    review _BadMessage <$> mkBadMessageBits,
    review _BadSignature <$> mkBadSignatureBits
    ]
  where
    mkBadVerKeyBits :: Gen (ByteString,
                            MessageHash,
                            SigDSIGN EcdsaSecp256k1DSIGN)
    mkBadVerKeyBits = (,,) <$> genBadVerKey @EcdsaSecp256k1DSIGN <*>
                               genEcdsaMsg <*>
                               genEcdsaSig
    mkBadMessageBits :: Gen (VerKeyDSIGN EcdsaSecp256k1DSIGN,
                             ByteString,
                             SigDSIGN EcdsaSecp256k1DSIGN)
    mkBadMessageBits = (,,) <$> genVerKey <*> genBadEcdsaMsg <*> genEcdsaSig
    mkBadSignatureBits :: Gen (VerKeyDSIGN EcdsaSecp256k1DSIGN,
                               MessageHash,
                               ByteString)
    mkBadSignatureBits = (,,) <$> genVerKey <*>
                                  genEcdsaMsg <*>
                                  genBadSig @EcdsaSecp256k1DSIGN

genSchnorrErrorCase :: Gen (ErrorCase SchnorrSecp256k1DSIGN ByteString)
genSchnorrErrorCase = Gen.choice [
  review _BadVerKey <$> mkBadVerKeyBits,
  review _BadSignature <$> mkBadSignatureBits
  ]
  where
    mkBadVerKeyBits :: Gen (ByteString,
                            ByteString,
                            SigDSIGN SchnorrSecp256k1DSIGN)
    mkBadVerKeyBits = (,,) <$> genBadVerKey @SchnorrSecp256k1DSIGN <*>
                              (Gen.bytes . Range.linear 0 $ 64) <*>
                              genSchnorrSig
    mkBadSignatureBits :: Gen (VerKeyDSIGN SchnorrSecp256k1DSIGN,
                               ByteString,
                               ByteString)
    mkBadSignatureBits = (,,) <$> genVerKey <*>
                                  (Gen.bytes . Range.linear 0 $ 64) <*>
                                  genBadSig @SchnorrSecp256k1DSIGN

genEd25519ErrorCase :: Gen (ErrorCase Ed25519DSIGN ByteString)
genEd25519ErrorCase = Gen.choice [
  review _BadVerKey <$> mkBadVerKeyBits,
  review _BadSignature <$> mkBadSignatureBits
  ]
  where
    mkBadVerKeyBits :: Gen (ByteString,
                            ByteString,
                            SigDSIGN Ed25519DSIGN)
    mkBadVerKeyBits = (,,) <$> genBadVerKey @Ed25519DSIGN <*>
                              (Gen.bytes . Range.linear 0 $ 64) <*>
                              genEd25519Sig
    mkBadSignatureBits :: Gen (VerKeyDSIGN Ed25519DSIGN,
                               ByteString,
                               ByteString)
    mkBadSignatureBits = (,,) <$> genVerKey <*>
                                  (Gen.bytes . Range.linear 0 $ 64) <*>
                                  genBadSig @Ed25519DSIGN

genEcdsaNoErrorCase :: Gen (NoErrorCase EcdsaSecp256k1DSIGN MessageHash)
genEcdsaNoErrorCase = do
  sk <- genSignKey
  let vk = deriveVerKeyDSIGN sk
  msg <- genEcdsaMsg
  Gen.prune . Gen.choice $ [
    review _WrongVerKey <$> mkWrongKeyBits sk vk msg,
    review _WrongSignature <$> mkWrongSignatureBits sk vk msg,
    pure . review _AllGood $ (vk, msg, signDSIGN () msg sk)
    ]
  where
    mkWrongSignatureBits ::
      SignKeyDSIGN EcdsaSecp256k1DSIGN ->
      VerKeyDSIGN EcdsaSecp256k1DSIGN ->
      MessageHash ->
      Gen (VerKeyDSIGN EcdsaSecp256k1DSIGN,
           MessageHash,
           SigDSIGN EcdsaSecp256k1DSIGN)
    mkWrongSignatureBits sk vk msg = do
      msgBad <- Gen.filter (/= msg) genEcdsaMsg
      pure (vk, msg, signDSIGN () msgBad sk)

genSchnorrNoErrorCase :: Gen (NoErrorCase SchnorrSecp256k1DSIGN ByteString)
genSchnorrNoErrorCase = do
  sk <- genSignKey
  let vk = deriveVerKeyDSIGN sk
  msg <- Gen.bytes . Range.linear 0 $ 64
  Gen.choice [
    review _WrongVerKey <$> mkWrongKeyBits sk vk msg,
    review _WrongSignature <$> mkWrongSignatureBits sk vk msg,
    pure . review _AllGood $ (vk, msg, signDSIGN () msg sk)
    ]
  where
    mkWrongSignatureBits ::
      SignKeyDSIGN SchnorrSecp256k1DSIGN ->
      VerKeyDSIGN SchnorrSecp256k1DSIGN ->
      ByteString ->
      Gen (VerKeyDSIGN SchnorrSecp256k1DSIGN,
           ByteString,
           SigDSIGN SchnorrSecp256k1DSIGN)
    mkWrongSignatureBits sk vk msg = do
      msgBad <- Gen.filter (/= msg) (Gen.bytes . Range.linear 0 $ 64)
      pure (vk, msg, signDSIGN () msgBad sk)

genEd25519NoErrorCase :: Gen (NoErrorCase Ed25519DSIGN ByteString)
genEd25519NoErrorCase = do
  sk <- genSignKey
  let vk = deriveVerKeyDSIGN sk
  msg <- Gen.bytes . Range.linear 0 $ 64
  Gen.choice [
    review _WrongVerKey <$> mkWrongKeyBits sk vk msg,
    review _WrongSignature <$> mkWrongSignatureBits sk vk msg,
    pure . review _AllGood $ (vk, msg, signDSIGN () msg sk)
    ]
  where
    mkWrongSignatureBits ::
      SignKeyDSIGN Ed25519DSIGN ->
      VerKeyDSIGN Ed25519DSIGN ->
      ByteString ->
      Gen (VerKeyDSIGN Ed25519DSIGN,
           ByteString,
           SigDSIGN Ed25519DSIGN)
    mkWrongSignatureBits sk vk msg = do
      msgBad <- Gen.filter (/= msg) (Gen.bytes . Range.linear 0 $ 64)
      pure (vk, msg, signDSIGN () msgBad sk)

genEcdsaCase :: Gen (Case EcdsaSecp256k1DSIGN MessageHash)
genEcdsaCase = Gen.prune . Gen.choice $ [
  review _Shouldn'tError <$> genEcdsaNoErrorCase,
  review _ShouldError <$> genEcdsaErrorCase
  ]

genSchnorrCase :: Gen (Case SchnorrSecp256k1DSIGN ByteString)
genSchnorrCase = Gen.prune . Gen.frequency $ [
  (6, review _Shouldn'tError <$> genSchnorrNoErrorCase),
  (4, review _ShouldError <$> genSchnorrErrorCase)
  ]

genEd25519Case :: Gen (Case Ed25519DSIGN ByteString)
genEd25519Case = Gen.prune . Gen.frequency $ [
  (6, review _Shouldn'tError <$> genEd25519NoErrorCase),
  (4, review _ShouldError <$> genEd25519ErrorCase)
  ]

mkWrongKeyBits :: forall (a :: Type) (msg :: Type) .
  (DSIGNAlgorithm a, ContextDSIGN a ~ (), Signable a msg) =>
  SignKeyDSIGN a ->
  VerKeyDSIGN a ->
  msg ->
  Gen (VerKeyDSIGN a, msg, SigDSIGN a)
mkWrongKeyBits sk vk msg = do
  vkBad <- Gen.filter (/= vk) genVerKey
  pure (vkBad, msg, signDSIGN () msg sk)

genBadVerKey :: forall (a :: Type) .
  (DSIGNAlgorithm a) => Gen ByteString
genBadVerKey = Gen.filter (isNothing . rawDeserialiseVerKeyDSIGN @a)
                          (Gen.bytes . Range.linear 0 $ 64)

genEcdsaMsg :: Gen MessageHash
genEcdsaMsg = Gen.mapMaybe toMessageHash (Gen.bytes . Range.singleton $ 32)

genEcdsaSig :: Gen (SigDSIGN EcdsaSecp256k1DSIGN)
genEcdsaSig = do
  sk <- genSignKey
  msg <- genEcdsaMsg
  pure . signDSIGN () msg $ sk

genSchnorrSig :: Gen (SigDSIGN SchnorrSecp256k1DSIGN)
genSchnorrSig = do
  sk <- genSignKey
  msg <- Gen.bytes . Range.linear 0 $ 64
  pure . signDSIGN () msg $ sk

genEd25519Sig :: Gen (SigDSIGN Ed25519DSIGN)
genEd25519Sig = do
  sk <- genSignKey
  msg <- Gen.bytes . Range.linear 0 $ 64
  pure . signDSIGN () msg $ sk

genVerKey :: forall (a :: Type) . (DSIGNAlgorithm a) => Gen (VerKeyDSIGN a)
genVerKey = deriveVerKeyDSIGN <$> genSignKey

genBadEcdsaMsg :: Gen ByteString
genBadEcdsaMsg = Gen.filter (isNothing . toMessageHash) (Gen.bytes . Range.linear 0 $ 64)

genBadSig :: forall (a :: Type) . (DSIGNAlgorithm a) => Gen ByteString
genBadSig = Gen.filter (isNothing . rawDeserialiseSigDSIGN @a)
                       (Gen.bytes . Range.linear 0 $ 64)

genSignKey :: forall (a :: Type) . (DSIGNAlgorithm a) => Gen (SignKeyDSIGN a)
genSignKey = do
  seed <- mkSeedFromBytes <$> (Gen.bytes . Range.linear 64 $ 128)
  pure . genKeyDSIGN $ seed
