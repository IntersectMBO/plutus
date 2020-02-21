{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | Functions for working with scripts on the ledger.
module Ledger.Scripts(
    -- * Scripts
    Script (..),
    scriptSize,
    fromCompiledCode,
    Checking (..),
    ScriptError (..),
    evaluateScript,
    runScript,
    runMonetaryPolicyScript,
    applyScript,
    -- * Script wrappers
    mkValidatorScript,
    Validator,
    unValidatorScript,
    RedeemerValue(..),
    DataValue(..),
    mkMonetaryPolicyScript,
    MonetaryPolicy (..),
    unMonetaryPolicyScript,
    ValidationData(..),
    -- * Hashes
    DataValueHash(..),
    RedeemerHash(..),
    ValidatorHash(..),
    MonetaryPolicyHash (..),
    dataValueHash,
    redeemerHash,
    validatorHash,
    monetaryPolicyHash,
    -- * Example scripts
    unitRedeemer,
    unitData
    ) where

import qualified Prelude                              as Haskell

import qualified Codec.CBOR.Write                     as Write
import           Codec.Serialise                      (serialise)
import           Codec.Serialise.Class                (Serialise, encode)
import           Control.DeepSeq                      (NFData)
import           Control.Monad.Except                 (MonadError, runExcept, throwError)
import           Crypto.Hash                          (Digest, SHA256, hash)
import           Data.Aeson                           (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import qualified Data.Aeson                           as JSON
import qualified Data.Aeson.Extras                    as JSON
import qualified Data.ByteArray                       as BA
import qualified Data.ByteString.Lazy                 as BSL
import           Data.Functor                         (void)
import           Data.Hashable                        (Hashable)
import           Data.String
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Extras
import           GHC.Generics                         (Generic)
import           IOTS                                 (IotsType (iotsDefinition))
import qualified Language.PlutusCore                             as PLC
import qualified Language.PlutusCore.Constant.Dynamic            as PLC
import qualified Language.PlutusCore.Pretty                      as PLC
import qualified Language.PlutusCore.Evaluation.Machine.ExMemory as PLC
import           Language.PlutusTx                    (CompiledCode, Data, IsData (..), getPlc, makeLift)
import           Language.PlutusTx.Builtins           as Builtins
import           Language.PlutusTx.Evaluation         (ErrorWithCause (..), EvaluationError (..), evaluateCekTrace)
import           Language.PlutusTx.Lift               (liftCode)
import           Language.PlutusTx.Prelude
import           Ledger.Orphans                       ()
import           LedgerBytes                          (LedgerBytes (..))

-- | A script on the chain. This is an opaque type as far as the chain is concerned.
--
-- Note: the program inside the 'Script' should have normalized types.
newtype Script uni = Script { unScript :: PLC.Program PLC.TyName PLC.Name uni () }
  deriving stock Generic
  deriving newtype (Serialise)

instance IotsType (Script uni) where
  iotsDefinition = iotsDefinition @Haskell.String

{- Note [Normalized types in Scripts]
The Plutus Tx plugin and lifting machinery does not necessarily produce programs
with normalized types, but we are supposed to put programs on the chain *with*
normalized types.

So we normalize types when we turn things into 'Script's. The only operation we
do after that is applying 'Script's together, which preserves type normalization.
-}

{- Note [Eq and Ord for Scripts]
We need `Eq` and `Ord` instances for `Script`s mostly so we can put them in `Set`s.
However, the `Eq` instance for `Program`s is *alpha-equivalence*, and we don't
have a compatible `Ord` instance, nor is it easy to derive one.

So we piggyback off a different representation. In this instance we have two
options:
- Use the serialized form
- Use a hash
The problem with the latter is that we don't want to add a derived `Hashable` instance
for `Program`s that's not compatible with the `Eq` instance. We *could* add a derived
instance for `Program`s with de Bruijn indices, since in that case the derived `Eq`
coincides with alpha-equivalence. However, this might be faster.

For the moment we use the serialized form. We used to store the serialized form directly
in `Script`, but that led to a lot of deserializing and reserializing in `applyProgram`.
Here we have to serialize when we do `Eq` or `Ord` operations, but this happens comparatively
infrequently (I believe).
-}
instance (PLC.Closed uni, uni `PLC.Everywhere` Serialise) => Eq (Script uni) where
    {-# INLINABLE (==) #-}
    a == b = serialise a == serialise b

instance (PLC.Closed uni, uni `PLC.Everywhere` Serialise) => Haskell.Eq (Script uni) where
    a == b = serialise a == serialise b

instance (PLC.Closed uni, uni `PLC.Everywhere` Serialise) => Ord (Script uni) where
    {-# INLINABLE compare #-}
    a `compare` b = serialise a `compare` serialise b

instance (PLC.Closed uni, uni `PLC.Everywhere` Serialise) => Haskell.Ord (Script uni) where
    a `compare` b = serialise a `compare` serialise b

instance (PLC.Closed uni, uni `PLC.Everywhere` NFData) => NFData (Script uni)

data Checking = Typecheck | DontCheck

-- | The size of a 'Script'. No particular interpretation is given to this, other than that it is
-- proportional to the serialized size of the script.
scriptSize :: Script uni -> Integer
scriptSize (Script s) = PLC.programSize s

-- See Note [Normalized types in Scripts]
-- | Turn a 'CompiledCode' (usually produced by 'compile') into a 'Script' for use with this package.
fromCompiledCode :: (PLC.Closed uni, uni `PLC.Everywhere` Serialise) => CompiledCode uni a -> Script uni
fromCompiledCode = fromPlc . getPlc

fromPlc :: PLC.Program PLC.TyName PLC.Name uni () -> Script uni
fromPlc = Script . PLC.runQuote . PLC.normalizeTypesFullInProgram

-- | Given two 'Script's, compute the 'Script' that consists of applying the first to the second.
applyScript :: Script uni -> Script uni -> Script uni
applyScript (unScript -> s1) (unScript -> s2) = Script $ s1 `PLC.applyProgram` s2

data ScriptError =
      TypecheckError Haskell.String -- ^ Incorrect type at runtime
    | EvaluationError [Haskell.String] -- ^ Expected behavior of the engine (e.g. user-provided error)
    | EvaluationException Haskell.String -- ^ Unexpected behavior of the engine (a bug)
    deriving (Haskell.Show, Haskell.Eq, Generic, NFData)
    deriving anyclass (ToJSON, FromJSON)

-- | Evaluate a script, returning the trace log.
evaluateScript
    :: forall uni m .
       ( MonadError ScriptError m
       , PLC.GShow uni, uni `PLC.Everywhere` Pretty
       , PLC.GEq uni, PLC.DefaultUni PLC.<: uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.ExMemoryUsage
       )
    => Checking -> Script uni -> m [Haskell.String]
evaluateScript checking s = do
    case checking of
      DontCheck -> Haskell.pure ()
      Typecheck -> void $ typecheckScript s
    let (logOut, _tally, result) = evaluateCekTrace (unScript s)
    case result of
        Right _ -> Haskell.pure ()
        Left errWithCause@(ErrorWithCause err _) -> throwError $ case err of
            InternalEvaluationError {} -> EvaluationException $ show errWithCause
            UserEvaluationError {}     -> EvaluationError logOut -- TODO fix this error channel fuckery
    Haskell.pure logOut

typecheckScript
    :: forall uni m .
       ( MonadError ScriptError m
       , PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni
       , PLC.Closed uni, uni `PLC.Everywhere` Pretty
       )
    => Script uni -> m (PLC.Type PLC.TyName uni ())
typecheckScript (unScript -> p) =
    either (throwError . TypecheckError . show . PLC.prettyPlcDef) Haskell.pure act
      where
        act :: Either (PLC.Error uni ()) (PLC.Type PLC.TyName uni ())
        act = runExcept $ PLC.runQuoteT $ do
            types <- PLC.getStringBuiltinTypes ()
            -- We should be normalized, so we can use the on-chain config
            -- See Note [Normalized types in Scripts]
            -- FIXME
            let config = PLC.defOnChainConfig { PLC._tccDynamicBuiltinNameTypes = types }
            PLC.unNormalized Haskell.<$> PLC.typecheckPipeline config p

instance (PLC.Closed uni, uni `PLC.Everywhere` Serialise) => ToJSON (Script uni) where
    toJSON = JSON.String . JSON.encodeSerialise

instance (PLC.Closed uni, uni `PLC.Everywhere` Serialise) => FromJSON (Script uni) where
    parseJSON = JSON.decodeSerialise

instance ToJSON Data where
    toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON Data where
    parseJSON = JSON.decodeSerialise

mkValidatorScript
    :: (PLC.Closed uni, uni `PLC.Everywhere` Serialise)
    => CompiledCode uni (Data -> Data -> Data -> ()) -> Validator uni
mkValidatorScript = Validator . fromCompiledCode

unValidatorScript :: Validator uni -> Script uni
unValidatorScript = getValidator

mkMonetaryPolicyScript
    :: (PLC.Closed uni, uni `PLC.Everywhere` Serialise)
    => CompiledCode uni (Data -> ()) -> MonetaryPolicy uni
mkMonetaryPolicyScript = MonetaryPolicy . fromCompiledCode

unMonetaryPolicyScript :: MonetaryPolicy uni -> Script uni
unMonetaryPolicyScript = getMonetaryPolicy

-- | 'Validator' is a wrapper around 'Script's which are used as validators in transaction outputs.
newtype Validator uni = Validator { getValidator :: Script uni }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON, IotsType, NFData)
  deriving Pretty via (PrettyShow (Validator uni))

instance Show (Validator uni) where
    show = const "Validator { <script> }"

instance (PLC.Closed uni, uni `PLC.Everywhere` Serialise) => BA.ByteArrayAccess (Validator uni) where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | 'DataValue' is a wrapper around 'Data' values which are used as data in transaction outputs.
newtype DataValue = DataValue { getDataScript :: Data }
  deriving stock (Generic, Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise, IsData)
  deriving anyclass (ToJSON, FromJSON, IotsType)
  deriving Pretty via Data

instance BA.ByteArrayAccess DataValue where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | 'RedeemerValue' is a wrapper around 'Data' values that are used as redeemers in transaction inputs.
newtype RedeemerValue = RedeemerValue { getRedeemer :: Data }
  deriving stock (Generic, Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON, IotsType)

instance Pretty RedeemerValue where
    pretty (RedeemerValue dat) = "RedeemerValue:" <+> pretty dat

instance BA.ByteArrayAccess RedeemerValue where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | 'MonetaryPolicy' is a wrapper around 'Script's which are used as validators for forging constraints.
newtype MonetaryPolicy uni = MonetaryPolicy { getMonetaryPolicy :: Script uni }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON, IotsType, NFData)
  deriving Pretty via (PrettyShow (MonetaryPolicy uni))

instance Show (MonetaryPolicy uni) where
    show = const "MonetaryPolicy { <script> }"

instance (PLC.Closed uni, uni `PLC.Everywhere` Serialise) => BA.ByteArrayAccess (MonetaryPolicy uni) where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | Script runtime representation of a @Digest SHA256@.
newtype ValidatorHash =
    ValidatorHash Builtins.ByteString
    deriving (IsString, Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, IsData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey)

instance IotsType ValidatorHash where
    iotsDefinition = iotsDefinition @LedgerBytes

-- | Script runtime representation of a @Digest SHA256@.
newtype DataValueHash =
    DataValueHash Builtins.ByteString
    deriving (IsString, Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, IsData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey)

instance IotsType DataValueHash where
    iotsDefinition = iotsDefinition @LedgerBytes

-- | Script runtime representation of a @Digest SHA256@.
newtype RedeemerHash =
    RedeemerHash Builtins.ByteString
    deriving (IsString, Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, IsData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey)

instance IotsType RedeemerHash where
    iotsDefinition = iotsDefinition @LedgerBytes

-- | Script runtime representation of a @Digest SHA256@.
newtype MonetaryPolicyHash =
    MonetaryPolicyHash Builtins.ByteString
    deriving (IsString, Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, IsData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey)

instance IotsType MonetaryPolicyHash where
    iotsDefinition = iotsDefinition @LedgerBytes

dataValueHash :: DataValue -> DataValueHash
dataValueHash = DataValueHash . Builtins.sha2_256 . BSL.fromStrict . BA.convert

redeemerHash :: RedeemerValue -> RedeemerHash
redeemerHash = RedeemerHash . Builtins.sha2_256 . BSL.fromStrict . BA.convert

validatorHash
    :: (PLC.Closed uni, uni `PLC.Everywhere` Serialise)
    => Validator uni -> ValidatorHash
validatorHash vl = ValidatorHash $ BSL.fromStrict $ BA.convert h' where
    h :: Digest SHA256 = hash $ Write.toStrictByteString e
    h' :: Digest SHA256 = hash h
    e = encode vl

monetaryPolicyHash
    :: (PLC.Closed uni, uni `PLC.Everywhere` Serialise)
    => MonetaryPolicy uni -> MonetaryPolicyHash
monetaryPolicyHash vl = MonetaryPolicyHash $ BSL.fromStrict $ BA.convert h' where
    h :: Digest SHA256 = hash $ Write.toStrictByteString e
    h' :: Digest SHA256 = hash h
    e = encode vl

-- | Information about the state of the blockchain and about the transaction
--   that is currently being validated, represented as a value in 'Data'.
newtype ValidationData = ValidationData Data
    deriving stock (Generic, Show)
    deriving anyclass (ToJSON, FromJSON)

-- | Evaluate a validator script with the given arguments, returning the log.
runScript
    :: (MonadError ScriptError m)
    => Checking
    -> ValidationData
    -> Validator PLC.DefaultUni
    -> DataValue
    -> RedeemerValue
    -> m [Haskell.String]
runScript checking (ValidationData valData) (Validator validator) (DataValue dataValue) (RedeemerValue redeemer) = do
    let appliedValidator = ((validator `applyScript` (fromCompiledCode $ liftCode dataValue)) `applyScript` (fromCompiledCode $ liftCode redeemer)) `applyScript` (fromCompiledCode $ liftCode valData)
    evaluateScript checking appliedValidator

-- | Evaluate a monetary policy script just the validation data, returning the log.
runMonetaryPolicyScript
    :: (MonadError ScriptError m)
    => Checking
    -> ValidationData
    -> MonetaryPolicy PLC.DefaultUni
    -> m [Haskell.String]
runMonetaryPolicyScript checking (ValidationData valData) (MonetaryPolicy validator) = do
    let appliedValidator = validator `applyScript` (fromCompiledCode $ liftCode valData)
    evaluateScript checking appliedValidator

-- | @()@ as a data script.
unitData :: DataValue
unitData = DataValue $ toData ()

-- | @()@ as a redeemer.
unitRedeemer :: RedeemerValue
unitRedeemer = RedeemerValue $ toData ()

makeLift ''ValidatorHash

makeLift ''DataValueHash

makeLift ''MonetaryPolicyHash

makeLift ''RedeemerHash

makeLift ''DataValue
