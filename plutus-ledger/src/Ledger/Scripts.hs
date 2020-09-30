{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- | Functions for working with scripts on the ledger.
module Ledger.Scripts(
    -- * Scripts
    Script (..),
    scriptSize,
    fromCompiledCode,
    ScriptError (..),
    evaluateScript,
    runScript,
    runMonetaryPolicyScript,
    -- * Script wrappers
    mkValidatorScript,
    Validator,
    unValidatorScript,
    Redeemer(..),
    Datum(..),
    mkMonetaryPolicyScript,
    MonetaryPolicy (..),
    unMonetaryPolicyScript,
    Context(..),
    -- * Hashes
    DatumHash(..),
    RedeemerHash(..),
    ValidatorHash(..),
    MonetaryPolicyHash (..),
    datumHash,
    redeemerHash,
    validatorHash,
    monetaryPolicyHash,
    -- * Example scripts
    unitRedeemer,
    unitDatum,
    acceptingValidator,
    acceptingMonetaryPolicy
    ) where

import qualified Prelude                             as Haskell

import           Codec.Serialise                     (Serialise, serialise)
import           Control.DeepSeq                     (NFData)
import           Control.Monad.Except                (MonadError, runExceptT, throwError)
import           Crypto.Hash                         (Digest, SHA256, hash)
import           Data.Aeson                          (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import qualified Data.Aeson                          as JSON
import qualified Data.Aeson.Extras                   as JSON
import qualified Data.ByteArray                      as BA
import qualified Data.ByteString.Lazy                as BSL
import           Data.Hashable                       (Hashable)
import           Data.String
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Extras
import           GHC.Generics                        (Generic)
import           IOTS                                (IotsType (iotsDefinition))
import qualified Language.PlutusCore                 as PLC
import           Language.PlutusTx                   (CompiledCode, IsData (..), compile, getPlc, makeLift)
import           Language.PlutusTx.Builtins          as Builtins
import           Language.PlutusTx.Evaluation        (ErrorWithCause (..), EvaluationError (..), evaluateCekTrace)
import           Language.PlutusTx.Lift              (liftCode)
import           Language.PlutusTx.Prelude
import qualified Language.UntypedPlutusCore          as UPLC
import qualified Language.UntypedPlutusCore.DeBruijn as UPLC
import           Ledger.Orphans                      ()
import           LedgerBytes                         (LedgerBytes (..))

-- | A script on the chain. This is an opaque type as far as the chain is concerned.
newtype Script = Script { unScript :: UPLC.Program UPLC.DeBruijn PLC.DefaultUni () }
  deriving stock Generic
  deriving Serialise via UPLC.OmitUnitAnnotations UPLC.DeBruijn PLC.DefaultUni
-- | Don't include unit annotations in the CBOR when serialising.
-- See Note [Serialising Scripts] in Language.PlutusCore.CBOR

instance IotsType Script where
  iotsDefinition = iotsDefinition @Haskell.String

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
instance Eq Script where
    {-# INLINABLE (==) #-}
    a == b = BSL.toStrict (serialise a) == BSL.toStrict (serialise b)

instance Haskell.Eq Script where
    a == b = BSL.toStrict (serialise a) == BSL.toStrict (serialise b)

instance Ord Script where
    {-# INLINABLE compare #-}
    a `compare` b = BSL.toStrict (serialise a) `compare` BSL.toStrict (serialise b)

instance Haskell.Ord Script where
    a `compare` b = BSL.toStrict (serialise a) `compare` BSL.toStrict (serialise b)

instance NFData Script

-- | The size of a 'Script'. No particular interpretation is given to this, other than that it is
-- proportional to the serialized size of the script.
scriptSize :: Script -> Integer
scriptSize (Script s) = UPLC.programSize s

-- See Note [Normalized types in Scripts]
-- | Turn a 'CompiledCode' (usually produced by 'compile') into a 'Script' for use with this package.
fromCompiledCode :: CompiledCode PLC.DefaultUni a -> Script
fromCompiledCode = fromPlc . getPlc

fromPlc :: UPLC.Program PLC.Name PLC.DefaultUni () -> Script
fromPlc (UPLC.Program a v t) = case UPLC.deBruijnTerm $ t of
    Right t' ->
        let nameless = UPLC.termMapNames UPLC.unNameDeBruijn t'
        in Script $ UPLC.Program a v nameless
    Left _   -> Haskell.error "Debruijn failed"

-- | Given two 'Script's, compute the 'Script' that consists of applying the first to the second.
applyScript :: Script -> Script -> Script
applyScript (unScript -> s1) (unScript -> s2) = Script $ s1 `UPLC.applyProgram` s2

data ScriptError =
    EvaluationError [Haskell.String] -- ^ Expected behavior of the engine (e.g. user-provided error)
    | EvaluationException Haskell.String -- ^ Unexpected behavior of the engine (a bug)
    | MalformedScript Haskell.String -- ^ Script is wrong in some way
    deriving (Haskell.Show, Haskell.Eq, Generic, NFData)
    deriving anyclass (ToJSON, FromJSON)

-- | Evaluate a script, returning the trace log.
evaluateScript :: forall m . (MonadError ScriptError m) => Script -> m [Haskell.String]
evaluateScript s = do
    -- TODO: evaluate the nameless debruijn program directly
    let namedProgram =
            let (UPLC.Program a v t) = unScript s
                named = UPLC.termMapNames (\(UPLC.DeBruijn ix) -> UPLC.NamedDeBruijn "" ix) t
            in UPLC.Program a v named
    p <- case PLC.runQuote $ runExceptT $ UPLC.unDeBruijnProgram namedProgram of
        Right p -> return p
        Left e  -> throwError $ MalformedScript $ show e
    let (logOut, _tally, result) = evaluateCekTrace p
    case result of
        Right _ -> Haskell.pure ()
        Left errWithCause@(ErrorWithCause err _) -> throwError $ case err of
            InternalEvaluationError {} -> EvaluationException $ show errWithCause
            UserEvaluationError {}     -> EvaluationError logOut -- TODO fix this error channel fuckery
    Haskell.pure logOut

instance ToJSON Script where
    toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON Script where
    parseJSON = JSON.decodeSerialise

instance ToJSON Data where
    toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON Data where
    parseJSON = JSON.decodeSerialise

mkValidatorScript :: CompiledCode PLC.DefaultUni (Data -> Data -> Data -> ()) -> Validator
mkValidatorScript = Validator . fromCompiledCode

unValidatorScript :: Validator -> Script
unValidatorScript = getValidator

mkMonetaryPolicyScript :: CompiledCode PLC.DefaultUni (Data -> ()) -> MonetaryPolicy
mkMonetaryPolicyScript = MonetaryPolicy . fromCompiledCode

unMonetaryPolicyScript :: MonetaryPolicy -> Script
unMonetaryPolicyScript = getMonetaryPolicy

-- | 'Validator' is a wrapper around 'Script's which are used as validators in transaction outputs.
newtype Validator = Validator { getValidator :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON, IotsType, NFData)
  deriving Pretty via (PrettyShow Validator)

instance Show Validator where
    show = const "Validator { <script> }"

instance BA.ByteArrayAccess Validator where
    length =
        BA.length . BSL.toStrict . serialise
    withByteArray =
        BA.withByteArray . BSL.toStrict . serialise

-- | 'Datum' is a wrapper around 'Data' values which are used as data in transaction outputs.
newtype Datum = Datum { getDatum :: Data  }
  deriving stock (Generic, Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise, IsData)
  deriving anyclass (ToJSON, FromJSON, IotsType)
  deriving Pretty via Data

instance BA.ByteArrayAccess Datum where
    length =
        BA.length . BSL.toStrict . serialise
    withByteArray =
        BA.withByteArray . BSL.toStrict . serialise

-- | 'Redeemer' is a wrapper around 'Data' values that are used as redeemers in transaction inputs.
newtype Redeemer = Redeemer { getRedeemer :: Data }
  deriving stock (Generic, Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON, IotsType)

instance Pretty Redeemer where
    pretty (Redeemer dat) = "Redeemer:" <+> pretty dat

instance BA.ByteArrayAccess Redeemer where
    length =
        BA.length . BSL.toStrict . serialise
    withByteArray =
        BA.withByteArray . BSL.toStrict . serialise

-- | 'MonetaryPolicy' is a wrapper around 'Script's which are used as validators for forging constraints.
newtype MonetaryPolicy = MonetaryPolicy { getMonetaryPolicy :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON, IotsType, NFData)
  deriving Pretty via (PrettyShow MonetaryPolicy)

instance Show MonetaryPolicy where
    show = const "MonetaryPolicy { <script> }"

instance BA.ByteArrayAccess MonetaryPolicy where
    length =
        BA.length . BSL.toStrict . serialise
    withByteArray =
        BA.withByteArray . BSL.toStrict . serialise

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
newtype DatumHash =
    DatumHash Builtins.ByteString
    deriving (IsString, Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, IsData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey)

instance IotsType DatumHash where
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

datumHash :: Datum -> DatumHash
datumHash = DatumHash . Builtins.sha2_256 . BA.convert

redeemerHash :: Redeemer -> RedeemerHash
redeemerHash = RedeemerHash . Builtins.sha2_256 . BA.convert

validatorHash :: Validator -> ValidatorHash
validatorHash vl = ValidatorHash $ BA.convert h' where
    h :: Digest SHA256 = hash $ BSL.toStrict e
    h' :: Digest SHA256 = hash h
    e = serialise vl

monetaryPolicyHash :: MonetaryPolicy -> MonetaryPolicyHash
monetaryPolicyHash vl = MonetaryPolicyHash $ BA.convert h' where
    h :: Digest SHA256 = hash $ BSL.toStrict e
    h' :: Digest SHA256 = hash h
    e = serialise vl

-- | Information about the state of the blockchain and about the transaction
--   that is currently being validated, represented as a value in 'Data'.
newtype Context = Context Data
    deriving stock (Generic, Show)
    deriving anyclass (ToJSON, FromJSON)

-- | Evaluate a validator script with the given arguments, returning the log.
runScript
    :: (MonadError ScriptError m)
    => Context
    -> Validator
    -> Datum
    -> Redeemer
    -> m [Haskell.String]
runScript (Context valData) (Validator validator) (Datum datum) (Redeemer redeemer) = do
    let appliedValidator = ((validator `applyScript` (fromCompiledCode $ liftCode datum)) `applyScript` (fromCompiledCode $ liftCode redeemer)) `applyScript` (fromCompiledCode $ liftCode valData)
    evaluateScript appliedValidator

-- | Evaluate a monetary policy script with just the validation context, returning the log.
runMonetaryPolicyScript
    :: (MonadError ScriptError m)
    => Context
    -> MonetaryPolicy
    -> m [Haskell.String]
runMonetaryPolicyScript (Context valData) (MonetaryPolicy validator) = do
    let appliedValidator = validator `applyScript` (fromCompiledCode $ liftCode valData)
    evaluateScript appliedValidator

-- | @()@ as a datum.
unitDatum :: Datum
unitDatum = Datum $ toData ()

-- | @()@ as a redeemer.
unitRedeemer :: Redeemer
unitRedeemer = Redeemer $ toData ()

-- | A validator that always succeeds.
acceptingValidator :: Validator
acceptingValidator = mkValidatorScript $$(compile [|| (\_ _ _ -> ()) ||])

-- | A monetary policy that always succeeds.
acceptingMonetaryPolicy :: MonetaryPolicy
acceptingMonetaryPolicy = mkMonetaryPolicyScript $$(compile [|| (\_ -> ()) ||])

makeLift ''ValidatorHash

makeLift ''DatumHash

makeLift ''MonetaryPolicyHash

makeLift ''RedeemerHash

makeLift ''Datum
