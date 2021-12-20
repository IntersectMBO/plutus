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
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | Functions for working with scripts on the ledger.
module Plutus.V1.Ledger.Scripts(
    -- * Scripts
    Script (..),
    scriptSize,
    fromCompiledCode,
    ScriptError (..),
    evaluateScript,
    runScript,
    runMintingPolicyScript,
    runStakeValidatorScript,
    applyValidator,
    applyMintingPolicyScript,
    applyStakeValidatorScript,
    applyArguments,
    -- * Script wrappers
    mkValidatorScript,
    Validator (..),
    unValidatorScript,
    Redeemer(..),
    Datum(..),
    mkMintingPolicyScript,
    MintingPolicy (..),
    unMintingPolicyScript,
    mkStakeValidatorScript,
    StakeValidator (..),
    unStakeValidatorScript,
    Context(..),
    -- * Hashes
    DatumHash(..),
    RedeemerHash(..),
    ScriptHash(..),
    ValidatorHash(..),
    MintingPolicyHash (..),
    StakeValidatorHash (..),
    -- * Example scripts
    unitRedeemer,
    unitDatum,
    ) where

import Prelude qualified as Haskell

import Codec.CBOR.Decoding (decodeBytes)
import Codec.Serialise (Serialise, decode, encode, serialise)
import Control.DeepSeq (NFData)
import Control.Monad.Except (MonadError, throwError)
import Data.Aeson (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import Data.Aeson qualified as JSON
import Data.Aeson.Extras qualified as JSON
import Data.ByteArray qualified as BA
import Data.ByteString.Lazy qualified as BSL
import Data.Hashable (Hashable)
import Data.String
import Data.Text (Text)
import Flat qualified
import GHC.Generics (Generic)
import Plutus.V1.Ledger.Bytes (LedgerBytes (..))
import Plutus.V1.Ledger.Orphans ()
import PlutusCore qualified as PLC
import PlutusCore.Data qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Evaluation.Machine.Exception (ErrorWithCause (..), EvaluationError (..))
import PlutusCore.MkPlc qualified as PLC
import PlutusTx (CompiledCode, FromData (..), ToData (..), UnsafeFromData (..), getPlc, makeLift)
import PlutusTx.Builtins as Builtins
import PlutusTx.Builtins.Internal as BI
import PlutusTx.Prelude
import Prettyprinter
import Prettyprinter.Extras
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

-- | A script on the chain. This is an opaque type as far as the chain is concerned.
newtype Script = Script { unScript :: UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun () }
  deriving stock Generic
  -- See Note [Using Flat inside CBOR instance of Script]
  -- Important to go via 'WithSizeLimits' to ensure we enforce the size limits for constants
  deriving Serialise via (SerialiseViaFlat (UPLC.WithSizeLimits 64 (UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ())))

{-| Note [Using Flat inside CBOR instance of Script]
`plutus-ledger` uses CBOR for data serialisation and `plutus-core` uses Flat. The
choice to use Flat was made to have a more efficient (most wins are in uncompressed
size) data serialisation format and use less space on-chain.

To make `plutus-ledger` work with scripts serialised with Flat, and keep the CBOR
format otherwise we have defined a Serialise instance for Script, which is a wrapper
over Programs serialised with Flat. The instance will see programs as an opaque
ByteString, which is the result of encoding programs using Flat.

Because Flat is not self-describing and it gets used in the encoding of Programs,
data structures that include scripts (for example, transactions) no-longer benefit
for CBOR's ability to self-describe it's format.
-}

-- | Newtype for to provide 'Serialise' instances for types with a 'Flat' instance that
-- just encodes the flat-serialized value as a CBOR bytestring
newtype SerialiseViaFlat a = SerialiseViaFlat a
instance Flat.Flat a => Serialise (SerialiseViaFlat a) where
  encode (SerialiseViaFlat a) = encode $ Flat.flat a
  decode = do
    bs <- decodeBytes
    case Flat.unflat bs of
      Left  err -> Haskell.fail (Haskell.show err)
      Right v   -> Haskell.return (SerialiseViaFlat v)

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
instance Haskell.Eq Script where
    a == b = Builtins.toBuiltin (BSL.toStrict (serialise a)) == Builtins.toBuiltin (BSL.toStrict (serialise b))

instance Haskell.Ord Script where
    a `compare` b = Builtins.toBuiltin (BSL.toStrict (serialise a)) `compare` Builtins.toBuiltin (BSL.toStrict (serialise b))

instance Haskell.Show Script where
    showsPrec _ _ = Haskell.showString "<Script>"

instance NFData Script

-- | The size of a 'Script'. No particular interpretation is given to this, other than that it is
-- proportional to the serialized size of the script.
scriptSize :: Script -> Integer
scriptSize (Script s) = UPLC.programSize s

-- See Note [Normalized types in Scripts]
-- | Turn a 'CompiledCode' (usually produced by 'compile') into a 'Script' for use with this package.
fromCompiledCode :: CompiledCode a -> Script
fromCompiledCode = fromPlc . getPlc

fromPlc :: UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun () -> Script
fromPlc (UPLC.Program a v t) =
    let nameless = UPLC.termMapNames UPLC.unNameDeBruijn t
    in Script $ UPLC.Program a v nameless

data ScriptError =
    EvaluationError [Text] Haskell.String -- ^ Expected behavior of the engine (e.g. user-provided error)
    | EvaluationException Haskell.String Haskell.String -- ^ Unexpected behavior of the engine (a bug)
    deriving (Haskell.Show, Haskell.Eq, Generic, NFData)
    deriving anyclass (ToJSON, FromJSON)

applyArguments :: Script -> [PLC.Data] -> Script
applyArguments (Script (UPLC.Program a v t)) args =
    let termArgs = Haskell.fmap (UPLC.termMapNames UPLC.unNameDeBruijn . PLC.mkConstant ()) args
        applied = PLC.mkIterApp () t termArgs
    in Script (UPLC.Program a v applied)

-- | Evaluate a script, returning the trace log.
evaluateScript :: forall m . (MonadError ScriptError m) => Script -> m (PLC.ExBudget, [Text])
evaluateScript s = do
    let t = UPLC.termMapNames UPLC.fakeNameDeBruijn $ UPLC._progTerm $ unScript s
        (result, UPLC.TallyingSt _ budget, logOut) = UPLC.runCekDeBruijn PLC.defaultCekParameters UPLC.tallying UPLC.logEmitter t
    case result of
        Right _ -> Haskell.pure (budget, logOut)
        Left errWithCause@(ErrorWithCause err cause) -> throwError $ case err of
            InternalEvaluationError internalEvalError -> EvaluationException (Haskell.show errWithCause) (PLC.show internalEvalError)
            UserEvaluationError evalError -> EvaluationError logOut (mkError evalError cause) -- TODO fix this error channel fuckery

-- | Create an error message from the contents of an ErrorWithCause.
-- If the cause of an error is a `Just t` where `t = b v0 v1 .. vn` for some builtin `b` then
-- the error will be a "BuiltinEvaluationFailure" otherwise it will be `PLC.show evalError`
mkError :: UPLC.CekUserError -> Maybe (UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()) -> String
mkError evalError Nothing = PLC.show evalError
mkError evalError (Just t) =
  case findBuiltin t of
    Just b  -> "BuiltinEvaluationFailure of " ++ Haskell.show b
    Nothing -> PLC.show evalError
  where
    findBuiltin :: UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun () -> Maybe PLC.DefaultFun
    findBuiltin t = case t of
       UPLC.Apply _ t _   -> findBuiltin t
       UPLC.Builtin _ fun -> Just fun
       -- These two *really shouldn't* appear but
       -- we are future proofing for a day when they do
       UPLC.Force _ t     -> findBuiltin t
       UPLC.Delay _ t     -> findBuiltin t
       -- Future proofing for eta-expanded builtins
       UPLC.LamAbs _ _ t  -> findBuiltin t
       UPLC.Var _ _       -> Nothing
       UPLC.Constant _ _  -> Nothing
       UPLC.Error _       -> Nothing

{- Note [JSON instances for Script]
The JSON instances for Script are partially hand-written rather than going via the Serialise
instance directly. The reason for this is to *avoid* the size checks that are in place in the
Serialise instance. These are only useful for deserialisation checks on-chain, whereas the
JSON instances are used for e.g. transmitting validation events, which often include scripts
with the data arguments applied (which can be very big!).
-}

instance ToJSON Script where
    -- See note [JSON instances for Script]
    toJSON (Script p) = JSON.String $ JSON.encodeSerialise (SerialiseViaFlat p)

instance FromJSON Script where
    -- See note [JSON instances for Script]
    parseJSON v = do
        (SerialiseViaFlat p) <- JSON.decodeSerialise v
        Haskell.return $ Script p

deriving via (JSON.JSONViaSerialise PLC.Data) instance ToJSON PLC.Data
deriving via (JSON.JSONViaSerialise PLC.Data) instance FromJSON PLC.Data

mkValidatorScript :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ()) -> Validator
mkValidatorScript = Validator . fromCompiledCode

unValidatorScript :: Validator -> Script
unValidatorScript = getValidator

mkMintingPolicyScript :: CompiledCode (BuiltinData -> BuiltinData -> ()) -> MintingPolicy
mkMintingPolicyScript = MintingPolicy . fromCompiledCode

unMintingPolicyScript :: MintingPolicy -> Script
unMintingPolicyScript = getMintingPolicy

mkStakeValidatorScript :: CompiledCode (BuiltinData -> BuiltinData -> ()) -> StakeValidator
mkStakeValidatorScript = StakeValidator . fromCompiledCode

unStakeValidatorScript :: StakeValidator -> Script
unStakeValidatorScript = getStakeValidator

-- | 'Validator' is a wrapper around 'Script's which are used as validators in transaction outputs.
newtype Validator = Validator { getValidator :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON, NFData)
  deriving Pretty via (PrettyShow Validator)

instance Haskell.Show Validator where
    show = const "Validator { <script> }"

instance BA.ByteArrayAccess Validator where
    length =
        BA.length . BSL.toStrict . serialise
    withByteArray =
        BA.withByteArray . BSL.toStrict . serialise

-- | 'Datum' is a wrapper around 'Data' values which are used as data in transaction outputs.
newtype Datum = Datum { getDatum :: BuiltinData  }
  deriving stock (Generic, Haskell.Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, ToData, FromData, UnsafeFromData)
  deriving (ToJSON, FromJSON, Serialise, NFData) via PLC.Data
  deriving Pretty via PLC.Data

instance BA.ByteArrayAccess Datum where
    length =
        BA.length . BSL.toStrict . serialise
    withByteArray =
        BA.withByteArray . BSL.toStrict . serialise

-- | 'Redeemer' is a wrapper around 'Data' values that are used as redeemers in transaction inputs.
newtype Redeemer = Redeemer { getRedeemer :: BuiltinData }
  deriving stock (Generic, Haskell.Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, ToData, FromData, UnsafeFromData)
  deriving (ToJSON, FromJSON, Serialise, NFData, Pretty) via PLC.Data

instance BA.ByteArrayAccess Redeemer where
    length =
        BA.length . BSL.toStrict . serialise
    withByteArray =
        BA.withByteArray . BSL.toStrict . serialise

-- | 'MintingPolicy' is a wrapper around 'Script's which are used as validators for minting constraints.
newtype MintingPolicy = MintingPolicy { getMintingPolicy :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON, NFData)
  deriving Pretty via (PrettyShow MintingPolicy)

instance Haskell.Show MintingPolicy where
    show = const "MintingPolicy { <script> }"

instance BA.ByteArrayAccess MintingPolicy where
    length =
        BA.length . BSL.toStrict . serialise
    withByteArray =
        BA.withByteArray . BSL.toStrict . serialise

-- | 'StakeValidator' is a wrapper around 'Script's which are used as validators for withdrawals and stake address certificates.
newtype StakeValidator = StakeValidator { getStakeValidator :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON, NFData)
  deriving Pretty via (PrettyShow MintingPolicy)

instance Haskell.Show StakeValidator where
    show = const "StakeValidator { <script> }"

instance BA.ByteArrayAccess StakeValidator where
    length =
        BA.length . BSL.toStrict . serialise
    withByteArray =
        BA.withByteArray . BSL.toStrict . serialise

-- | Script runtime representation of a @Digest SHA256@.
newtype ScriptHash =
    ScriptHash { getScriptHash :: Builtins.BuiltinByteString }
    deriving (IsString, Haskell.Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, ToData, FromData, UnsafeFromData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey, NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype ValidatorHash =
    ValidatorHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, ToData, FromData, UnsafeFromData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey, NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype DatumHash =
    DatumHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, ToData, FromData, UnsafeFromData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey, NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype RedeemerHash =
    RedeemerHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, ToData, FromData, UnsafeFromData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey, NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype MintingPolicyHash =
    MintingPolicyHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, ToData, FromData, UnsafeFromData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey)

-- | Script runtime representation of a @Digest SHA256@.
newtype StakeValidatorHash =
    StakeValidatorHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Serialise, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, ToData, FromData, UnsafeFromData)
    deriving anyclass (FromJSON, ToJSON, ToJSONKey, FromJSONKey)

-- | Information about the state of the blockchain and about the transaction
--   that is currently being validated, represented as a value in 'Data'.
newtype Context = Context BuiltinData
    deriving (ToJSON, FromJSON, Pretty, Haskell.Show) via PLC.Data

-- | Apply a 'Validator' to its 'Context', 'Datum', and 'Redeemer'.
applyValidator
    :: Context
    -> Validator
    -> Datum
    -> Redeemer
    -> Script
applyValidator (Context (BuiltinData valData)) (Validator validator) (Datum (BuiltinData datum)) (Redeemer (BuiltinData redeemer)) =
    applyArguments validator [datum, redeemer, valData]

-- | Evaluate a 'Validator' with its 'Context', 'Datum', and 'Redeemer', returning the log.
runScript
    :: (MonadError ScriptError m)
    => Context
    -> Validator
    -> Datum
    -> Redeemer
    -> m (PLC.ExBudget, [Text])
runScript context validator datum redeemer = do
    evaluateScript (applyValidator context validator datum redeemer)

-- | Apply 'MintingPolicy' to its 'Context' and 'Redeemer'.
applyMintingPolicyScript
    :: Context
    -> MintingPolicy
    -> Redeemer
    -> Script
applyMintingPolicyScript (Context (BuiltinData valData)) (MintingPolicy validator) (Redeemer (BuiltinData red)) =
    applyArguments validator [red, valData]

-- | Evaluate a 'MintingPolicy' with its 'Context' and 'Redeemer', returning the log.
runMintingPolicyScript
    :: (MonadError ScriptError m)
    => Context
    -> MintingPolicy
    -> Redeemer
    -> m (PLC.ExBudget, [Text])
runMintingPolicyScript context mps red = do
    evaluateScript (applyMintingPolicyScript context mps red)

-- | Apply 'StakeValidator' to its 'Context' and 'Redeemer'.
applyStakeValidatorScript
    :: Context
    -> StakeValidator
    -> Redeemer
    -> Script
applyStakeValidatorScript (Context (BuiltinData valData)) (StakeValidator validator) (Redeemer (BuiltinData red)) =
    applyArguments validator [red, valData]

-- | Evaluate a 'StakeValidator' with its 'Context' and 'Redeemer', returning the log.
runStakeValidatorScript
    :: (MonadError ScriptError m)
    => Context
    -> StakeValidator
    -> Redeemer
    -> m (PLC.ExBudget, [Text])
runStakeValidatorScript context wps red = do
    evaluateScript (applyStakeValidatorScript context wps red)

-- | @()@ as a datum.
unitDatum :: Datum
unitDatum = Datum $ toBuiltinData ()

-- | @()@ as a redeemer.
unitRedeemer :: Redeemer
unitRedeemer = Redeemer $ toBuiltinData ()

makeLift ''ValidatorHash

makeLift ''MintingPolicyHash

makeLift ''StakeValidatorHash

makeLift ''DatumHash

makeLift ''RedeemerHash

makeLift ''Datum

makeLift ''Redeemer
