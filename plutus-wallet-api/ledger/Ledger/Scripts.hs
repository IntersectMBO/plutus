{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE ViewPatterns       #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE RankNTypes  #-}
{-# LANGUAGE DerivingVia  #-}
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
    applyScript,
    -- * Script wrappers
    mkValidatorScript,
    ValidatorScript,
    unValidatorScript,
    RedeemerScript(..),
    DataScript(..),
    ValidationData(..),
    -- * Hashes
    DataScriptHash(..),
    RedeemerHash(..),
    ValidatorHash(..),
    plcDataScriptHash,
    plcValidatorDigest,
    plcValidatorHash,
    plcRedeemerHash,
    plcAddress,
    unsafePlcAddress,
    -- * Example scripts
    unitRedeemer,
    unitData
    ) where

import qualified Prelude                                  as Haskell

import qualified Codec.CBOR.Write                         as Write
import           Codec.Serialise                          (serialise)
import           Codec.Serialise.Class                    (Serialise, encode)
import           Control.Monad                            (unless)
import           Control.Monad.Except                     (MonadError(..), runExcept)
import           Control.DeepSeq                          (NFData)
import           Crypto.Hash                              (Digest, SHA256, digestFromByteString)
import           Data.Aeson                               (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import qualified Data.Aeson                               as JSON
import qualified Data.Aeson.Extras                        as JSON
import qualified Data.ByteArray                           as BA
import qualified Data.ByteString.Lazy                     as BSL
import           Data.Functor                             (void)
import           Data.Hashable                            (Hashable)
import           Data.Maybe                               (fromJust)
import           Data.String
import           GHC.Generics                             (Generic)
import qualified Language.PlutusCore                      as PLC
import qualified Language.PlutusCore.Pretty               as PLC
import qualified Language.PlutusCore.Constant.Dynamic     as PLC
import qualified Language.PlutusCore.Evaluation.Result    as PLC
import           Language.PlutusTx.Evaluation             (evaluateCekTrace)
import           Language.PlutusTx.Lift                   (liftCode)
import           Language.PlutusTx                        (CompiledCode, compile, getPlc, makeLift, IsData (..), Data)
import           Language.PlutusTx.Prelude
import           Language.PlutusTx.Builtins               as Builtins
import           LedgerBytes                              (LedgerBytes (..))
import           Ledger.Crypto
import           Schema                                   (ToSchema)

-- | A script on the chain. This is an opaque type as far as the chain is concerned.
--
-- Note: the program inside the 'Script' should have normalized types.
newtype Script = Script { unScript :: PLC.Program PLC.TyName PLC.Name () }
  deriving newtype (Serialise)

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
instance Eq Script where
    {-# INLINABLE (==) #-}
    a == b = serialise a == serialise b

instance Haskell.Eq Script where
    a == b = serialise a == serialise b

instance Ord Script where
    {-# INLINABLE compare #-}
    a `compare` b = serialise a `compare` serialise b

instance Haskell.Ord Script where
    a `compare` b = serialise a `compare` serialise b

data Checking = Typecheck | DontCheck

-- | The size of a 'Script'. No particular interpretation is given to this, other than that it is
-- proportional to the serialized size of the script.
scriptSize :: Script -> Integer
scriptSize (Script s) = PLC.programSize s

-- See Note [Normalized types in Scripts]
-- | Turn a 'CompiledCode' (usually produced by 'compile') into a 'Script' for use with this package.
fromCompiledCode :: CompiledCode a -> Script
fromCompiledCode = fromPlc . getPlc

fromPlc :: PLC.Program PLC.TyName PLC.Name () -> Script
fromPlc = Script . PLC.runQuote . PLC.normalizeTypesFullInProgram

-- | Given two 'Script's, compute the 'Script' that consists of applying the first to the second.
applyScript :: Script -> Script -> Script
applyScript (unScript -> s1) (unScript -> s2) = Script $ s1 `PLC.applyProgram` s2

data ScriptError = TypecheckError Haskell.String | EvaluationError [Haskell.String]
    deriving (Haskell.Show, Haskell.Eq, Generic, NFData)
    deriving anyclass (ToJSON, FromJSON)

-- | Evaluate a script, returning the trace log.
evaluateScript :: forall m . (MonadError ScriptError m) => Checking -> Script -> m [Haskell.String]
evaluateScript checking s = do
    case checking of
      DontCheck -> Haskell.pure ()
      Typecheck -> void $ typecheckScript s
    let (logOut, result) = evaluateCekTrace (unScript s)
    unless (PLC.isEvaluationSuccess result) $ throwError $ EvaluationError logOut
    Haskell.pure logOut

typecheckScript :: (MonadError ScriptError m) => Script -> m (PLC.Type PLC.TyName ())
typecheckScript (unScript -> p) =
    either (throwError . TypecheckError . show . PLC.prettyPlcDef) Haskell.pure $ act
      where
        act :: Either (PLC.Error ()) (PLC.Type PLC.TyName ())
        act = runExcept $ PLC.runQuoteT $ do
            types <- PLC.getStringBuiltinTypes ()
            -- We should be normalized, so we can use the on-chain config
            -- See Note [Normalized types in Scripts]
            -- FIXME
            let config = PLC.defOnChainConfig { PLC._tccDynamicBuiltinNameTypes = types }
            PLC.unNormalized Haskell.<$> PLC.typecheckPipeline config p

instance ToJSON Script where
    toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON Script where
    parseJSON = JSON.decodeSerialise

instance ToJSON Data where
    toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON Data where
    parseJSON = JSON.decodeSerialise

mkValidatorScript :: CompiledCode (Data -> Data -> Data -> Bool) -> ValidatorScript
mkValidatorScript = ValidatorScript . fromCompiledCode

unValidatorScript :: ValidatorScript -> Script
unValidatorScript = getValidator

-- | 'ValidatorScript' is a wrapper around 'Script's which are used as validators in transaction outputs.
newtype ValidatorScript = ValidatorScript { getValidator :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show ValidatorScript where
    show = const "ValidatorScript { <script> }"

instance BA.ByteArrayAccess ValidatorScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | 'DataScript' is a wrapper around 'Data' values which are used as data in transaction outputs.
newtype DataScript = DataScript { getDataScript :: Data  }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise, IsData)
  deriving anyclass (ToJSON, FromJSON)

instance Show DataScript where
    show = const "DataScript { <script> }"

instance BA.ByteArrayAccess DataScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | 'RedeemerScript' is a wrapper around 'Data' values that are used as redeemers in transaction inputs.
newtype RedeemerScript = RedeemerScript { getRedeemer :: Data }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show RedeemerScript where
    show = const "RedeemerScript { <script> }"

instance BA.ByteArrayAccess RedeemerScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | Script runtime representation of a @Digest SHA256@.
newtype ValidatorHash =
    ValidatorHash Builtins.ByteString
    deriving (IsString, Show, ToJSONKey, FromJSONKey, Serialise, FromJSON, ToJSON) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, IsData)
    deriving anyclass (ToSchema)

-- | Script runtime representation of a @Digest SHA256@.
newtype DataScriptHash =
    DataScriptHash Builtins.ByteString
    deriving (IsString, Show, ToJSONKey, FromJSONKey, Serialise, FromJSON, ToJSON) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, IsData)

-- | Script runtime representation of a @Digest SHA256@.
newtype RedeemerHash =
    RedeemerHash Builtins.ByteString
    deriving (IsString, Show, ToJSONKey, FromJSONKey, Serialise, FromJSON, ToJSON) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Hashable, IsData)

{-# INLINABLE plcDataScriptHash #-}
plcDataScriptHash :: DataScript -> DataScriptHash
plcDataScriptHash = DataScriptHash . plcSHA2_256 . BSL.pack . BA.unpack

{-# INLINABLE plcValidatorDigest #-}
-- | Compute the hash of a validator script.
plcValidatorDigest :: Digest SHA256 -> ValidatorHash
plcValidatorDigest = ValidatorHash . BSL.pack . BA.unpack

{-# INLINABLE plcAddress #-}
-- | Get the SHA256 hash (for use in off-chain code) from a 'ValidatorHash'
--   (on-chain)
plcAddress :: ValidatorHash -> Maybe (Digest SHA256)
plcAddress (ValidatorHash hsh) = digestFromByteString $ BSL.toStrict hsh

{-# INLINABLE unsafePlcAddress #-}
-- | Get the SHA256 hash (for use in off-chain code) from a 'ValidatorHash'
--   (on-chain). Should be safe if 'ValidatorHash' was constructed using 
--   'plcValidatorDigest' or 'plcValidatorHash'.
unsafePlcAddress :: ValidatorHash -> Digest SHA256
unsafePlcAddress = fromJust . plcAddress

-- TODO: Is this right? Make it obvious
{-# INLINABLE plcValidatorHash #-}
-- | Compute the hash of a validator script.
plcValidatorHash :: ValidatorScript -> ValidatorHash
plcValidatorHash = ValidatorHash . plcSHA2_256 . BSL.pack . BA.unpack

{-# INLINABLE plcRedeemerHash #-}
plcRedeemerHash :: RedeemerScript -> RedeemerHash
plcRedeemerHash = RedeemerHash . plcSHA2_256 . BSL.pack . BA.unpack

-- | Information about the state of the blockchain and about the transaction
--   that is currently being validated, represented as a value in 'Data'.
newtype ValidationData = ValidationData Data
    deriving stock (Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Show ValidationData where
    show = const "ValidationData { <script> }"

-- | Evaluate a validator script with the given arguments, returning the log and a boolean indicating whether evaluation was successful.
runScript
    :: (MonadError ScriptError m)
    => Checking
    -> ValidationData
    -> ValidatorScript
    -> DataScript
    -> RedeemerScript
    -> m [Haskell.String]
runScript checking (ValidationData valData) (ValidatorScript validator) (DataScript dataScript) (RedeemerScript redeemer) = do
    let appliedValidator = ((validator `applyScript` (fromCompiledCode $ liftCode dataScript)) `applyScript` (fromCompiledCode $ liftCode redeemer)) `applyScript` (fromCompiledCode $ liftCode valData)
    -- See Note [Scripts returning Bool]
    let appliedChecker = checker `applyScript` appliedValidator
    evaluateScript checking appliedChecker

{- Note [Scripts returning Bool]
It used to be that the signal for validation failure was a script being `error`. This is nice for the validator, since
you can determine whether the script evaluation is error-or-not without having to look at what the result actually
*is* if there is one.

However, from the script author's point of view, it would be nicer to return a Bool, since otherwise you end up doing a
lot of `if realCondition then () else error ()` which is rubbish.

So we changed the result type to be Bool. But now we have to answer the question of how the validator knows what the
result value is. All *sorts* of terms can be True or False in disguise. The easiest way to tell is by reducing it
to the previous problem: apply a function which does a pattern match and returns error in the case of False and ()
otherwise. Then, as before, we just check for error in the overall evaluation.
-}

-- | @()@ as a data script.
unitData :: DataScript
unitData = DataScript $ toData ()

-- | @()@ as a redeemer.
unitRedeemer :: RedeemerScript
unitRedeemer = RedeemerScript $ toData ()

-- | @()@ as a redeemer.
checker :: Script
checker = fromCompiledCode $$(compile [|| check ||])

makeLift ''ValidatorHash

makeLift ''DataScriptHash

makeLift ''RedeemerHash

makeLift ''DataScript
