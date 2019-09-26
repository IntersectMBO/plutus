{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE RankNTypes  #-}
{-# LANGUAGE DerivingVia  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | Functions for working with scripts on the ledger.
module Ledger.Scripts(
    -- * Scripts
    Script (..),
    scriptSize,
    fromCompiledCode,
    compileScript,
    lifted,
    applyScript,
    Checking (..),
    ScriptError (..),
    evaluateScript,
    runScript,
    -- * Script wrappers
    ValidatorScript(..),
    RedeemerScript(..),
    DataScript(..),
    DataScripts,
    ValidationData(..),
    -- * Hashes
    DataScriptHash(..),
    RedeemerHash(..),
    ValidatorHash(..),
    plcDataScriptHash,
    plcValidatorDigest,
    plcValidatorHash,
    plcRedeemerHash,
    -- * Data script evidence
    HashedDataScript (..),
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
import           Crypto.Hash                              (Digest, SHA256)
import           Data.List                                (foldl')
import           Data.Aeson                               (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import qualified Data.Aeson                               as JSON
import qualified Data.Aeson.Extras                        as JSON
import qualified Data.ByteArray                           as BA
import qualified Data.ByteString.Lazy                     as BSL
import           Data.Functor                             (void)
import           Data.Hashable                            (Hashable)
import           Data.String
import           Data.Traversable
import           GHC.Generics                             (Generic)
import qualified Language.Haskell.TH                      as TH
import qualified Language.PlutusCore                      as PLC
import qualified Language.PlutusCore.Pretty               as PLC
import qualified Language.PlutusCore.Constant.Dynamic     as PLC
import qualified Language.PlutusCore.Evaluation.Result    as PLC
import           Language.PlutusTx.Evaluation             (evaluateCekTrace)
import           Language.PlutusTx.Lift                   (liftCode)
import           Language.PlutusTx.Lift.Class             (Lift)
import           Language.PlutusTx                        (CompiledCode, compile, getPlc, makeLift, IsData)
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

-- | Compile a quoted Haskell expression to a 'Script'.
compileScript :: TH.Q (TH.TExp a) -> TH.Q (TH.TExp Script)
compileScript a = [|| fromCompiledCode $$(compile a) ||]

-- | Given two 'Script's, compute the 'Script' that consists of applying the first to the second.
applyScript :: Script -> Script -> Script
applyScript (unScript -> s1) (unScript -> s2) = Script $ s1 `PLC.applyProgram` s2

data ScriptError = TypecheckError Haskell.String | EvaluationError [Haskell.String]
    deriving (Haskell.Show, Haskell.Eq, Generic, NFData)

instance ToJSON ScriptError
instance FromJSON ScriptError

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

-- See Note [Normalized types in Scripts]
-- | Lift a Haskell value into the corresponding 'Script'. This allows you to create
-- 'Script's at runtime, whereas 'compileScript' allows you to do so at compile time.
lifted :: Lift a => a -> Script
lifted = fromCompiledCode . liftCode

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

-- | 'DataScript' is a wrapper around 'Script's which are used as data scripts in transaction outputs.
newtype DataScript = DataScript { getDataScript :: Script  }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show DataScript where
    show = const "DataScript { <script> }"

instance BA.ByteArrayAccess DataScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | 'RedeemerScript' is a wrapper around 'Script's that are used as redeemer scripts in transaction inputs.
newtype RedeemerScript = RedeemerScript { getRedeemer :: Script }
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

-- TODO: Is this right? Make it obvious
{-# INLINABLE plcValidatorHash #-}
-- | Compute the hash of a validator script.
plcValidatorHash :: ValidatorScript -> ValidatorHash
plcValidatorHash = ValidatorHash . plcSHA2_256 . BSL.pack . BA.unpack

{-# INLINABLE plcRedeemerHash #-}
plcRedeemerHash :: RedeemerScript -> RedeemerHash
plcRedeemerHash = RedeemerHash . plcSHA2_256 . BSL.pack . BA.unpack

-- | Information about the state of the blockchain and about the transaction
--   that is currently being validated, represented as a value in a 'Script'.
newtype ValidationData = ValidationData Script
    deriving stock (Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Show ValidationData where
    show = const "ValidationData { <script> }"

type DataScripts = [DataScript]

-- | Evaluate a validator script with the given arguments, returning the log and a boolean indicating whether evaluation was successful.
runScript
    :: (MonadError ScriptError m)
    => Checking
    -> ValidationData
    -> DataScripts
    -> ValidatorScript
    -> DataScript
    -> RedeemerScript
    -> m [Haskell.String]
runScript checking (ValidationData valData) dataScripts (ValidatorScript validator) (DataScript dataScript) (RedeemerScript redeemer) = do
    -- See Note [Sealing data scripts]
    dsSealed <- for dataScripts $ \ds -> do
        let script = getDataScript ds
        dsTy <- typecheckScript script
        Haskell.pure $ (sealScript dsTy `applyScript` script) `applyScript` (lifted (plcDataScriptHash ds))
    let appliedRedeemer = foldl' applyScript redeemer dsSealed
    let appliedValidator = ((validator `applyScript` dataScript) `applyScript` appliedRedeemer) `applyScript` valData
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

{- Note [Sealing data scripts]
To pass data scripts securely through the redeemer, we need to *seal* them. This means applying the 'seal' builtin
to the data script value, and then applying the redeemer to all the (sealed) values.

However, 'seal' is *polymorphic*, so we need to instantiate it at the correct type first. So we need to know the
type of all the data scripts, which means we need to typecheck them. This is annoying, but I don't have
another solution at the moment.
-}

{- Note [Impredicative polymorphism and seal]
We need to turn 'seal :: forall a . a -> Sealed a' into a PLC term, which we
can instantiate at a PLC type (which we do *not* have the corresponding Haskell type
for). But this causes GHC to get its knickers in a twist in two ways:
- GHC is very eager to replace the quantified type variable with 'Any', which we can't
currently reconstruct. See Note [Polymorphic values and Any] for more complaining.
- If you try and specify the type you end up asking for a 'CompiledCode (forall a . a -> Sealed a)'.
But this is impredicative polymorphism, and Banned.

So we apply the usual trick of wrapping it in a newtype wrapper. However, we then need
to *unwrap* it to actually apply the function, and the function which does *that* is
also going to be polymorphic, so we hit exactly the same problem defining it.

At this point we deploy a CURSED HACK. We compile newtypes into precisely their
underlying type... so we actually don't have to unwrap it at all! We just leave
it there to satisfy GHC and act as though it's unwrapped later. It's horrible, but
it seems to work.
-}

-- | A data script of type @a@, along with its hash. The hash can be cross-referenced into
-- a 'PendingTx' to determine which output this data script comes from.
data HashedDataScript a = HashedDataScript { getData :: a, getHash :: DataScriptHash }

-- See Note [Impredicative polymorphism and seal]
newtype Sealer = Sealer (forall a . a -> DataScriptHash -> Sealed (HashedDataScript a))

-- | @seal@ as a term at a particular type.
sealScript :: PLC.Type PLC.TyName () -> Script
sealScript ty =
    -- See Note [Impredicative polymorphism and seal]
    let compiled :: CompiledCode (Sealer)
        compiled = $$(compile [|| Sealer (\a hsh -> seal (HashedDataScript a hsh)) ||])
        PLC.Program _ v t = getPlc $ compiled
    in fromPlc $ PLC.Program ()  v $ PLC.TyInst () t ty

-- | @()@ as a data script.
unitData :: DataScript
unitData = DataScript $ fromCompiledCode $$(compile [|| () ||])

-- | @()@ as a redeemer.
unitRedeemer :: RedeemerScript
unitRedeemer = RedeemerScript $ fromCompiledCode $$(compile [|| () ||])

-- | @()@ as a redeemer.
checker :: Script
checker = fromCompiledCode $$(compile [|| check ||])

makeLift ''ValidatorHash

makeLift ''DataScriptHash

makeLift ''RedeemerHash

makeLift ''HashedDataScript
