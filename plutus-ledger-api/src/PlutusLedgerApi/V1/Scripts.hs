-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | Functions for working with scripts on the ledger.
module PlutusLedgerApi.V1.Scripts
    (
    -- * Scripts
      Script (..)
    , scriptSize
    , fromCompiledCode
    , ScriptError (..)
    , applyValidator
    , applyMintingPolicyScript
    , applyStakeValidatorScript
    , applyArguments
    -- * Script wrappers
    , mkValidatorScript
    , Validator (..)
    , unValidatorScript
    , Redeemer(..)
    , Datum(..)
    , mkMintingPolicyScript
    , MintingPolicy (..)
    , unMintingPolicyScript
    , mkStakeValidatorScript
    , StakeValidator (..)
    , unStakeValidatorScript
    , Context(..)
    -- * Hashes
    , DatumHash(..)
    , RedeemerHash(..)
    , ScriptHash(..)
    , ValidatorHash(..)
    , MintingPolicyHash (..)
    , StakeValidatorHash (..)
    ) where

import Prelude qualified as Haskell

import Codec.CBOR.Extras (SerialiseViaFlat (..))
import Codec.Serialise (Serialise (..), serialise)
import Control.DeepSeq (NFData)
import Control.Lens hiding (Context)
import Data.ByteString.Lazy qualified as BSL
import Data.String
import Data.Text (Text)
import GHC.Generics (Generic)
import PlutusCore qualified as PLC
import PlutusCore.Data qualified as PLC
import PlutusCore.MkPlc qualified as PLC
import PlutusLedgerApi.V1.Bytes (LedgerBytes (..))
import PlutusTx (CompiledCode, FromData (..), ToData (..), UnsafeFromData (..), getPlc, makeLift)
import PlutusTx.Builtins as Builtins
import PlutusTx.Builtins.Internal as BI
import PlutusTx.Prelude
import Prettyprinter
import Prettyprinter.Extras
import UntypedPlutusCore qualified as UPLC

-- | A script on the chain. This is an opaque type as far as the chain is concerned.
newtype Script = Script { unScript :: UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun () }
  deriving stock (Generic)
  deriving anyclass (NFData)
  -- See Note [Using Flat inside CBOR instance of Script]
  -- Currently, this is off because the old implementation didn't actually work, so we need to be careful
  -- about introducing a working version
  deriving Serialise via (SerialiseViaFlat (UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ()))

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

{- Note [Serialise instances for Datum and Redeemer]
The `Serialise` instances for `Datum` and `Redeemer` exist for several reasons:

- They are useful for the indexers in plutus-apps
- There's clearly only one sensible way to encode `Datum` and `Redeemer` into CBOR,
  since they just wrap `PLC.Data`.
- The encoders and decoders are annoying to implement downstream, because one would
  have to import `BuiltinData` which is from a different package.
-}

instance Haskell.Eq Script where
    a == b = Builtins.toBuiltin (BSL.toStrict (serialise a)) == Builtins.toBuiltin (BSL.toStrict (serialise b))

instance Haskell.Ord Script where
    a `compare` b = Builtins.toBuiltin (BSL.toStrict (serialise a)) `compare` Builtins.toBuiltin (BSL.toStrict (serialise b))

instance Haskell.Show Script where
    showsPrec _ _ = Haskell.showString "<Script>"

-- | The size of a 'Script'. No particular interpretation is given to this, other than that it is
-- proportional to the serialized size of the script.
scriptSize :: Script -> Integer
scriptSize (Script s) = UPLC.programSize s

-- | Turn a 'CompiledCode' (usually produced by 'compile') into a 'Script' for use with this package.
fromCompiledCode :: CompiledCode a -> Script
fromCompiledCode = Script . toNameless . getPlc
    where
      toNameless :: UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
                 -> UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ()
      toNameless = over UPLC.progTerm $ UPLC.termMapNames UPLC.unNameDeBruijn

data ScriptError =
    EvaluationError [Text] Haskell.String -- ^ Expected behavior of the engine (e.g. user-provided error)
    | EvaluationException Haskell.String Haskell.String -- ^ Unexpected behavior of the engine (a bug)
    deriving stock (Haskell.Show, Haskell.Eq, Generic)
    deriving anyclass (NFData)

applyArguments :: Script -> [PLC.Data] -> Script
applyArguments (Script p) args =
    let termArgs = Haskell.fmap (PLC.mkConstant ()) args
        applied t = PLC.mkIterApp () t termArgs
    in Script $ over UPLC.progTerm applied p

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
  deriving anyclass (NFData)
  deriving Pretty via (PrettyShow Validator)

instance Haskell.Show Validator where
    show = const "Validator { <script> }"

-- | 'Datum' is a wrapper around 'Data' values which are used as data in transaction outputs.
newtype Datum = Datum { getDatum :: BuiltinData  }
  deriving stock (Generic, Haskell.Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, ToData, FromData, UnsafeFromData, Pretty)
  deriving anyclass (NFData)

-- See Note [Serialise instances for Datum and Redeemer]
instance Serialise Datum where
    encode (Datum (BuiltinData d)) = encode d
    decode = Datum . BuiltinData Haskell.<$> decode

-- | 'Redeemer' is a wrapper around 'Data' values that are used as redeemers in transaction inputs.
newtype Redeemer = Redeemer { getRedeemer :: BuiltinData }
  deriving stock (Generic, Haskell.Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, ToData, FromData, UnsafeFromData, Pretty)
  deriving anyclass (NFData)

-- See Note [Serialise instances for Datum and Redeemer]
instance Serialise Redeemer where
    encode (Redeemer (BuiltinData d)) = encode d
    decode = Redeemer . BuiltinData Haskell.<$> decode

-- | 'MintingPolicy' is a wrapper around 'Script's which are used as validators for minting constraints.
newtype MintingPolicy = MintingPolicy { getMintingPolicy :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Serialise)
  deriving anyclass (NFData)
  deriving Pretty via (PrettyShow MintingPolicy)

instance Haskell.Show MintingPolicy where
    show = const "MintingPolicy { <script> }"

-- | 'StakeValidator' is a wrapper around 'Script's which are used as validators for withdrawals and stake address certificates.
newtype StakeValidator = StakeValidator { getStakeValidator :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Serialise)
  deriving anyclass (NFData)
  deriving Pretty via (PrettyShow MintingPolicy)

instance Haskell.Show StakeValidator where
    show = const "StakeValidator { <script> }"

-- | Script runtime representation of a @Digest SHA256@.
newtype ScriptHash =
    ScriptHash { getScriptHash :: Builtins.BuiltinByteString }
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype ValidatorHash =
    ValidatorHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype DatumHash =
    DatumHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype RedeemerHash =
    RedeemerHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype MintingPolicyHash =
    MintingPolicyHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype StakeValidatorHash =
    StakeValidatorHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Information about the state of the blockchain and about the transaction
--   that is currently being validated, represented as a value in 'Data'.
newtype Context = Context BuiltinData
    deriving newtype (Pretty, Haskell.Show)

-- | Apply a 'Validator' to its 'Context', 'Datum', and 'Redeemer'.
applyValidator
    :: Context
    -> Validator
    -> Datum
    -> Redeemer
    -> Script
applyValidator (Context (BuiltinData valData)) (Validator validator) (Datum (BuiltinData datum)) (Redeemer (BuiltinData redeemer)) =
    applyArguments validator [datum, redeemer, valData]

-- | Apply 'MintingPolicy' to its 'Context' and 'Redeemer'.
applyMintingPolicyScript
    :: Context
    -> MintingPolicy
    -> Redeemer
    -> Script
applyMintingPolicyScript (Context (BuiltinData valData)) (MintingPolicy validator) (Redeemer (BuiltinData red)) =
    applyArguments validator [red, valData]

-- | Apply 'StakeValidator' to its 'Context' and 'Redeemer'.
applyStakeValidatorScript
    :: Context
    -> StakeValidator
    -> Redeemer
    -> Script
applyStakeValidatorScript (Context (BuiltinData valData)) (StakeValidator validator) (Redeemer (BuiltinData red)) =
    applyArguments validator [red, valData]

makeLift ''ScriptHash

makeLift ''ValidatorHash

makeLift ''MintingPolicyHash

makeLift ''StakeValidatorHash

makeLift ''DatumHash

makeLift ''RedeemerHash

makeLift ''Datum

makeLift ''Redeemer
