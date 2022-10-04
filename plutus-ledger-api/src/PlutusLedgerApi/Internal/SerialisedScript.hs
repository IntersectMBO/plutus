-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE TemplateHaskell #-}
module PlutusLedgerApi.Internal.SerialisedScript
    ( SerialisedScript
    , scriptCBORDecoder
    , ScriptForExecution (..)
    , ScriptDecodeError (..)
    , AsScriptDecodeError (..)
    , deserialiseScriptForExecution
    ) where

import PlutusCore
import PlutusLedgerApi.Common.PlutusVersions
import UntypedPlutusCore qualified as UPLC

import Codec.CBOR.Decoding qualified as CBOR
import Codec.CBOR.Extras
import Codec.CBOR.Read qualified as CBOR
import Control.Arrow ((>>>))
import Control.Exception
import Control.Lens
import Control.Monad.Error.Lens
import Control.Monad.Except
import Data.ByteString.Lazy as BSL (ByteString, fromStrict)
import Data.ByteString.Short
import Data.Coerce
import Data.Set as Set
import Prettyprinter

data ScriptDecodeError =
      CBORDeserialiseError CBOR.DeserialiseFailure
    | RemainderError BSL.ByteString
    | LanguageNotAvailableError
        { sdeAffectedLang :: LedgerPlutusVersion
        , sdeIntroPv      :: ProtocolVersion
        , sdeCurrentPv    :: ProtocolVersion
        }
    deriving stock (Eq, Show)
    deriving anyclass Exception
makeClassyPrisms ''ScriptDecodeError

-- | Scripts to the ledger are serialised bytestrings.
type SerialisedScript = ShortByteString

-- | A variant of `Script` with a specialized decoder.
-- used internally only.
newtype ScriptForExecution = ScriptForExecution (UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ())

{- Note [Size checking of constants in PLC programs]
We impose a 64-byte *on-the-wire* limit on the constants inside PLC programs. This prevents people from inserting
Mickey Mouse entire.

This is somewhat inconvenient for users, but they can always send multiple bytestrings and
concatenate them at runtime.

Unfortunately this check was broken in the ledger Plutus language version V1, and so for backwards compatibility
we only perform it in V2 and above.
-}


{-| Note [Using Flat for serialising/deserialising Script]
`plutus-ledger` uses CBOR for data serialisation and `plutus-core` uses Flat. The
choice to use Flat was made to have a more efficient (most wins are in uncompressed
size) data serialisation format and use less space on-chain.

To make `plutus-ledger` work with scripts serialised with Flat, and keep the CBOR
format otherwise, we have defined the `serialiseUPLC` and `deserialiseUPLC` functions.

Because Flat is not self-describing and it gets used in the encoding of Programs,
data structures that include scripts (for example, transactions) no-longer benefit
for CBOR's ability to self-describe it's format.
-}


{-| This decoder decodes the names directly into `NamedDeBruijn`s rather than `DeBruijn`s.
This is needed because the CEK machine expects `NameDeBruijn`s, but there are obviously no names in the serialised form of a `Script`.
Rather than traversing the term and inserting fake names after deserialising, this lets us do at the same time as deserialising.
-}
scriptCBORDecoder :: LedgerPlutusVersion -> ProtocolVersion -> CBOR.Decoder s ScriptForExecution
scriptCBORDecoder lv pv =
    -- See Note [New builtins and protocol versions]
    let availableBuiltins = builtinsAvailableIn lv pv
        flatDecoder = UPLC.decodeProgram checkBuiltin
        -- TODO: optimize this by using a better datastructure e.g. 'IntSet'
        checkBuiltin f | f `Set.member` availableBuiltins = Nothing
        checkBuiltin f = Just $ "Builtin function " ++ show f ++ " is not available in language " ++ show (pretty lv) ++ " at and protocol version " ++ show (pretty pv)
    in do
        -- Deserialise using 'FakeNamedDeBruijn' to get the fake names added
        (p :: UPLC.Program UPLC.FakeNamedDeBruijn DefaultUni DefaultFun ()) <- decodeViaFlat flatDecoder
        pure $ coerce p

-- | The deserialization from a serialised script to a Script (for execution).
-- Called inside phase-1 validation (assertScriptWellFormed) and inside phase-2's `mkTermToEvaluate`
deserialiseScriptForExecution :: forall e m. (AsScriptDecodeError e, MonadError e m)
                     => LedgerPlutusVersion
                     -> ProtocolVersion
                     -> SerialisedScript
                     -> m ScriptForExecution
deserialiseScriptForExecution lv currentPv sScript = do
    when (introPv > currentPv)  $
        throwing _ScriptDecodeError $ LanguageNotAvailableError lv introPv currentPv
    (remderBS, script) <- deserialiseSScript sScript
    when (lv /= PlutusV1 && lv /= PlutusV2 && remderBS /= mempty) $
        throwing _ScriptDecodeError $ RemainderError remderBS
    pure script
  where
    introPv = languageIntroducedIn lv
    deserialiseSScript :: SerialisedScript -> m (BSL.ByteString, ScriptForExecution)
    deserialiseSScript = fromShort
                       >>> fromStrict
                       >>> CBOR.deserialiseFromBytes (scriptCBORDecoder lv currentPv)
                       -- lift the underlying cbor error to our custom error
                       >>> either (throwing _ScriptDecodeError . CBORDeserialiseError) pure
