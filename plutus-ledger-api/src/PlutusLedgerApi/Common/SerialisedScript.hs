-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE TemplateHaskell #-}
module PlutusLedgerApi.Common.SerialisedScript
    ( SerialisedScript
    , scriptCBORDecoder
    , ScriptForExecution (..)
    , ScriptDecodeError (..)
    , AsScriptDecodeError (..)
    , fromSerialisedScript
    , assertScriptWellFormed
    ) where

import PlutusCore
import PlutusLedgerApi.Common.Versions
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

{- Note [Size checking of constants in PLC programs]
We impose a 64-byte *on-the-wire* limit on the constants inside PLC programs. This prevents people from inserting
Mickey Mouse entire.

This is somewhat inconvenient for users, but they can always send multiple bytestrings and
concatenate them at runtime.

Unfortunately this check was broken in the ledger Plutus language version V1, and so for backwards compatibility
we only perform it in V2 and above.
-}

-- | Scripts to the ledger are serialised bytestrings.
type SerialisedScript = ShortByteString

-- | A variant of `Script` with a specialized decoder.
newtype ScriptForExecution = ScriptForExecution (UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ())

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
fromSerialisedScript :: forall e m. (AsScriptDecodeError e, MonadError e m)
                     => LedgerPlutusVersion
                     -> ProtocolVersion
                     -> SerialisedScript
                     -> m ScriptForExecution
fromSerialisedScript lv currentPv sScript = do
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

{-| Check if a 'Script' is "valid" according to a protocol version. At the moment this means "deserialises correctly", which in particular
implies that it is (almost certainly) an encoded script and the script does not mention any builtins unavailable in the given protocol version.

Note: Parameterized over the ledger-plutus-version since the builtins allowed (during decoding) differs.
-}
assertScriptWellFormed :: MonadError ScriptDecodeError m
                       => LedgerPlutusVersion
                       -> ProtocolVersion
                       -> SerialisedScript
                       -> m ()
assertScriptWellFormed lv pv =
    -- We opt to throw away the ScriptExecution result. for not "leaking" the actual Script through the API.
    void
    . fromSerialisedScript lv pv
