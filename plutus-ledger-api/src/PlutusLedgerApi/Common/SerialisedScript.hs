{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE TemplateHaskell #-}

module PlutusLedgerApi.Common.SerialisedScript (
  SerialisedScript,
  serialiseCompiledCode,
  serialiseUPLC,
  uncheckedDeserialiseUPLC,
  scriptCBORDecoder,
  ScriptNamedDeBruijn (..),
  ScriptForEvaluation, -- Do not export data constructor
  ScriptDecodeError (..),
  AsScriptDecodeError (..),
  DeserialiseFailureInfo (..),
  DeserialiseFailureReason (..),
  deserialiseScript,
  serialisedScript,
  deserialisedScript,
) where

import PlutusCore
import PlutusLedgerApi.Common.Versions
import PlutusTx.Code
import UntypedPlutusCore qualified as UPLC

-- this allows us to safe, 0-cost coerce from FND->ND. Unfortunately, since Coercible is symmetric,
-- we cannot expose this safe Coercible FND ND w.o. also allowing the unsafe Coercible ND FND.
import PlutusCore.DeBruijn.Internal (FakeNamedDeBruijn (FakeNamedDeBruijn))

import Codec.CBOR.Decoding qualified as CBOR
import Codec.CBOR.Extras as CBOR.Extras
import Codec.CBOR.Read qualified as CBOR
import Codec.Serialise
import Control.Arrow ((>>>))
import Control.DeepSeq (NFData)
import Control.Exception
import Control.Lens
import Control.Monad (unless, when)
import Control.Monad.Error.Lens
import Control.Monad.Except (MonadError)
import Data.ByteString.Lazy as BSL (ByteString, fromStrict, toStrict)
import Data.ByteString.Short
import Data.Coerce
import Data.Set as Set
import GHC.Generics
import NoThunks.Class
import Prettyprinter

-- | An error that occurred during script deserialization.
data ScriptDecodeError
  = -- | an error from the underlying CBOR/serialise library
    CBORDeserialiseError !CBOR.Extras.DeserialiseFailureInfo
  | -- | Script was successfully parsed, but more (runaway) bytes encountered
    -- after script's position
    RemainderError !BSL.ByteString
  | -- | the plutus version of the given script is not enabled yet
    LedgerLanguageNotAvailableError
      { sdeAffectedLang :: !PlutusLedgerLanguage
      -- ^ the script's ledger language
      , sdeIntroPv      :: !MajorProtocolVersion
      -- ^ the major protocol version that will first introduce/enable the ledger language
      , sdeThisPv       :: !MajorProtocolVersion
      -- ^ the current protocol version
      }
  | PlutusCoreLanguageNotAvailableError
      { sdeAffectedVersion :: !UPLC.Version
      -- ^ the script's Plutus Core language version
      , sdeThisPv          :: !MajorProtocolVersion
      -- ^ the current protocol version
      }
  deriving stock (Eq, Show)
  deriving anyclass (Exception)

makeClassyPrisms ''ScriptDecodeError

{- Note [Size checking of constants in PLC programs]
We impose a 64-byte *on-the-wire* limit on the constants inside PLC programs. This prevents
people from inserting Mickey Mouse entire.

This is somewhat inconvenient for users, but they can always send multiple bytestrings and
concatenate them at runtime.

Unfortunately this check was broken in the ledger Plutus language version V1, and so for
backwards compatibility we only perform it in V2 and above.
-}

-- | Scripts to the ledger are serialised bytestrings.
type SerialisedScript = ShortByteString

{- Note [Using Flat for serialising/deserialising Script]
`plutus-ledger` uses CBOR for data serialisation and `plutus-core` uses Flat. The
choice to use Flat was made to have a more efficient (most wins are in uncompressed
size) data serialisation format and use less space on-chain.

To make `plutus-ledger` work with scripts serialised with Flat, and keep the CBOR
format otherwise, we have defined the `serialiseUPLC` and `uncheckedDeserialiseUPLC` functions.

Because Flat is not self-describing and it gets used in the encoding of Programs,
data structures that include scripts (for example, transactions) no-longer benefit
from CBOR's ability to self-describe its format.
-}

{- | Turns a program which was compiled using the \'PlutusTx\' toolchain into
a binary format that is understood by the network and can be stored on-chain.
-}
serialiseCompiledCode :: forall a. CompiledCode a -> SerialisedScript
serialiseCompiledCode =
  -- MAYBE: Instead of this `serialiseUPLC . toNameLess` we could instead
  -- call `serialise(coerce @(Prog ND) @(Prog FND))` which, despite violating momentarily the
  -- invariant `fnd.name==fakeName`, would be faster.
  serialiseUPLC . toNameless . getPlcNoAnn
  where
    toNameless ::
      UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun () ->
      UPLC.Program UPLC.DeBruijn DefaultUni DefaultFun ()
    toNameless = over UPLC.progTerm $ UPLC.termMapNames UPLC.unNameDeBruijn

{- | Turns a program's AST (most likely manually constructed)
into a binary format that is understood by the network and can be stored on-chain.
-}
serialiseUPLC :: UPLC.Program UPLC.DeBruijn DefaultUni DefaultFun () -> SerialisedScript
serialiseUPLC =
  -- See Note [Using Flat for serialising/deserialising Script]
  -- Currently, this is off because the old implementation didn't actually work, so we
  -- need to be careful about introducing a working version
  toShort . BSL.toStrict . serialise . SerialiseViaFlat . UPLC.UnrestrictedProgram

{- | Deserialises a 'SerialisedScript' back into an AST. Does *not* do
ledger-language-version-specific checks like for allowable builtins.
-}
uncheckedDeserialiseUPLC :: SerialisedScript -> UPLC.Program UPLC.DeBruijn DefaultUni DefaultFun ()
uncheckedDeserialiseUPLC = unSerialiseViaFlat . deserialise . BSL.fromStrict . fromShort
  where
    unSerialiseViaFlat (SerialiseViaFlat (UPLC.UnrestrictedProgram a)) = a

-- | A script with named de-bruijn indices.
newtype ScriptNamedDeBruijn
  = ScriptNamedDeBruijn (UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ())
  deriving stock (Eq, Show, Generic)
  deriving anyclass (NFData)

-- | A Plutus script ready to be evaluated on-chain, via @evaluateScriptRestricting@.
data ScriptForEvaluation = UnsafeScriptForEvaluation !SerialisedScript !ScriptNamedDeBruijn
  deriving stock (Eq, Show, Generic)
  deriving anyclass (NFData)

-- Only check WHNF for NoThunks, since the only way to obtain a ScriptForEvaluation
-- is `deserialiseScript`.
deriving via OnlyCheckWhnf ScriptForEvaluation instance NoThunks ScriptForEvaluation

-- | Get a `SerialisedScript` from a `ScriptForEvaluation`. /O(1)/.
serialisedScript :: ScriptForEvaluation -> SerialisedScript
serialisedScript (UnsafeScriptForEvaluation s _) = s

-- | Get a `ScriptNamedDeBruijn` from a `ScriptForEvaluation`. /O(1)/.
deserialisedScript :: ScriptForEvaluation -> ScriptNamedDeBruijn
deserialisedScript (UnsafeScriptForEvaluation _ s) = s

{- | This decoder decodes the names directly into `NamedDeBruijn`s rather than `DeBruijn`s.
This is needed because the CEK machine expects `NameDeBruijn`s, but there are obviously no
names in the serialised form of a `Script`. Rather than traversing the term and inserting
fake names after deserialising, this lets us do at the same time as deserialising.
-}
scriptCBORDecoder ::
  PlutusLedgerLanguage ->
  MajorProtocolVersion ->
  CBOR.Decoder s ScriptNamedDeBruijn
scriptCBORDecoder lv pv =
  -- See Note [New builtins and protocol versions]
  let availableBuiltins = builtinsAvailableIn lv pv
      flatDecoder = UPLC.decodeProgram checkBuiltin
      -- TODO: optimize this by using a better datastructure e.g. 'IntSet'
      checkBuiltin f | f `Set.member` availableBuiltins = Nothing
      checkBuiltin f =
        Just $
          "Builtin function "
            ++ show f
            ++ " is not available in language "
            ++ show (pretty lv)
            ++ " at and protocol version "
            ++ show (pretty pv)
   in do
        -- Deserialise using 'FakeNamedDeBruijn' to get the fake names added
        (p :: UPLC.Program UPLC.FakeNamedDeBruijn DefaultUni DefaultFun ()) <-
          decodeViaFlat flatDecoder
        pure $ coerce p

{- | The deserialization from a serialised script into a `ScriptForEvaluation`,
ready to be evaluated on-chain.
Called inside phase-1 validation (i.e., deserialisation error is a phase-1 error).
-}
deserialiseScript ::
  forall m.
  (MonadError ScriptDecodeError m) =>
  -- | the Plutus ledger language of the script.
  PlutusLedgerLanguage ->
  -- | which major protocol version the script was submitted in.
  MajorProtocolVersion ->
  -- | the script to deserialise.
  SerialisedScript ->
  m ScriptForEvaluation
deserialiseScript ll pv sScript = do
  -- check that the ledger language version is available
  let llIntroPv = ledgerLanguageIntroducedIn ll
  unless (llIntroPv <= pv) $
    throwing _ScriptDecodeError $
      LedgerLanguageNotAvailableError ll llIntroPv pv

  (remderBS, dScript@(ScriptNamedDeBruijn (UPLC.Program{}))) <- deserialiseSScript sScript
  when (ll /= PlutusV1 && ll /= PlutusV2 && remderBS /= mempty) $
    throwing _ScriptDecodeError $
      RemainderError remderBS

  pure $ UnsafeScriptForEvaluation sScript dScript
  where
    deserialiseSScript :: SerialisedScript -> m (BSL.ByteString, ScriptNamedDeBruijn)
    deserialiseSScript =
      fromShort
        >>> fromStrict
        >>> CBOR.deserialiseFromBytes (scriptCBORDecoder ll pv)
        -- lift the underlying cbor error to our custom error
        >>> either (throwing _ScriptDecodeError . toScripDecodeError) pure

    -- turn a cborg failure to our own error type
    toScripDecodeError :: CBOR.DeserialiseFailure -> ScriptDecodeError
    toScripDecodeError = CBORDeserialiseError . CBOR.Extras.readDeserialiseFailureInfo
