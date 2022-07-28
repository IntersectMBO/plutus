-- editorconfig-checker-disable-file
module PlutusLedgerApi.Common.SerialisedScript
    ( SerialisedScript
    , scriptCBORDecoder
    , ScriptForExecution (..)
    , isScriptWellFormed
    ) where

import PlutusCore
import PlutusLedgerApi.Common.Versions
import UntypedPlutusCore qualified as UPLC

import Codec.CBOR.Decoding qualified as CBOR
import Codec.CBOR.Extras
import Codec.CBOR.Read qualified as CBOR
import Data.ByteString.Lazy (fromStrict)
import Data.ByteString.Short
import Data.Coerce
import Data.Either
import Data.Set as Set
import Prettyprinter

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

{-| Check if a 'Script' is "valid" according to a protocol version. At the moment this means "deserialises correctly", which in particular
implies that it is (almost certainly) an encoded script and the script does not mention any builtins unavailable in the given protocol version.

Note: Parameterized over the ledger-plutus-version since the builtins allowed (during decoding) differs.
-}
isScriptWellFormed :: LedgerPlutusVersion -> ProtocolVersion -> SerialisedScript -> Bool
isScriptWellFormed lv pv = isRight . CBOR.deserialiseFromBytes (scriptCBORDecoder lv pv) . fromStrict . fromShort

