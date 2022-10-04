-- editorconfig-checker-disable-file
module PlutusLedgerApi.Common.SerialisedScript
    ( SerialisedScript
    , serialiseCompiledCode
    , serialiseUPLC
    , deserialiseUPLC
    , ScriptDecodeError (..)
    , AsScriptDecodeError (..)
    , assertScriptWellFormed
    ) where

import PlutusLedgerApi.Internal.SerialisedScript

import PlutusCore
import PlutusLedgerApi.Common.PlutusVersions
import PlutusTx.Code
import UntypedPlutusCore qualified as UPLC

import Codec.CBOR.Extras
import Codec.Serialise
import Control.Lens
import Control.Monad.Except
import Data.ByteString.Lazy as BSL (fromStrict, toStrict)
import Data.ByteString.Short

-- FIXME: serialiseUPLC,deserialiseUPLC,serialiseCompiledCode should be perhaps be moved out of the api
-- they are not part of the ledger api, but they are more like user tools

serialiseUPLC :: UPLC.Program UPLC.DeBruijn DefaultUni DefaultFun () -> SerialisedScript
serialiseUPLC =
    -- See Note [Using Flat for serialising/deserialising Script]
    -- Currently, this is off because the old implementation didn't actually work, so we need to be careful
    -- about introducing a working version
    toShort . BSL.toStrict . serialise . SerialiseViaFlat

deserialiseUPLC :: SerialisedScript -> UPLC.Program UPLC.DeBruijn DefaultUni DefaultFun ()
deserialiseUPLC = unSerialiseViaFlat . deserialise . BSL.fromStrict . fromShort
  where
    unSerialiseViaFlat (SerialiseViaFlat a) = a

serialiseCompiledCode :: forall a. CompiledCode a -> SerialisedScript
serialiseCompiledCode = serialiseUPLC . toNameless . getPlc
    where
        toNameless :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
                -> UPLC.Program UPLC.DeBruijn DefaultUni DefaultFun ()
        toNameless = over UPLC.progTerm $ UPLC.termMapNames UPLC.unNameDeBruijn

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
    . deserialiseScriptForExecution lv pv
