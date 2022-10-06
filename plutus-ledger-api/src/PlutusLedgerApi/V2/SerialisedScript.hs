-- editorconfig-checker-disable-file
module PlutusLedgerApi.V2.SerialisedScript
    ( module PlutusLedgerApi.Common.SerialisedScript
    , assertScriptWellFormed
    ) where

import PlutusLedgerApi.Common.SerialisedScript
    hiding ( assertScriptWellFormed
           )
import PlutusLedgerApi.Common.SerialisedScript
    qualified as Override ( assertScriptWellFormed
                          )
import PlutusLedgerApi.Common.Versions
import Control.Monad.Except

-- | Check if a 'Script' is "valid" according to a protocol version. At the moment this means "deserialises correctly", which in particular
-- implies that it is (almost certainly) an encoded script and the script does not mention any builtins unavailable in the given protocol version.
assertScriptWellFormed :: MonadError ScriptDecodeError m
                       => ProtocolVersion
                       -> SerialisedScript
                       -> m ()
assertScriptWellFormed = Override.assertScriptWellFormed PlutusV2

