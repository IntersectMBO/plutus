module Language.UntypedPlutusCore
    ( module Export
    , applyProgram
    , parseScoped
    ) where

import           Language.UntypedPlutusCore.Check.Uniques      as Uniques
import           Language.UntypedPlutusCore.Parser             as Parser
import           Language.UntypedPlutusCore.Rename             as Rename

import           Language.UntypedPlutusCore.Core               as Export
import           Language.UntypedPlutusCore.Core.Instance.CBOR as Export
import           Language.UntypedPlutusCore.Size               as Export
import           Language.UntypedPlutusCore.Subst              as Export
-- Also has some functions


import qualified Language.PlutusCore                           as PLC
import qualified Language.PlutusCore.Error                     as PLC
import           PlutusPrelude                                 (through)

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                          as BSL


-- | Take one PLC program and apply it to another.
applyProgram :: Program name uni () -> Program name uni () -> Program name uni ()
applyProgram (Program _ _ t1) (Program _ _ t2) = Program () (PLC.defaultVersion ()) (Apply () t1 t2)

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped
    :: (PLC.AsParseError e PLC.AlexPosn,
        PLC.AsUniqueError e PLC.AlexPosn,
        MonadError e m,
        PLC.MonadQuote m)
    => BSL.ByteString
    -> m (Program PLC.Name PLC.DefaultUni PLC.AlexPosn)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped = through (Uniques.checkProgram (const True)) <=< Rename.rename <=< Parser.parseProgram


