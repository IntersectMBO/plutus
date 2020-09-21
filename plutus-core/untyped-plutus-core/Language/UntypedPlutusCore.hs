module Language.UntypedPlutusCore
    ( module Export
    , applyProgram
    ) where

import           Language.UntypedPlutusCore.Core               as Export
import           Language.UntypedPlutusCore.Size               as Export
-- Also has some functions
import           Language.UntypedPlutusCore.Core.Instance.CBOR as Export

import qualified Language.PlutusCore                           as PLC

-- | Take one PLC program and apply it to another.
applyProgram :: Program name uni () -> Program name uni () -> Program name uni ()
applyProgram (Program _ _ t1) (Program _ _ t2) = Program () (PLC.defaultVersion ()) (Apply () t1 t2)
