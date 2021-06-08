-- | Will replace UntypedPlutusCore.

module NewUntypedPlutusCore (
    Term (..)
    , Program (..)
    , toTerm
    , bindFunM
    , bindFun
    , mapFun
    , termAnn
    , erase
    , eraseProgram
    , applyProgram
) where

import qualified PlutusCore             as PLC
import           UntypedPlutusCore.Core

-- | Take one UPLC program and apply it to another.
applyProgram :: Program name uni fun () -> Program name uni fun () -> Program name uni fun ()
applyProgram (Program _ _ t1) (Program _ _ t2) = Program () (PLC.defaultVersion ()) (Apply () t1 t2)


