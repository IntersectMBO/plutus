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
    , parseScoped
    , PLC.DefaultUni
    , PLC.DefaultFun
    ) where

import UntypedPlutusCore.Check.Uniques as Uniques
import UntypedPlutusCore.Parser as Parser
import UntypedPlutusCore.Rename as Rename

import PlutusCore.Name as Export
import UntypedPlutusCore.Core as Export
import UntypedPlutusCore.Core.Instance.Flat as Export
import UntypedPlutusCore.DeBruijn as Export
import UntypedPlutusCore.Simplify as Export
import UntypedPlutusCore.Size as Export
import UntypedPlutusCore.Subst as Export
-- Also has some functions


import PlutusCore qualified as PLC
import UntypedPlutusCore.Core

-- | Take one UPLC program and apply it to another.
applyProgram :: Program name uni fun () -> Program name uni fun () -> Program name uni fun ()
applyProgram (Program _ _ t1) (Program _ _ t2) = Program () (PLC.defaultVersion ()) (Apply () t1 t2)


