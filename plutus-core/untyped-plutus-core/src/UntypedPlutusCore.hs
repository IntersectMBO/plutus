module UntypedPlutusCore (
    module Export
    , Term (..)
    , Program (..)
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

import UntypedPlutusCore.Parser as Parser (parseScoped)

import UntypedPlutusCore.Simplify as Export

import PlutusCore qualified as PLC
import PlutusCore.Core.Type as Export (Version (..))
import PlutusCore.Name as Export
import UntypedPlutusCore.Core
import UntypedPlutusCore.Core.Instance.Flat as Export
import UntypedPlutusCore.DeBruijn as Export
import UntypedPlutusCore.Size as Export
import UntypedPlutusCore.Subst as Export

-- | Take one UPLC program and apply it to another.
applyProgram :: Program name uni fun () -> Program name uni fun () -> Program name uni fun ()
applyProgram (Program _ _ t1) (Program _ _ t2) = Program () (PLC.defaultVersion ()) (Apply () t1 t2)


