module UntypedPlutusCore (
    module Export
    , Term (..)
    , Program (..)
    , applyProgram
    , parseScoped
    , PLC.DefaultUni
    , PLC.DefaultFun
    ) where

import UntypedPlutusCore.Check.Scope as Export
import UntypedPlutusCore.Core as Export
import UntypedPlutusCore.DeBruijn as Export
import UntypedPlutusCore.Parser as Parser (parseScoped)
import UntypedPlutusCore.Simplify as Export
import UntypedPlutusCore.Size as Export
import UntypedPlutusCore.Subst as Export

import PlutusCore.Default qualified as PLC
import PlutusCore.Name as Export

-- | Applies one program to another. Takes the maximum of the versions,
-- and tries to merge annotations.
applyProgram ::
    Semigroup a =>
    Program name uni fun a ->
    Program name uni fun a ->
    Program name uni fun a
applyProgram (Program a1 v1 t1) (Program a2 v2 t2) =
    Program (a1 <> a2) (max v1 v2) (Apply (termAnn t1 <> termAnn t2) t1 t2)
