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
import PlutusCore.Error (ApplyProgramError (MkApplyProgramError))
import PlutusCore.Name as Export

-- | Applies one program to another. Fails if the versions do not match
-- and tries to merge annotations.
applyProgram
    :: Semigroup a
    => Program name uni fun a
    -> Program name uni fun a
    -> Either ApplyProgramError (Program name uni fun a)
applyProgram (Program a1 v1 t1) (Program a2 v2 t2) | v1 == v2
  = Right $ Program (a1 <> a2) v1 (Apply (termAnn t1 <> termAnn t2) t1 t2)
applyProgram (Program _a1 v1 _t1) (Program _a2 v2 _t2) =
    Left $ MkApplyProgramError v1 v2
