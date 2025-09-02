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
import UntypedPlutusCore.AstSize as Export
import UntypedPlutusCore.Subst as Export

import PlutusCore.Default qualified as PLC
import PlutusCore.Error (ApplyProgramError (MkApplyProgramError))
import PlutusCore.Name.Unique as Export

import Control.Monad.Except

-- | Applies one program to another. Fails if the versions do not match
-- and tries to merge annotations.
applyProgram
    :: (MonadError ApplyProgramError m, Semigroup a)
    => Program name uni fun a
    -> Program name uni fun a
    -> m (Program name uni fun a)
applyProgram (Program a1 v1 t1) (Program a2 v2 t2) | v1 == v2
  = pure $ Program (a1 <> a2) v1 (Apply (termAnn t1 <> termAnn t2) t1 t2)
applyProgram (Program _a1 v1 _t1) (Program _a2 v2 _t2) =
    throwError $ MkApplyProgramError v1 v2
