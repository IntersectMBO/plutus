module UntypedPlutusCore (
    module Export
    , Term (..)
    , Program (..)
    , applyProgram
    , parseScoped
    , PLC.DefaultUni
    , PLC.DefaultFun
    , mkDefaultProg
    ) where

import UntypedPlutusCore.Check.Scope as Export
import UntypedPlutusCore.Core as Export
import UntypedPlutusCore.DeBruijn as Export
import UntypedPlutusCore.Parser as Parser (parseScoped)
import UntypedPlutusCore.Simplify as Export
import UntypedPlutusCore.Size as Export
import UntypedPlutusCore.Subst as Export

import PlutusCore.Core qualified as PLC
import PlutusCore.Default qualified as PLC
import PlutusCore.Name as Export

-- | Take one UPLC program and apply it to another.
applyProgram ::
    Monoid a =>
    Program name uni fun a ->
    Program name uni fun a ->
    Program name uni fun a
applyProgram (Program a1 _ t1) (Program a2 _ t2) =
    Program (a1 <> a2) PLC.defaultVersion (Apply (termAnn t1 <> termAnn t2) t1 t2)

{- | DON'T USE, we'll be getting rid of `defaultVersion`.
Turn a UPLC term to a UPLC program with the default version.
-}
mkDefaultProg :: Term name uni fun () -> Program name uni fun ()
mkDefaultProg = Program () PLC.defaultVersion
