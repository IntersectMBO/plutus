-- | The user-facing API of the untyped renamer.
-- See Language.PlutusCore.Rename for details.
-- FIXME: Annoyingly, all that's needed here are the instances for Rename,
-- and they're orphans.

{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.UntypedPlutusCore.Rename
    ( Rename (..)
    ) where

import           PlutusPrelude

import           Language.UntypedPlutusCore.Core
import           Language.UntypedPlutusCore.Mark
import           Language.UntypedPlutusCore.Rename.Internal

import           Language.PlutusCore.Core                   (HasUniques)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Rename                 (Rename (..))

instance HasUniques (Term name uni ann) => Rename (Term name uni ann) where
    -- See Note [Marking].
    rename = through markNonFreshTerm >=> runRenameT . renameTermM

instance HasUniques (Program name uni ann) => Rename (Program name uni ann) where
    -- See Note [Marking].
    rename = through markNonFreshProgram >=> runRenameT . renameProgramM

