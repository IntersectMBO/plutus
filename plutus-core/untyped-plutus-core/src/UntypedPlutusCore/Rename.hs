{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-| The user-facing API of the untyped renamer.
See PlutusCore.Rename for details. -}
module UntypedPlutusCore.Rename
  ( Rename (..)
  ) where

import PlutusPrelude

import UntypedPlutusCore.Core
import UntypedPlutusCore.Mark
import UntypedPlutusCore.Rename.Internal

import PlutusCore.Core (HasUniques)
import PlutusCore.Name.Unique
import PlutusCore.Rename (Rename (..))

instance HasUniques (Term name uni fun ann) => Rename (Term name uni fun ann) where
  -- See Note [Marking].
  rename = through markNonFreshTerm >=> runRenameT . renameTermM

instance HasUniques (Program name uni fun ann) => Rename (Program name uni fun ann) where
  -- See Note [Marking].
  rename = through markNonFreshProgram >=> runRenameT . renameProgramM
