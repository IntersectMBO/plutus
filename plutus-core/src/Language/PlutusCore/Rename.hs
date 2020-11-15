-- | The user-facing API of the renamer.

{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Rename
    ( Rename (..)
    , Dupable
    , liftDupable
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core
import           Language.PlutusCore.Mark
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename.Internal

import           Data.Functor.Identity

{- Note [Marking]
We use functions from the @markNonFresh*@ family in order to ensure that bound variables never get
renamed to free ones. This means types/terms/etc are processed twice: once by a @markNonFresh*@
function and once for the actual renaming. We may consider later to do some kind of meta-circular
programming trick in order to perform renaming in a single pass.
-}

-- | The class of things that can be renamed.
-- I.e. things that are capable of satisfying the global uniqueness condition.
class Rename a where
    -- | Rename 'Unique's so that they're globally unique.
    -- In case there are any free variables, they must be left untouched and bound variables
    -- must not get renamed to free ones.
    -- Must always assign new names to bound variables,
    -- so that @rename@ can be used for alpha-renaming as well.
    rename :: MonadQuote m => a -> m a

instance HasUniques (Type tyname uni ann) => Rename (Type tyname uni ann) where
    -- See Note [Marking].
    rename = through markNonFreshType >=> runRenameT @TypeRenaming . renameTypeM

instance HasUniques (Term tyname name uni fun ann) => Rename (Term tyname name uni fun ann) where
    -- See Note [Marking].
    rename = through markNonFreshTerm >=> runRenameT . renameTermM

instance HasUniques (Program tyname name uni fun ann) => Rename (Program tyname name uni fun ann) where
    -- See Note [Marking].
    rename = through markNonFreshProgram >=> runRenameT . renameProgramM

instance Rename a => Rename (Normalized a) where
    rename = traverse rename

-- | @Dupable a@ is isomorphic to @a@, but the only way to extract the @a@ is via 'liftDupable'
-- which renames the stored value along the way. This type is used whenever
--
-- 1. preserving global uniqueness is required
-- 2. some value may be used multiple times
--
-- so we annotate such a value with 'Dupable' and call 'liftDupable' at each usage, which ensures
-- global conditions is preserved.
newtype Dupable a = Dupable
    { unDupable :: a
    } deriving (Show, Eq, Functor, Foldable, Traversable)
      deriving (Applicative, Monad) via Identity

-- | Extract the value stored in a @Dupable a@ and rename it.
liftDupable :: (MonadQuote m, Rename a) => Dupable a -> m a
liftDupable = liftQuote . rename . unDupable
