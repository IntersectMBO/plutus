{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The user-facing API of the renamer.
module PlutusCore.Rename
  ( Renamed (unRenamed)
  , Rename (..)
  , getRenamed
  , Dupable
  , dupable
  , liftDupable
  ) where

import PlutusPrelude

import PlutusCore.Core
import PlutusCore.Mark
import PlutusCore.Name.Unique
import PlutusCore.Quote
import PlutusCore.Rename.Internal

{- Note [Marking]
We use functions from the @markNonFresh*@ family in order to ensure that bound variables never get
renamed to free ones. This means types/terms/etc are processed twice: once by a @markNonFresh*@
function and once for the actual renaming. We may consider later to do some kind of meta-circular
programming trick in order to perform renaming in a single pass.
-}

{-| The class of things that can be renamed.
I.e. things that are capable of satisfying the global uniqueness condition. -}
class Rename a where
  {-| Rename 'Unique's so that they're globally unique.
  In case there are any free variables, they must be left untouched and bound variables
  must not get renamed to free ones.
  Must always assign new names to bound variables,
  so that @rename@ can be used for alpha-renaming as well. -}
  rename :: MonadQuote m => a -> m a

{-| 'rename' a value and wrap the result in 'Renamed', so that it can be passed around and it's
visible in the types that the thing inside satisfies global uniqueness. -}
getRenamed :: (Rename a, MonadQuote m) => a -> m (Renamed a)
getRenamed = fmap Renamed . rename

-- | Wrap a value in 'Dupable'.
dupable :: a -> Dupable a
dupable = Dupable

-- | Extract the value stored in a @Dupable a@ and rename it.
liftDupable :: (MonadQuote m, Rename a) => Dupable a -> m a
liftDupable = liftQuote . rename . unDupable

instance HasUniques (Type tyname uni ann) => Rename (Type tyname uni ann) where
  -- See Note [Marking].
  rename = through markNonFreshType >=> runRenameT @TypeRenaming . renameTypeM

instance HasUniques (Term tyname name uni fun ann) => Rename (Term tyname name uni fun ann) where
  -- See Note [Marking].
  rename = through markNonFreshTerm >=> runRenameT . renameTermM

instance
  HasUniques (Program tyname name uni fun ann)
  => Rename (Program tyname name uni fun ann)
  where
  -- See Note [Marking].
  rename = through markNonFreshProgram >=> runRenameT . renameProgramM

instance Rename a => Rename (Normalized a) where
  rename = traverse rename
