-- | The monad that the renamer runs in and related infrastructure.

{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.PlutusCore.Rename.Monad
    ( RenameT (..)
    , Renaming
    , TypeMapping
    , TermMapping
    , ScopedMapping (..)
    , HasMapping (..)
    , HasRenaming
    , scopedRenamingTypes
    , scopedRenamingTerms
    , runRenameT
    , lookupNameM
    , withMappedUnique
    , withMappedName
    , renameNameM
    , withFreshenedName
    , withRenamedName
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

import           Control.Lens              hiding (mapping)
import           Control.Monad.Reader

-- | The monad the renamer runs in.
newtype RenameT ren m a = RenameT
    { unRenameT :: ReaderT ren m a
    } deriving newtype
        ( Functor, Applicative, Alternative, Monad
        , MonadReader ren
        , MonadQuote
        )

-- | A class that specifies which 'Renaming' a @ren@ has inside.
-- A @ren@ can contain several 'Renaming's (like 'Scoped', for example).
class Coercible unique Unique => HasMapping map unique a | map unique -> a where
    mapping :: Lens' map (UniqueMap unique a)

-- | A renaming is a mapping from old uniques to new ones.
type Renaming unique = UniqueMap unique unique

type HasRenaming ren unique = HasMapping ren unique unique

-- | A type-level mapping.
-- Needed for instantiating functions running over types in generic @RenameT ren m@ to
-- a particular type of renaming.
type TypeMapping = UniqueMap TypeUnique

-- | A term-level mapping.
-- Needed for symmetry with 'TypeMapping'.
type TermMapping = UniqueMap TermUnique

-- | Scoping-aware mapping from locally unique uniques to globally unique uniques.
data ScopedMapping type' term' = ScopedMapping
    { _scopedRenamingTypes :: TypeMapping type'
    , _scopedRenamingTerms :: TermMapping term'
    }

makeLenses ''ScopedMapping

instance Semigroup (ScopedMapping type' term') where
    ScopedMapping types1 terms1 <> ScopedMapping types2 terms2 =
        ScopedMapping (types1 <> types2) (terms1 <> terms2)

instance Monoid (ScopedMapping type' term') where
    mempty = ScopedMapping mempty mempty

instance (Coercible unique1 Unique, unique1 ~ unique2) =>
        HasMapping (UniqueMap unique1 a) unique2 a where
    mapping = id

instance HasMapping (ScopedMapping type' term') TypeUnique type' where
    mapping = scopedRenamingTypes . mapping

instance HasMapping (ScopedMapping type' term') TermUnique term' where
    mapping = scopedRenamingTerms . mapping

-- | Run a 'RenameT' computation with an empty renaming.
runRenameT :: Monoid ren => RenameT ren m a -> m a
runRenameT (RenameT a) = runReaderT a mempty

-- | Look up the new unique a name got mapped to.
lookupNameM
    :: (HasUnique name unique, HasMapping map unique a, Monad m)
    => name -> RenameT map m (Maybe a)
lookupNameM name = asks $ lookupName name . view mapping

-- | Save the mapping from a @unique@ to a value.
insertByUniqueM
    :: HasMapping map unique a
    => unique -> a -> map -> map
insertByUniqueM uniq = over mapping . insertByUnique uniq

-- | Save the mapping from the @unique@ of a name to a value.
insertByNameM
    :: (HasUnique name unique, HasMapping map unique a)
    => name -> a -> map -> map
insertByNameM name = over mapping . insertByName name

-- | Run a 'RenameT' computation in the environment extended by the mapping from a unique to a value.
withMappedUnique
    :: (HasMapping map unique a, Monad m)
    => unique -> a -> RenameT map m c -> RenameT map m c
withMappedUnique uniq = local . insertByUniqueM uniq

-- | Run a 'RenameT' computation in the environment extended by the mapping from a name to a value.
withMappedName
    :: (HasUnique name unique, HasMapping map unique a, Monad m)
    => name -> a -> RenameT map m c -> RenameT map m c
withMappedName name = local . insertByNameM name

-- | Rename a name that has a unique inside.
renameNameM
    :: (HasUnique name unique, HasRenaming ren unique, Monad m)
    => name -> RenameT ren m name
renameNameM name = do
    mayUniqNew <- lookupNameM name
    pure $ case mayUniqNew of
        Nothing      -> name
        Just uniqNew -> name & unique .~ uniqNew

-- | Replace the unique in a name by a new unique, save the mapping
-- from the old unique to the new one and supply the updated value to a continuation.
withFreshenedName
    :: (HasUnique name unique, HasRenaming ren unique, MonadQuote m)
    => name -> (name -> RenameT ren m c) -> RenameT ren m c
withFreshenedName nameOld k = do
    uniqNew <- coerce <$> freshUnique
    local (insertByNameM nameOld uniqNew) $ k (nameOld & unique .~ uniqNew)

-- | Run a 'RenameT' computation in the environment extended by the mapping from an old name
-- to a new one.
withRenamedName
    :: (HasUnique name unique, HasRenaming ren unique, Monad m)
    => name -> name -> RenameT ren m c -> RenameT ren m c
withRenamedName old new = withMappedName old $ new ^. unique
