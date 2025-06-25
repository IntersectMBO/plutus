-- | The monad that the renamer runs in and related infrastructure.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module PlutusCore.Rename.Monad
    ( RenameT (..)
    , ScopedRenameT
    , Renaming (..)
    , TypeRenaming
    , ScopedRenaming (..)
    , HasRenaming (..)
    , scopedRenamingTypes
    , scopedRenamingTerms
    , emptyRenaming
    , emptyScopedRenaming
    , runRenameT
    , lookupNameM
    , renameNameM
    , withFreshenedName
    , withRenamedName
    ) where

import PlutusPrelude (Alternative, Coercible, Lens', coerce, over, view, (&), (.~), (^.))

import PlutusCore.Name.Unique (HasUnique (..), TermUnique (TermUnique), TypeUnique (TypeUnique),
                               Unique (Unique))
import PlutusCore.Name.UniqueMap (UniqueMap (UniqueMap), emptyUniqueMap, insertByName, lookupName)
import PlutusCore.Quote (MonadQuote, freshUnique)

import Control.Lens (makeLenses)
import Control.Monad.Reader (MonadReader (local), ReaderT (..), asks)

-- | The monad the renamer runs in.
newtype RenameT ren m a = RenameT
    { unRenameT :: ReaderT ren m a
    } deriving newtype
        ( Functor, Applicative, Alternative, Monad
        , MonadReader ren
        , MonadQuote
        )

-- | A renaming is a mapping from old uniques to new ones.
newtype Renaming unique = Renaming
    { unRenaming :: UniqueMap unique unique
    }

-- | A type-level renaming.
-- Needed for instantiating functions running over types in generic @RenameT ren m@ to
-- a particular type of renaming.
type TypeRenaming = Renaming TypeUnique

-- | A class that specifies which 'Renaming' a @ren@ has inside.
-- A @ren@ can contain several 'Renaming's (like 'Scoped', for example).
class Coercible unique Unique => HasRenaming ren unique where
    renaming :: Lens' ren (Renaming unique)

-- | Scoping-aware mapping from locally unique uniques to globally unique uniques.
data ScopedRenaming = ScopedRenaming
    { _scopedRenamingTypes :: Renaming TypeUnique
    , _scopedRenamingTerms :: Renaming TermUnique
    }

makeLenses ''ScopedRenaming

type ScopedRenameT = RenameT ScopedRenaming

instance (Coercible unique1 Unique, unique1 ~ unique2) =>
        HasRenaming (Renaming unique1) unique2 where
    renaming = id

instance HasRenaming ScopedRenaming TypeUnique where
    renaming = scopedRenamingTypes . renaming

instance HasRenaming ScopedRenaming TermUnique where
    renaming = scopedRenamingTerms . renaming

emptyRenaming :: Renaming unique
emptyRenaming = Renaming emptyUniqueMap

emptyScopedRenaming :: ScopedRenaming
emptyScopedRenaming = ScopedRenaming emptyRenaming emptyRenaming

-- | Run a 'RenameT' computation with an empty renaming.
runRenameT :: ren -> RenameT ren m a -> m a
runRenameT emp (RenameT a) = runReaderT a emp

-- | Map the underlying representation of 'Renaming'.
mapRenaming
    :: (UniqueMap unique unique -> UniqueMap unique unique)
    -> Renaming unique
    -> Renaming unique
mapRenaming = coerce

-- | Save the mapping from the @unique@ of a name to a new @unique@.
insertByNameM
    :: (HasUnique name unique, HasRenaming ren unique)
    => name -> unique -> ren -> ren
insertByNameM name = over renaming . mapRenaming . insertByName name

-- | Look up the new unique a name got mapped to.
lookupNameM
    :: (HasUnique name unique, HasRenaming ren unique, MonadReader ren m)
    => name -> m (Maybe unique)
lookupNameM name = asks $ lookupName name . unRenaming . view renaming

-- | Rename a name that has a unique inside.
renameNameM
    :: (HasRenaming ren unique, HasUnique name unique, MonadReader ren m)
    => name -> m name
renameNameM name = do
    mayUniqNew <- lookupNameM name
    pure $ case mayUniqNew of
        Nothing      -> name
        Just uniqNew -> name & unique .~ uniqNew

-- | Replace the unique in a name by a new unique, save the mapping
-- from the old unique to the new one and supply the updated value to a continuation.
withFreshenedName
    :: (HasRenaming ren unique, HasUnique name unique, MonadQuote m, MonadReader ren m)
    => name -> (name -> m c) -> m c
withFreshenedName nameOld k = do
    uniqNew <- coerce <$> freshUnique
    local (insertByNameM nameOld uniqNew) $ k (nameOld & unique .~ uniqNew)

-- | Run a 'RenameT' computation in the environment extended by the mapping from an old name
-- to a new one.
withRenamedName
    :: (HasRenaming ren unique, HasUnique name unique, MonadReader ren m)
    => name -> name -> m c -> m c
withRenamedName old new = local $ insertByNameM old (new ^. unique)
