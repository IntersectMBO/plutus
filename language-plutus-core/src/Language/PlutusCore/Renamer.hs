{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Renamer ( Rename (..)
                                   ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Lens.TH
import           Control.Monad.Reader
import qualified Data.IntMap               as IM

newtype UniquesRenaming unique = UniquesRenaming
    { unUniquesRenaming :: IM.IntMap unique
    }

-- | Scoping-aware mapping from locally unique indices to globally unique uniques.
data ScopedUniquesRenaming = ScopedUniquesRenaming
    { _scopedUniquesRenamingTypes :: UniquesRenaming TypeUnique
    , _scopedUniquesRenamingTerms :: UniquesRenaming TermUnique
    }

makeLenses ''ScopedUniquesRenaming

-- | A class that specifies which 'UniquesRenaming' a @renaming@ has inside.
-- A @renaming@ can contain several 'UniquesRenaming's (like 'ScopedUniquesRenaming', for example).
class Coercible unique Unique => HasUniquesRenaming renaming unique where
    uniquesRenaming :: Lens' renaming (UniquesRenaming unique)

instance (Coercible unique1 Unique, unique1 ~ unique2) =>
        HasUniquesRenaming (UniquesRenaming unique1) unique2 where
    uniquesRenaming = id

instance HasUniquesRenaming ScopedUniquesRenaming TypeUnique where
    uniquesRenaming = scopedUniquesRenamingTypes

instance HasUniquesRenaming ScopedUniquesRenaming TermUnique where
    uniquesRenaming = scopedUniquesRenamingTerms

-- | The class of things that can be renamed.
-- I.e. things that are capable of satisfying the global uniqueness condition.
class Rename a where
    -- | Rename 'Unique's so that they're globally unique.
    -- In case there are any free variables, they must be left untouched.
    -- Must always assign new names to bound variables,
    -- so that @rename@ can be used for alpha renaming as well.
    rename :: MonadQuote m => a -> m a

instance HasUnique (tyname a) TypeUnique => Rename (Type tyname a) where
    rename = runDirectRenameM . renameTypeM

instance (HasUnique (tyname a) TypeUnique, HasUnique (name a) TermUnique) =>
        Rename (Term tyname name a) where
    rename = runScopedRenameM . renameTermM

instance (HasUnique (tyname a) TypeUnique, HasUnique (name a) TermUnique) =>
        Rename (Program tyname name a) where
    rename = runScopedRenameM . renameProgramM

instance HasUnique (tyname a) TypeUnique => Rename (NormalizedType tyname a) where
    rename = traverse rename

-- | The monad the renamer runs in.
type RenameM renaming = ReaderT renaming Quote

-- | Run a 'RenameM' computation with a supplied @renaming@.
runRenameM :: MonadQuote m => renaming -> RenameM renaming a -> m a
runRenameM renaming a = liftQuote $ runReaderT a renaming

-- | Run a 'RenameM' computation with 'emptyUniquesRenaming'.
runDirectRenameM :: MonadQuote m => RenameM (UniquesRenaming unique) a -> m a
runDirectRenameM = runRenameM emptyUniquesRenaming

-- | Run a 'RenameM' computation with 'emptyScopedUniquesRenaming'.
runScopedRenameM :: MonadQuote m => RenameM ScopedUniquesRenaming a -> m a
runScopedRenameM = runRenameM emptyScopedUniquesRenaming

-- | The empty 'UniquesRenaming'.
emptyUniquesRenaming :: UniquesRenaming unique
emptyUniquesRenaming = UniquesRenaming mempty

-- | The empty 'ScopedUniquesRenaming'.
emptyScopedUniquesRenaming :: ScopedUniquesRenaming
emptyScopedUniquesRenaming = ScopedUniquesRenaming emptyUniquesRenaming emptyUniquesRenaming

-- | Save the mapping from an old 'Unique' to a new one.
updateScopedUniquesRenaming
    :: HasUniquesRenaming renaming unique => unique -> unique -> renaming -> renaming
updateScopedUniquesRenaming uniqOld uniqNew =
    over uniquesRenaming $ UniquesRenaming . IM.insert (coerce uniqOld) uniqNew . unUniquesRenaming

-- | Look up a new unique an old unique got mapped to.
lookupUnique :: HasUniquesRenaming renaming unique => unique -> RenameM renaming (Maybe unique)
lookupUnique uniq = asks $ IM.lookup (coerce uniq) . unUniquesRenaming . view uniquesRenaming

-- | Replace the unique in a value by a new unique, save the mapping
-- from an old unique to the new one and supply the updated value to a continuation.
withRefreshed
    :: (HasUniquesRenaming renaming unique, HasUnique a unique)
    => a -> (a -> RenameM renaming c) -> RenameM renaming c
withRefreshed x k = do
    let uniqOld = x ^. unique
    uniqNew <- liftQuote $ coerce <$> freshUnique
    local (updateScopedUniquesRenaming uniqOld uniqNew) $ k (x & unique .~ uniqNew)

-- | Rename a name that has a unique inside.
renameNameM
    :: (HasUniquesRenaming renaming unique, HasUnique name unique)
    => name -> RenameM renaming name
renameNameM name = do
    let uniqOld = name ^. unique
    mayUniqNew <- lookupUnique uniqOld
    pure $ case mayUniqNew of
        Nothing      -> name
        Just uniqNew -> name & unique .~ uniqNew

-- | Rename a 'Type' in the 'RenameM' monad.
renameTypeM
    :: (HasUniquesRenaming renaming TypeUnique, HasUnique (tyname a) TypeUnique)
    => Type tyname a -> RenameM renaming (Type tyname a)
renameTypeM (TyLam ann name kind ty)    =
    withRefreshed name $ \nameFr -> TyLam ann nameFr kind <$> renameTypeM ty
renameTypeM (TyForall ann name kind ty) =
    withRefreshed name $ \nameFr -> TyForall ann nameFr kind <$> renameTypeM ty
renameTypeM (TyIFix ann pat arg)        = TyIFix ann <$> renameTypeM pat <*> renameTypeM arg
renameTypeM (TyApp ann fun arg)         = TyApp ann <$> renameTypeM fun <*> renameTypeM arg
renameTypeM (TyFun ann dom cod)         = TyFun ann <$> renameTypeM dom <*> renameTypeM cod
renameTypeM (TyVar ann name)            = TyVar ann <$> renameNameM name
renameTypeM ty@TyInt{}                  = pure ty
renameTypeM ty@TyBuiltin{}              = pure ty

-- | Rename a 'Term' in the 'RenameM' monad.
renameTermM
    :: (HasUnique (tyname a) TypeUnique, HasUnique (name a) TermUnique)
    => Term tyname name a -> RenameM ScopedUniquesRenaming (Term tyname name a)
renameTermM (LamAbs ann name ty body)  =
    withRefreshed name $ \nameFr -> LamAbs ann nameFr <$> renameTypeM ty <*> renameTermM body
renameTermM (TyAbs ann name kind body) =
    withRefreshed name $ \nameFr -> TyAbs ann nameFr kind <$> renameTermM body
renameTermM (IWrap ann pat arg term)   =
    IWrap ann <$> renameTypeM pat <*> renameTypeM arg <*> renameTermM term
renameTermM (Apply ann fun arg)        = Apply ann <$> renameTermM fun <*> renameTermM arg
renameTermM (Unwrap ann term)          = Unwrap ann <$> renameTermM term
renameTermM (Error ann ty)             = Error ann <$> renameTypeM ty
renameTermM (TyInst ann body ty)       = TyInst ann <$> renameTermM body <*> renameTypeM ty
renameTermM (Var ann name)             = Var ann <$> renameNameM name
renameTermM con@Constant{}             = pure con
renameTermM bi@Builtin{}               = pure bi

-- | Rename a 'Program' in the 'RenameM' monad.
renameProgramM
    :: (HasUnique (tyname a) TypeUnique, HasUnique (name a) TermUnique)
    => Program tyname name a -> RenameM ScopedUniquesRenaming (Program tyname name a)
renameProgramM (Program ann ver term) = Program ann ver <$> renameTermM term
