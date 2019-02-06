-- | The internal module of the renamer that defines the actual algorithms,
-- but not the user-facing API.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

module Language.PlutusCore.Rename.Internal
    ( RenameM (..)
    , ScopedRenameM
    , UniquesRenaming
    , ScopedUniquesRenaming
    , HasUniquesRenaming (..)
    , scopedUniquesRenamingTypes
    , scopedUniquesRenamingTerms
    , runRenameM
    , runDirectRenameM
    , runScopedRenameM
    , withFreshenedName
    , withFreshenedTyVarDecl
    , withFreshenedVarDecl
    , renameNameM
    , renameTypeM
    , renameTermM
    , renameProgramM
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Lens.TH
import           Control.Monad.Reader

-- | The monad the renamer runs in.
newtype RenameM renaming a = RenameM
    { unRenameM :: ReaderT renaming Quote a
    } deriving
        ( Functor, Applicative, Monad
        , MonadReader renaming
        , MonadQuote
        )

type ScopedRenameM = RenameM ScopedUniquesRenaming

type UniquesRenaming unique = UniqueMap unique unique

-- | Scoping-aware mapping from locally unique uniques to globally unique uniques.
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

-- | Run a 'RenameM' computation with a supplied @renaming@.
runRenameM :: MonadQuote m => renaming -> RenameM renaming a -> m a
runRenameM renaming (RenameM a) = liftQuote $ runReaderT a renaming

-- | Run a 'RenameM' computation with the empty 'UniquesRenaming'.
runDirectRenameM :: MonadQuote m => RenameM (UniquesRenaming unique) a -> m a
runDirectRenameM = runRenameM mempty

-- | Run a 'RenameM' computation with the empty 'ScopedUniquesRenaming'.
runScopedRenameM :: MonadQuote m => RenameM ScopedUniquesRenaming a -> m a
runScopedRenameM = runRenameM $ ScopedUniquesRenaming mempty mempty

-- | Save the mapping from the @unique@ of a name to a new @unique@.
insertByNameM
    :: (HasUnique name unique, HasUniquesRenaming renaming unique)
    => name -> unique -> renaming -> renaming
insertByNameM name = over uniquesRenaming . insertByName name

-- | Look up the new unique a name got mapped to.
lookupNameM
    :: (HasUnique name unique, HasUniquesRenaming renaming unique)
    => name -> RenameM renaming (Maybe unique)
lookupNameM name = asks $ lookupName name . view uniquesRenaming

-- | Replace the unique in a name by a new unique, save the mapping
-- from the old unique to the new one and supply the updated value to a continuation.
withFreshenedName
    :: (HasUniquesRenaming renaming unique, HasUnique name unique)
    => name -> (name -> RenameM renaming c) -> RenameM renaming c
withFreshenedName name k = do
    uniqNew <- coerce <$> freshUnique
    local (insertByNameM name uniqNew) $ k (name & unique .~ uniqNew)

-- | Replace the unique in the name stored in a 'TyVarDecl' by a new unique, save the mapping
-- from the old unique to the new one and supply the updated 'TyVarDecl' to a continuation.
withFreshenedTyVarDecl
    :: (HasUniquesRenaming renaming TypeUnique, HasUnique (tyname ann) TypeUnique)
    => TyVarDecl tyname ann
    -> (TyVarDecl tyname ann -> RenameM renaming c)
    -> RenameM renaming c
withFreshenedTyVarDecl (TyVarDecl ann name kind) cont =
    withFreshenedName name $ \nameFr -> cont $ TyVarDecl ann nameFr kind

-- | Replace the unique in the name stored in a 'VarDecl' by a new unique, save the mapping
-- from the old unique to the new one and supply to a continuation the computation that
-- renames the type stored in the updated 'VarDecl'.
-- The reason the continuation receives a computation rather than a pure term is that we may want
-- to bring several term and type variables in scope before renaming the types of term variables.
-- This situation arises when we want to rename a bunch of mutually recursive bindings.
withFreshenedVarDecl
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique)
    => VarDecl tyname name ann
    -> (ScopedRenameM (VarDecl tyname name ann) -> ScopedRenameM c)
    -> ScopedRenameM c
withFreshenedVarDecl (VarDecl ann name ty) cont =
    withFreshenedName name $ \nameFr -> cont $ VarDecl ann nameFr <$> renameTypeM ty

-- | Rename a name that has a unique inside.
renameNameM
    :: (HasUniquesRenaming renaming unique, HasUnique name unique)
    => name -> RenameM renaming name
renameNameM name = do
    mayUniqNew <- lookupNameM name
    pure $ case mayUniqNew of
        Nothing      -> name
        Just uniqNew -> name & unique .~ uniqNew

-- | Rename a 'Type' in the 'RenameM' monad.
renameTypeM
    :: (HasUniquesRenaming renaming TypeUnique, HasUnique (tyname ann) TypeUnique)
    => Type tyname ann -> RenameM renaming (Type tyname ann)
renameTypeM (TyLam ann name kind ty)    =
    withFreshenedName name $ \nameFr -> TyLam ann nameFr kind <$> renameTypeM ty
renameTypeM (TyForall ann name kind ty) =
    withFreshenedName name $ \nameFr -> TyForall ann nameFr kind <$> renameTypeM ty
renameTypeM (TyIFix ann pat arg)        = TyIFix ann <$> renameTypeM pat <*> renameTypeM arg
renameTypeM (TyApp ann fun arg)         = TyApp ann <$> renameTypeM fun <*> renameTypeM arg
renameTypeM (TyFun ann dom cod)         = TyFun ann <$> renameTypeM dom <*> renameTypeM cod
renameTypeM (TyVar ann name)            = TyVar ann <$> renameNameM name
renameTypeM ty@TyInt{}                  = pure ty
renameTypeM ty@TyBuiltin{}              = pure ty

-- | Rename a 'Term' in the 'RenameM' monad.
renameTermM
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique)
    => Term tyname name ann -> ScopedRenameM (Term tyname name ann)
renameTermM (LamAbs ann name ty body)  =
    withFreshenedName name $ \nameFr -> LamAbs ann nameFr <$> renameTypeM ty <*> renameTermM body
renameTermM (TyAbs ann name kind body) =
    withFreshenedName name $ \nameFr -> TyAbs ann nameFr kind <$> renameTermM body
renameTermM (IWrap ann pat arg term)   =
    IWrap ann <$> renameTypeM pat <*> renameTypeM arg <*> renameTermM term
renameTermM (Apply ann fun arg)        = Apply ann <$> renameTermM fun <*> renameTermM arg
renameTermM (Unwrap ann term)          = Unwrap ann <$> renameTermM term
renameTermM (Error ann ty)             = Error ann <$> renameTypeM ty
renameTermM (TyInst ann term ty)       = TyInst ann <$> renameTermM term <*> renameTypeM ty
renameTermM (Var ann name)             = Var ann <$> renameNameM name
renameTermM con@Constant{}             = pure con
renameTermM bi@Builtin{}               = pure bi

-- | Rename a 'Program' in the 'RenameM' monad.
renameProgramM
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique)
    => Program tyname name ann -> ScopedRenameM (Program tyname name ann)
renameProgramM (Program ann ver term) = Program ann ver <$> renameTermM term
