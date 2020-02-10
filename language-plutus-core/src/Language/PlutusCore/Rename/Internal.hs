-- | The internal module of the renamer that defines the actual algorithms,
-- but not the user-facing API.

module Language.PlutusCore.Rename.Internal
    ( module Export
    , withFreshenedTyVarDecl
    , withFreshenedVarDecl
    , renameTypeM
    , renameTermM
    , renameProgramM
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename.Monad as Export

-- | Replace the unique in the name stored in a 'TyVarDecl' by a new unique, save the mapping
-- from the old unique to the new one and supply the updated 'TyVarDecl' to a continuation.
withFreshenedTyVarDecl
    :: (HasRenaming ren TypeUnique, HasUniques (Type tyname uni ann), MonadQuote m)
    => TyVarDecl tyname ann
    -> (TyVarDecl tyname ann -> RenameT ren m c)
    -> RenameT ren m c
withFreshenedTyVarDecl (TyVarDecl ann name kind) cont =
    withFreshenedName name $ \nameFr -> cont $ TyVarDecl ann nameFr kind

-- | Replace the unique in the name stored in a 'VarDecl' by a new unique, save the mapping
-- from the old unique to the new one and supply to a continuation the computation that
-- renames the type stored in the updated 'VarDecl'.
-- The reason the continuation receives a computation rather than a pure term is that we may want
-- to bring several term and type variables in scope before renaming the types of term variables.
-- This situation arises when we want to rename a bunch of mutually recursive bindings.
withFreshenedVarDecl
    :: (HasUniques (Term tyname name uni ann), MonadQuote m)
    => VarDecl tyname name uni ann
    -> (ScopedRenameT m (VarDecl tyname name uni ann) -> ScopedRenameT m c)
    -> ScopedRenameT m c
withFreshenedVarDecl (VarDecl ann name ty) cont =
    withFreshenedName name $ \nameFr -> cont $ VarDecl ann nameFr <$> renameTypeM ty

-- | Rename a 'Type' in the 'RenameM' monad.
renameTypeM
    :: (HasRenaming ren TypeUnique, HasUniques (Type tyname uni ann), MonadQuote m)
    => Type tyname uni ann -> RenameT ren m (Type tyname uni ann)
renameTypeM (TyLam ann name kind ty)    =
    withFreshenedName name $ \nameFr -> TyLam ann nameFr kind <$> renameTypeM ty
renameTypeM (TyForall ann name kind ty) =
    withFreshenedName name $ \nameFr -> TyForall ann nameFr kind <$> renameTypeM ty
renameTypeM (TyIFix ann pat arg)        = TyIFix ann <$> renameTypeM pat <*> renameTypeM arg
renameTypeM (TyApp ann fun arg)         = TyApp ann <$> renameTypeM fun <*> renameTypeM arg
renameTypeM (TyFun ann dom cod)         = TyFun ann <$> renameTypeM dom <*> renameTypeM cod
renameTypeM (TyVar ann name)            = TyVar ann <$> renameNameM name
renameTypeM ty@TyBuiltin{}              = pure ty

-- | Rename a 'Term' in the 'RenameM' monad.
renameTermM
    :: (HasUniques (Term tyname name uni ann), MonadQuote m)
    => Term tyname name uni ann -> ScopedRenameT m (Term tyname name uni ann)
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
    :: (HasUniques (Program tyname name uni ann), MonadQuote m)
    => Program tyname name uni ann -> ScopedRenameT m (Program tyname name uni ann)
renameProgramM (Program ann ver term) = Program ann ver <$> renameTermM term
