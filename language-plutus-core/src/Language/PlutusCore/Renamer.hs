{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Renamer ( Rename (..)
                                   , rename
                                   , annotateProgram
                                   , annotateTerm
                                   , annotateType
                                   , TypeState (..)
                                   , RenameError (..)
                                   ) where

import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Lazy
import qualified Data.IntMap               as IM
import           Lens.Micro
import           Lens.Micro.Extras         (view)
import           Lens.Micro.TH

data TypeState a = TypeState { _terms :: IM.IntMap (RenamedType a), _types :: IM.IntMap (Kind a) }

terms :: Lens' (TypeState a) (IM.IntMap (RenamedType a))
terms f s = fmap (\x -> s { _terms = x }) (f (_terms s))

types :: Lens' (TypeState a) (IM.IntMap (Kind a))
types f s = fmap (\x -> s { _types = x }) (f (_types s))

instance Semigroup (TypeState a) where
    (<>) (TypeState x x') (TypeState y y') = TypeState (x <> y) (x' <> y')

instance Monoid (TypeState a) where
    mempty = TypeState mempty mempty
    mappend = (<>)

type TypeM a = StateT (TypeState a) (Either (RenameError a))

-- | Annotate a PLC program, so that all names are annotated with their types/kinds.
annotateProgram :: (MonadError (Error a) m) => Program TyName Name a -> m (Program TyNameWithKind NameWithType a)
annotateProgram (Program a v t) = Program a v <$> annotateTerm t

-- | Annotate a PLC term, so that all names are annotated with their types/kinds.
annotateTerm :: (MonadError (Error a) m) => Term TyName Name a -> m (Term TyNameWithKind NameWithType a)
annotateTerm t = fmap fst $ liftEither $ convertError $ runStateT (annotateT t) mempty

-- | Annotate a PLC type, so that all names are annotated with their types/kinds.
annotateType :: (MonadError (Error a) m) => Type TyName a -> m (Type TyNameWithKind a)
annotateType t = fmap fst $ liftEither $ convertError $ runStateT (annotateTy t) mempty

insertType :: Int -> Type TyNameWithKind a -> TypeM a ()
insertType = modify .* over terms .* IM.insert

insertKind :: Int -> Kind a -> TypeM a ()
insertKind = modify .* over types .* IM.insert

annotateT :: Term TyName Name a -> TypeM a (RenamedTerm a)
annotateT (Var x (Name x' b (Unique u))) = do
    st <- gets _terms
    case IM.lookup u st of
        Just ty -> pure $ Var x (NameWithType (Name (x', ty) b (Unique u)))
        Nothing -> throwError $ UnboundVar (Name x' b (Unique u))
annotateT (LamAbs x (Name x' s u@(Unique i)) ty t) = do
    aty <- annotateTy ty
    let nwt = NameWithType (Name (x', aty) s u)
    insertType i aty
    LamAbs x nwt aty <$> annotateT t
annotateT (TyAbs x (TyName (Name x' b u@(Unique i))) k t) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) b u))
    TyAbs x nwty k <$> annotateT t
annotateT (Unwrap x t) =
    Unwrap x <$> annotateT t
annotateT (Error x ty) =
    Error x <$> annotateTy ty
annotateT (Apply x t t') =
    Apply x <$> annotateT t <*> annotateT t'
annotateT (Constant x c) =
    pure (Constant x c)
annotateT (TyInst x t ty) =
    TyInst x <$> annotateT t <*> annotateTy ty
annotateT (Wrap x (TyName (Name x' b u@(Unique i))) ty t) = do
    let k = Type x'
    insertKind i k
    aty <- annotateTy ty
    let nwty = TyNameWithKind (TyName (Name (x', k) b u))
    Wrap x nwty aty <$> annotateT t

annotateTy :: Type TyName a -> TypeM a (RenamedType a)
annotateTy (TyVar x (TyName (Name x' b (Unique u)))) = do
    st <- gets _types
    case IM.lookup u st of
        Just ty -> pure $ TyVar x (TyNameWithKind (TyName (Name (x', ty) b (Unique u))))
        Nothing -> throwError $ UnboundTyVar (TyName (Name x' b (Unique u)))
annotateTy (TyLam x (TyName (Name x' s u@(Unique i))) k ty) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyLam x nwty k <$> annotateTy ty
annotateTy (TyForall x (TyName (Name x' s u@(Unique i))) k ty) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyForall x nwty k <$> annotateTy ty
annotateTy (TyFix x (TyName (Name x' s u@(Unique i))) ty) = do
    let k = Type x'
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyFix x nwty <$> annotateTy ty
annotateTy (TyFun x ty ty') =
    TyFun x <$> annotateTy ty <*> annotateTy ty'
annotateTy (TyApp x ty ty') =
    TyApp x <$> annotateTy ty <*> annotateTy ty'
annotateTy (TyBuiltin x tyb) = pure (TyBuiltin x tyb)
annotateTy (TyInt x n) = pure (TyInt x n)

-- | Mapping from locally unique indices to globally unique uniques.
data ScopedUniquesRenaming = ScopedUniquesRenaming
    { _scopedUniquesRenamingTypes :: IM.IntMap TypeUnique
    , _scopedUniquesRenamingTerms :: IM.IntMap TermUnique
    }

makeLenses ''ScopedUniquesRenaming

class Coercible Unique unique => HasUniquesRenaming unique where
    uniquesRenaming :: Lens' ScopedUniquesRenaming (IM.IntMap unique)

instance HasUniquesRenaming TypeUnique where
    uniquesRenaming = scopedUniquesRenamingTypes

instance HasUniquesRenaming TermUnique where
    uniquesRenaming = scopedUniquesRenamingTerms

-- | The monad the renamer runs in.
type RenameM = ReaderT ScopedUniquesRenaming Quote

-- | Rename 'Unique's so that they're globally unique.
-- In case there are any free variables, they're leaved untouched.
-- Always assigns new names to bound variables, hence can be used for cloning as well.
-- Distinguishes between type- and term-level scopes.
rename :: (Rename a, MonadQuote m) => a -> m a
rename x = liftQuote $ runReaderT (renameM x) (ScopedUniquesRenaming mempty mempty)

-- | Save the mapping from an old 'Unique' to a new one.
updateScopedUniquesRenaming
    :: HasUniquesRenaming unique
    => unique -> unique -> ScopedUniquesRenaming -> ScopedUniquesRenaming
updateScopedUniquesRenaming uniqOld uniqNew =
    over uniquesRenaming $ IM.insert (coerce uniqOld) uniqNew

-- | Look up a new unique an old unique got mapped to.
lookupUnique :: HasUniquesRenaming unique => unique -> RenameM (Maybe unique)
lookupUnique uniq = asks $ IM.lookup (coerce uniq) . view uniquesRenaming

-- | Replace the unique in a value by a new unique, save the mapping
-- from an old unique to the new one and supply the updated value to a continuation.
withRefreshed
    :: (HasUniquesRenaming unique, HasUnique a unique)
    => a -> (a -> RenameM c) -> RenameM c
withRefreshed x k = do
    let uniqOld = x ^. unique
    uniqNew <- liftQuote $ coerce <$> freshUnique
    local (updateScopedUniquesRenaming uniqOld uniqNew) $ k (x & unique .~ uniqNew)

-- | The class of things that can be renamed.
-- I.e. things that are capable of satisfying the global uniqueness condition.
class Rename a where
    renameM :: a -> RenameM a

-- | Rename a name that has a unique inside.
renameNameM
    :: (HasUniquesRenaming unique, HasUnique name unique)
    => name -> RenameM name
renameNameM name = do
    let uniqOld = name ^. unique
    mayUniqNew <- lookupUnique uniqOld
    pure $ case mayUniqNew of
        Nothing      -> name
        Just uniqNew -> name & unique .~ uniqNew

instance HasUnique (tyname a) TypeUnique => Rename (Type tyname a) where
    renameM (TyLam ann name kind ty)    =
        withRefreshed name $ \nameFr -> TyLam ann nameFr kind <$> renameM ty
    renameM (TyForall ann name kind ty) =
        withRefreshed name $ \nameFr -> TyForall ann nameFr kind <$> renameM ty
    renameM (TyFix ann name pat)        =
        withRefreshed name $ \nameFr -> TyFix ann nameFr <$> renameM pat
    renameM (TyApp ann fun arg)         = TyApp ann <$> renameM fun <*> renameM arg
    renameM (TyFun ann dom cod)         = TyFun ann <$> renameM dom <*> renameM cod
    renameM (TyVar ann name)            = TyVar ann <$> renameNameM name
    renameM ty@TyInt{}                  = pure ty
    renameM ty@TyBuiltin{}              = pure ty

instance (HasUnique (tyname a) TypeUnique, HasUnique (name a) TermUnique) =>
        Rename (Term tyname name a) where
    renameM (LamAbs ann name ty body)  =
        withRefreshed name $ \nameFr -> LamAbs ann nameFr <$> renameM ty <*> renameM body
    renameM (Wrap ann name ty term)    =
        withRefreshed name $ \nameFr -> Wrap ann nameFr <$> renameM ty <*> renameM term
    renameM (TyAbs ann name kind body) =
        withRefreshed name $ \nameFr -> TyAbs ann nameFr kind <$> renameM body
    renameM (Apply ann fun arg)        = Apply ann <$> renameM fun <*> renameM arg
    renameM (Unwrap ann term)          = Unwrap ann <$> renameM term
    renameM (Error ann ty)             = Error ann <$> renameM ty
    renameM (TyInst ann body ty)       = TyInst ann <$> renameM body <*> renameM ty
    renameM (Var ann name)             = Var ann <$> renameNameM name
    renameM con@Constant{}             = pure con

instance (HasUnique (tyname a) TypeUnique, HasUnique (name a) TermUnique) =>
        Rename (Program tyname name a) where
    renameM (Program ann ver term) = Program ann ver <$> renameM term
