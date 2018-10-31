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
annotateT (IWrap x (TyName (Name x' b u@(Unique i))) ty arg t) = do
    annotatedArg <- annotateTy arg
    let k = Type x'
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) b u))
    IWrap x nwty <$> annotateTy ty <*> pure annotatedArg <*> annotateT t

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
annotateTy (TyIFix x (TyName (Name x' s u@(Unique i))) ty arg) = do
    annotatedArg <- annotateTy arg
    let k = Type x'
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyIFix x nwty <$> annotateTy ty <*> pure annotatedArg
annotateTy (TyFun x ty ty') =
    TyFun x <$> annotateTy ty <*> annotateTy ty'
annotateTy (TyApp x ty ty') =
    TyApp x <$> annotateTy ty <*> annotateTy ty'
annotateTy (TyBuiltin x tyb) = pure (TyBuiltin x tyb)
annotateTy (TyInt x n) = pure (TyInt x n)

-- | Mapping from locally unique indices to globally unique 'Unique's.
newtype UniquesRenaming = UniquesRenaming
    { unUniquesRenaming :: IM.IntMap Unique
    }

-- | The monad the renamer runs in.
type RenameM = ReaderT UniquesRenaming Quote

-- | Rename 'Unique's so that they're globally unique.
rename :: (Rename a, MonadQuote m) => a -> m a
rename x = liftQuote $ runReaderT (renameM x) (UniquesRenaming mempty)

-- | Save the mapping from an old 'Unique' to a new one.
updateUniquesRenaming :: Unique -> Unique -> UniquesRenaming -> UniquesRenaming
updateUniquesRenaming uniqOld uniqNew (UniquesRenaming uniques) =
    UniquesRenaming $ IM.insert (unUnique uniqOld) uniqNew uniques

-- | Look up a new 'Unique' an old 'Unique' got mapped to.
lookupUnique :: Unique -> RenameM (Maybe Unique)
lookupUnique uniq = asks $ IM.lookup (unUnique uniq) . unUniquesRenaming

-- | Replace the 'Unique' in a value by a new 'Unique', save the mapping
-- from an old 'Unique' to the new one and supply the updated value to a continuation.
withRefreshed :: HasUnique a => a -> (a -> RenameM c) -> RenameM c
withRefreshed x k = do
    let uniqOld = x ^. unique
    uniqNew <- liftQuote freshUnique
    local (updateUniquesRenaming uniqOld uniqNew) $ k (x & unique .~ uniqNew)

-- | The class of things that can be renamed.
-- I.e. things that are capable of satisfying the global uniqueness condition.
class Rename a where
    renameM :: a -> RenameM a

-- | Rename a name that has a 'Unique' inside.
renameNameM :: HasUnique name => name -> RenameM name
renameNameM name = do
    let uniqOld = name ^. unique
    mayUniqNew <- lookupUnique uniqOld
    pure $ case mayUniqNew of
        Nothing      -> name
        Just uniqNew -> name & unique .~ uniqNew

instance HasUnique (tyname a) => Rename (Type tyname a) where
    renameM (TyLam ann name kind ty)    =
        withRefreshed name $ \nameFr -> TyLam ann nameFr kind <$> renameM ty
    renameM (TyForall ann name kind ty) =
        withRefreshed name $ \nameFr -> TyForall ann nameFr kind <$> renameM ty
    renameM (TyIFix ann name pat arg)   = do
        renamedArg <- renameM arg
        withRefreshed name $ \nameFr -> TyIFix ann nameFr <$> renameM pat <*> pure renamedArg
    renameM (TyApp ann fun arg)         = TyApp ann <$> renameM fun <*> renameM arg
    renameM (TyFun ann dom cod)         = TyFun ann <$> renameM dom <*> renameM cod
    renameM (TyVar ann name)            = TyVar ann <$> renameNameM name
    renameM ty@TyInt{}                  = pure ty
    renameM ty@TyBuiltin{}              = pure ty

instance (HasUnique (tyname a), HasUnique (name a)) => Rename (Term tyname name a) where
    renameM (LamAbs ann name ty body)     =
        withRefreshed name $ \nameFr ->
            LamAbs ann nameFr <$> renameM ty <*> renameM body
    renameM (IWrap ann name pat arg term) = do
        renamedArg <- rename arg
        withRefreshed name $ \nameFr ->
            IWrap ann nameFr <$> renameM pat <*> pure renamedArg <*> renameM term
    renameM (TyAbs ann name kind body)    =
        withRefreshed name $ \nameFr -> TyAbs ann nameFr kind <$> renameM body
    renameM (Apply ann fun arg)           = Apply ann <$> renameM fun <*> renameM arg
    renameM (Unwrap ann term)             = Unwrap ann <$> renameM term
    renameM (Error ann ty)                = Error ann <$> renameM ty
    renameM (TyInst ann body ty)          = TyInst ann <$> renameM body <*> renameM ty
    renameM (Var ann name)                = Var ann <$> renameNameM name
    renameM con@Constant{}                = pure con

instance (HasUnique (tyname a), HasUnique (name a)) => Rename (Program tyname name a) where
    renameM (Program ann ver term) = Program ann ver <$> renameM term
