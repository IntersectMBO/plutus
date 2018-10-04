{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings   #-}

module Language.PlutusCore.TypeSynthesis ( typecheckProgram
                                         , typecheckTerm
                                         , kindCheck
                                         , normalizeType
                                         , runTypeCheckM
                                         , extractFix
                                         , TypeCheckM
                                         , BuiltinTable (..)
                                         , TypeError (..)
                                         , TypeCheckCfg (..)
                                         ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Class
import           Control.Monad.Trans.State      hiding (get, modify)
import qualified Data.IntMap.Strict             as IM
import qualified Data.Map                       as M
import           Language.PlutusCore.Clone
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer.Type hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           Lens.Micro
import           PlutusPrelude

-- | A builtin table contains the kinds of builtin types and the types of
-- builtin names.
data BuiltinTable = BuiltinTable (M.Map TypeBuiltin (Kind ())) (M.Map BuiltinName (NormalizedType TyNameWithKind ()))

type TypeSt = IM.IntMap (NormalizedType TyNameWithKind ())

data TypeConfig = TypeConfig { _reduce   :: Bool -- ^ Whether we reduce type annotations
                             , _builtins :: BuiltinTable -- ^ Builtin types
                             }

data TypeCheckSt = TypeCheckSt { _uniqueLookup :: TypeSt
                               , _gas          :: Natural
                               }

data TypeCheckCfg = TypeCheckCfg { _cfgGas       :: Natural -- ^ Gas to be provided to the typechecker
                                 , _cfgNormalize :: Bool -- ^ Whether we should reduce type annotations
                                 }

uniqueLookup :: Lens' TypeCheckSt TypeSt
uniqueLookup f s = fmap (\x -> s { _uniqueLookup = x }) (f (_uniqueLookup s))

gas :: Lens' TypeCheckSt Natural
gas f s = fmap (\x -> s { _gas = x }) (f (_gas s))

-- | The type checking monad contains the 'BuiltinTable' and it lets us throw
-- 'TypeError's.
type TypeCheckM a = StateT TypeCheckSt (ReaderT TypeConfig (ExceptT (TypeError a) Quote))

isType :: Kind a -> Bool
isType Type{} = True
isType _      = False

-- | Create a new 'Type' for an integer operation.
intop :: (MonadQuote m) => m (NormalizedType TyNameWithKind ())
intop = do
    nam <- newTyName (Size ())
    let ity = TyApp () (TyBuiltin () TyInteger) (TyVar () nam)
        fty = TyFun () ity (TyFun () ity ity)
    pure $ NormalizedType $ TyForall () nam (Size ()) fty

-- | Create a new 'Type' for an integer relation
intRel :: (MonadQuote m)  => m (NormalizedType TyNameWithKind ())
intRel = NormalizedType <$> builtinRel TyInteger

bsRel :: (MonadQuote m) => m (NormalizedType TyNameWithKind ())
bsRel = NormalizedType <$> builtinRel TyByteString

-- | Create a dummy 'TyName'
newTyName :: (MonadQuote m) => Kind () -> m (TyNameWithKind ())
newTyName k = do
    u <- nameUnique . unTyName <$> liftQuote (freshTyName () "a")
    pure $ TyNameWithKind (TyName (Name ((), k) "a" u))

boolean :: MonadQuote m => m (Type TyNameWithKind ())
boolean = do
    nam <- newTyName (Type ())
    let var = TyVar () nam
    pure $ TyForall () nam (Type ()) (TyFun () var (TyFun () var var))

builtinRel :: (MonadQuote m) => TypeBuiltin -> m (Type TyNameWithKind ())
builtinRel bi = do
    nam <- newTyName (Size ())
    b <- boolean
    let ity = TyApp () (TyBuiltin () bi) (TyVar () nam)
        fty = TyFun () ity (TyFun () ity b)
    pure $ TyForall () nam (Size ()) fty

txHash :: NormalizedType TyNameWithKind ()
txHash = NormalizedType $ TyApp () (TyBuiltin () TyByteString) (TyInt () 256)

defaultTable :: (MonadQuote m) => m BuiltinTable
defaultTable = do

    let tyTable = M.fromList [ (TyByteString, KindArrow () (Size ()) (Type ()))
                             , (TySize      , KindArrow () (Size ()) (Type ()))
                             , (TyInteger   , KindArrow () (Size ()) (Type ()))
                             ]
        intTypes = [ AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, RemainderInteger ]
        intRelTypes = [ LessThanInteger, LessThanEqInteger, GreaterThanInteger, GreaterThanEqInteger, EqInteger ]

    is <- repeatM (length intTypes) intop
    irs <- repeatM (length intRelTypes) intRel
    bsRelType <- bsRel

    let f = M.fromList .* zip
        termTable = f intTypes is <> f intRelTypes irs <> f [TxHash, EqByteString] [txHash, bsRelType]

    pure $ BuiltinTable tyTable termTable

-- | Type-check a program, returning a normalized type.
typecheckProgram :: (MonadError (Error a) m, MonadQuote m)
                 => TypeCheckCfg
                 -> Program TyNameWithKind NameWithType a
                 -> m (NormalizedType TyNameWithKind ())
typecheckProgram cfg (Program _ _ t) = typecheckTerm cfg t

-- | Type-check a term, returning a normalized type.
typecheckTerm :: (MonadError (Error a) m, MonadQuote m)
              => TypeCheckCfg
              -> Term TyNameWithKind NameWithType a
              -> m (NormalizedType TyNameWithKind ())
typecheckTerm cfg t = convertErrors asError $ runTypeCheckM cfg (typeOf t)

-- | Kind-check a PLC type.
kindCheck :: (MonadError (Error a) m, MonadQuote m)
          => TypeCheckCfg
          -> Type TyNameWithKind a
          -> m (Kind ())
kindCheck cfg t = convertErrors asError $ runTypeCheckM cfg (kindOf t)

-- | Run the type checker with a default context.
runTypeCheckM :: TypeCheckCfg
              -> TypeCheckM a b
              -> ExceptT (TypeError a) Quote b
runTypeCheckM (TypeCheckCfg i n) tc = do
    table <- defaultTable
    runReaderT (evalStateT tc (TypeCheckSt mempty i)) (TypeConfig n table)

typeCheckStep :: TypeCheckM a ()
typeCheckStep = do
    (TypeCheckSt _ i) <- get
    if i == 0
        then throwError OutOfGas
        else modify (over gas (subtract 1))

-- | Extract kind information from a type.
kindOf :: Type TyNameWithKind a -> TypeCheckM a (Kind ())
kindOf TyInt{} = pure (Size ())
kindOf (TyFun x ty' ty'') = do
    k <- kindOf ty'
    k' <- kindOf ty''
    if isType k && isType k'
        then pure (Type ())
        else
            if isType k
                then throwError (KindMismatch x (void ty'') k' (Type ()))
                else throwError (KindMismatch x (void ty') k (Type ()))
kindOf (TyForall x _ _ ty) = do
    k <- kindOf ty
    if isType k
        then pure (Type ())
        else throwError (KindMismatch x (void ty) (Type ()) k)
kindOf (TyLam _ _ k ty) =
    [ KindArrow () (void k) k' | k' <- kindOf ty ]
kindOf (TyVar _ (TyNameWithKind (TyName (Name (_, k) _ _)))) = pure (void k)
kindOf (TyBuiltin _ b) = do
    (TypeConfig _ (BuiltinTable tyst _)) <- ask
    case M.lookup b tyst of
        Just k -> pure k
        _      -> throwError InternalError
kindOf (TyFix x _ ty) = do
    k <- kindOf ty
    if isType k
        then pure (Type ())
        else throwError (KindMismatch x (void ty) (Type ()) k)
kindOf (TyApp x ty ty') = do
    k <- kindOf ty
    case k of
        KindArrow _ k' k'' -> do
            k''' <- kindOf ty'
            typeCheckStep
            if k' == k'''
                then pure k''
                else throwError (KindMismatch x (void ty') k'' k''')
        _ -> throwError (KindMismatch x (void ty') (KindArrow () (Type ()) (Type ())) k)

intApp :: Type a () -> Natural -> Type a ()
intApp ty n = TyApp () ty (TyInt () n)

integerType :: Natural -> NormalizedType a ()
integerType = NormalizedType . intApp (TyBuiltin () TyInteger)

bsType :: Natural -> NormalizedType a ()
bsType = NormalizedType . intApp (TyBuiltin () TyByteString)

sizeType :: Natural -> NormalizedType a ()
sizeType = NormalizedType . intApp (TyBuiltin () TySize)

dummyUnique :: Unique
dummyUnique = Unique 0

dummyTyName :: TyNameWithKind ()
dummyTyName = TyNameWithKind (TyName (Name ((), Type ()) "*" dummyUnique))

dummyKind :: Kind ()
dummyKind = Type ()

dummyType :: Type TyNameWithKind ()
dummyType = TyVar () dummyTyName

-- This works using type environments to handle substitutions efficiently. We
-- keep a type environment which holds all substitutions which should be in
-- scope at any given momeny. After any lookups, we clone the looked-up type in
-- order to maintain global uniqueness.
--
-- This is all tracked in a state monad, and we simply delete any substitutions
-- once they go out of scope; this is permissible since 'Unique's are globally
-- unique and so we will not delete the wrong thing.
--
-- | Synthesize the type of a term, returning a normalized type.
typeOf :: Term TyNameWithKind NameWithType a -> TypeCheckM a (NormalizedType TyNameWithKind ())
typeOf (Var _ (NameWithType (Name (_, ty) _ _))) = normalizeTypeOpt $ void ty
typeOf (LamAbs _ _ ty t)                         =
    TyFun () <<$>> normalizeTypeOpt (void ty) <<*>> typeOf t
typeOf (Error x ty)                              = do
    k <- kindOf ty
    case k of
        Type{} -> normalizeType (void ty)
        _      -> throwError (KindMismatch x (void ty) (Type ()) k)
typeOf (TyAbs _ n k t)                           = TyForall () (void n) (void k) <<$>> typeOf t
typeOf (Constant _ (BuiltinName _ n)) = do
    (TypeConfig _ (BuiltinTable _ st)) <- ask
    case M.lookup n st of
        Just k -> pure k
        _      -> throwError InternalError
typeOf (Constant _ (BuiltinInt _ n _))           = pure (integerType n)
typeOf (Constant _ (BuiltinBS _ n _))            = pure (bsType n)
typeOf (Constant _ (BuiltinSize _ n))            = pure (sizeType n)
typeOf (Apply x fun arg) = do
    nFunTy <- typeOf fun
    case getNormalizedType nFunTy of
        TyFun _ inTy outTy -> do
            nArgTy <- typeOf arg
            typeCheckStep
            if inTy == getNormalizedType nArgTy
                then pure $ NormalizedType outTy -- subpart of a normalized type, so normalized
                else throwError (TypeMismatch x (void arg) inTy nArgTy)
        _ -> throwError (TypeMismatch x (void fun) (TyFun () dummyType dummyType) nFunTy)
typeOf (TyInst x body ty) = do
    nBodyTy <- typeOf body
    case getNormalizedType nBodyTy of
        TyForall _ n k absTy -> do
            nTy <- normalizeTypeOpt $ void ty
            k' <- kindOf ty
            typeCheckStep
            if k == k'
                then normalizeTypeBinder n nTy absTy
                else throwError (KindMismatch x (void ty) k k')
        _ -> throwError (TypeMismatch x (void body) (TyForall () dummyTyName dummyKind dummyType) nBodyTy)
typeOf (Unwrap x body) = do
    nBodyTy <- typeOf body
    case getNormalizedType nBodyTy of
        TyFix _ n fixTy ->
            normalizeTypeBinder n nBodyTy fixTy
        _             -> throwError (TypeMismatch x (void body) (TyFix () dummyTyName dummyType) nBodyTy)
typeOf (Wrap x n ty t) = do
    nTy <- normalizeType $ void ty
    nTermTy <- typeOf t
    typeCheckStep
    nTermTy' <- normalizeTypeBinder (void n) (TyFix () (void n) <$> nTy) $ getNormalizedType nTy
    if nTermTy == nTermTy'
        then pure $ TyFix () (void n) <$> nTy
        else throwError (TypeMismatch x (void t) (getNormalizedType nTermTy') nTermTy)

normalizeTypeBinder
    :: TyNameWithKind ()
    -> NormalizedType TyNameWithKind ()
    -> Type TyNameWithKind ()
    -> TypeCheckM err (NormalizedType TyNameWithKind ())
normalizeTypeBinder n ty ty' = do
    let u = extractUnique n
    tyEnvAssign u ty
    normalizeType ty' <* tyEnvDelete u

extractUnique :: TyNameWithKind a -> Unique
extractUnique = nameUnique . unTyName . unTyNameWithKind

-- This works because names are globally unique
tyEnvDelete :: MonadState TypeCheckSt m
            => Unique
            -> m ()
tyEnvDelete (Unique i) = modify (over uniqueLookup (IM.delete i))

tyEnvAssign :: MonadState TypeCheckSt m
            => Unique
            -> NormalizedType TyNameWithKind ()
            -> m ()
tyEnvAssign (Unique i) ty = modify (over uniqueLookup (IM.insert i ty))

-- Given a type Q, we extract (a, S) such that Q = E(fix a S)
extractFix :: Type TyNameWithKind () -- ^ Q
           -> TypeCheckM a (TyNameWithKind(), Type TyNameWithKind ()) -- ^ (a, S)
extractFix _ = undefined

normalizeTypeOpt :: Type TyNameWithKind () -> TypeCheckM a (NormalizedType TyNameWithKind ())
normalizeTypeOpt ty = do
    TypeConfig norm _ <- ask
    if norm
        then normalizeType ty
        else pure $ NormalizedType ty

-- | Normalize a 'Type'.
normalizeType :: Type TyNameWithKind () -> TypeCheckM err (NormalizedType TyNameWithKind ())
normalizeType (TyForall x tn k ty) = TyForall x tn k <<$>> normalizeType ty
normalizeType (TyFix x tn ty)      = TyFix x tn <<$>> normalizeType ty
normalizeType (TyFun x ty ty')     = TyFun x <<$>> normalizeType ty <<*>> normalizeType ty'
normalizeType (TyLam x tn k ty)    = TyLam x tn k <<$>> normalizeType ty
normalizeType (TyApp x fun arg)    = do
    nFun <- normalizeType fun
    nArg <- normalizeType arg
    case getNormalizedType nFun of
        TyLam _ name _ body -> normalizeTypeBinder name nArg body
        _                   -> pure $ TyApp x <$> nFun <*> nArg
normalizeType ty@(TyVar _ (TyNameWithKind (TyName (Name _ _ u)))) = do
    (TypeCheckSt st _) <- get
    case IM.lookup (unUnique u) st of
        Just ty' -> traverse cloneType ty'
        Nothing  -> pure $ NormalizedType ty

normalizeType ty@TyInt{}     = pure $ NormalizedType ty
normalizeType ty@TyBuiltin{} = pure $ NormalizedType ty
