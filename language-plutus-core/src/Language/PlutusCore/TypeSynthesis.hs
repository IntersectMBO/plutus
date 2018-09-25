{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings   #-}

module Language.PlutusCore.TypeSynthesis ( typecheckProgram
                                         , typecheckTerm
                                         , kindCheck
                                         , tyReduce
                                         , runTypeCheckM
                                         , TypeCheckM
                                         , BuiltinTable (..)
                                         , TypeError (..)
                                         ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Class
import           Control.Monad.Trans.State      hiding (get, modify)
import qualified Data.IntMap                    as IM
import qualified Data.Map                       as M
import           Language.PlutusCore.Clone
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | A builtin table contains the kinds of builtin types and the types of
-- builtin names.
data BuiltinTable = BuiltinTable (M.Map TypeBuiltin (Kind ())) (M.Map BuiltinName (NormalizedType TyNameWithKind ()))

type TypeSt = IM.IntMap (NormalizedType TyNameWithKind ())

-- | The type checking monad contains the 'BuiltinTable' and it lets us throw
-- 'TypeError's.
type TypeCheckM a = StateT (TypeSt, Natural) (ReaderT (Bool, BuiltinTable) (ExceptT (TypeError a) Quote))

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

unit :: MonadQuote m => m (Type TyNameWithKind ())
unit =
    [ TyForall () nam (Type ()) (TyFun () (TyVar () nam) (TyVar () nam)) | nam <- newTyName (Type ()) ]

boolean :: MonadQuote m => m (Type TyNameWithKind ())
boolean = do
    nam <- newTyName (Type ())
    (u, u') <- (,) <$> unit <*> unit
    let var = TyVar () nam
        unitVar = TyFun () u var
        unitVar' = TyFun () u' var
    pure $ TyForall () nam (Type ()) (TyFun () unitVar (TyFun () unitVar' var))

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
                             , (TySize, Size ())
                             , (TyInteger, KindArrow () (Size ()) (Type ()))
                             ]
        intTypes = [ AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, RemainderInteger ]
        intRelTypes = [ LessThanInteger, LessThanEqInteger, GreaterThanInteger, GreaterThanEqInteger, EqInteger ]

    is <- repeatM (length intTypes) intop
    irs <- repeatM (length intRelTypes) intRel
    bsRelType <- bsRel

    let f = M.fromList .* zip
        termTable = f intTypes is <> f intRelTypes irs <> f [TxHash, EqByteString] [txHash, bsRelType]

    pure $ BuiltinTable tyTable termTable

-- | Type-check a PLC program, returning a normalized type.
typecheckProgram :: (MonadError (Error a) m, MonadQuote m)
                 => Natural
                 -> Bool
                 -> Program TyNameWithKind NameWithType a
                 -> m (NormalizedType TyNameWithKind ())
typecheckProgram n norm (Program _ _ t) = typecheckTerm n norm t

-- | Type-check a PLC term, returning a normalized type.
typecheckTerm :: (MonadError (Error a) m, MonadQuote m)
              => Natural
              -> Bool
              -> Term TyNameWithKind NameWithType a
              -> m (NormalizedType TyNameWithKind ())
typecheckTerm n norm t = convertErrors asError $ runTypeCheckM n norm (typeOf t)

-- | Kind-check a PLC type.
kindCheck :: (MonadError (Error a) m, MonadQuote m)
          => Natural
          -> Bool
          -> Type TyNameWithKind a
          -> m (Kind ())
kindCheck n norm t = convertErrors asError $ runTypeCheckM n norm (kindOf t)

-- | Run the type checker with a default context.
runTypeCheckM :: Natural -- ^ Amount of gas to provide typechecker
              -> Bool -- ^ Whether to normalize types
              -> TypeCheckM a b
              -> ExceptT (TypeError a) Quote b
runTypeCheckM i n tc = do
    table <- defaultTable
    runReaderT (evalStateT tc (mempty, i)) (n, table)

typeCheckStep :: TypeCheckM a ()
typeCheckStep = do
    (_, i) <- get
    if i == 0
        then throwError OutOfGas
        else modify (second (subtract 1))

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
    (_, BuiltinTable tyst _) <- ask
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

-- | Extract type of a term. The resulting type is normalized.
typeOf :: Term TyNameWithKind NameWithType a -> TypeCheckM a (NormalizedType TyNameWithKind ())
typeOf (Var _ (NameWithType (Name (_, ty) _ _))) = do
    (norm, _) <- ask
    maybeRed norm (void ty)
typeOf (LamAbs _ _ ty t)                         = do
    (norm, _) <- ask
    (NormalizedType ty') <- maybeRed norm (void ty)
    NormalizedType <$> (TyFun () ty' <$> (getNormalizedType <$> typeOf t))
typeOf (Error x ty)                              = do
    k <- kindOf ty
    case k of
        Type{} -> pure (void $ NormalizedType ty)
        _      -> throwError (KindMismatch x (void ty) (Type ()) k)
typeOf (TyAbs _ n k t)                           = NormalizedType <$> (TyForall () (void n) (void k) <$> (getNormalizedType <$> typeOf t))
typeOf (Constant _ (BuiltinName _ n)) = do
    (_, BuiltinTable _ st) <- ask
    case M.lookup n st of
        Just k -> pure k
        _      -> throwError InternalError
typeOf (Constant _ (BuiltinInt _ n _))           = pure (integerType n)
typeOf (Constant _ (BuiltinBS _ n _))            = pure (bsType n)
typeOf (Constant _ (BuiltinSize _ n))            = pure (sizeType n)
typeOf (Apply x fun arg) = do
    nFunTy@(NormalizedType funTy) <- typeOf fun
    case funTy of
        TyFun _ inTy outTy -> do
            nArgTy@(NormalizedType argTy) <- typeOf arg
            typeCheckStep
            if inTy == argTy
                then pure $ NormalizedType outTy -- subpart of a normalized type, so normalized
                else throwError (TypeMismatch x (void arg) inTy nArgTy)
        _ -> throwError (TypeMismatch x (void fun) (TyFun () dummyType dummyType) nFunTy)
typeOf (TyInst x body ty) = do
    nBodyTy@(NormalizedType bodyTy) <- typeOf body
    case bodyTy of
        TyForall _ n k absTy -> do
            k' <- kindOf ty
            typeCheckStep
            if k == k'
                then do
                    tyEnvAssign (extractUnique n) (void $ NormalizedType ty)
                    tyReduce absTy
                else throwError (KindMismatch x (void ty) k k')
        _ -> throwError (TypeMismatch x (void body) (TyForall () dummyTyName dummyKind dummyType) nBodyTy)
typeOf (Unwrap x body) = do
    nBodyTy@(NormalizedType bodyTy) <- typeOf body
    case bodyTy of
        TyFix _ n fixTy -> do
            tyEnvAssign (extractUnique n) nBodyTy
            tyReduce fixTy
        _             -> throwError (TypeMismatch x (void body) (TyFix () dummyTyName dummyType) nBodyTy)
typeOf (Wrap x n ty body) = do
    nBodyTy <- typeOf body
    tyEnvAssign (extractUnique n) (NormalizedType $ TyFix () (void n) (void ty))
    typeCheckStep
    red <- tyReduce (void ty)
    if red == nBodyTy
        then pure $ NormalizedType (TyFix () (void n) (void ty))
        else throwError (TypeMismatch x (void body) (getNormalizedType red) nBodyTy)

extractUnique :: TyNameWithKind a -> Unique
extractUnique = nameUnique . unTyName . unTyNameWithKind

tyEnvAssign :: MonadState (TypeSt, Natural) m
            => Unique
            -> NormalizedType TyNameWithKind ()
            -> m ()
tyEnvAssign (Unique i) ty = modify (first (IM.insert i ty))

isTyLam :: Type TyNameWithKind () -> Bool
isTyLam TyLam{} = True
isTyLam _       = False

maybeRed :: Bool -> Type TyNameWithKind () -> TypeCheckM a (NormalizedType TyNameWithKind ())
maybeRed True  = tyReduce
maybeRed False = pure . NormalizedType

-- | Reduce any redexes inside a type.
tyReduce :: Type TyNameWithKind () -> TypeCheckM a (NormalizedType TyNameWithKind ())
tyReduce (TyApp _ (TyLam _ (TyNameWithKind (TyName (Name _ _ u))) _ ty) ty') =
    tyEnvAssign u (NormalizedType (void ty')) *>
    tyReduce ty
tyReduce (TyForall x tn k ty)                                                = NormalizedType <$> (TyForall x tn k <$> (getNormalizedType <$> tyReduce ty))
tyReduce (TyFun x ty ty') | isTypeValue ty                                   = NormalizedType <$> (TyFun x <$> (getNormalizedType <$> tyReduce ty) <*> (getNormalizedType <$> tyReduce ty'))
                          | otherwise                                        = NormalizedType <$> (TyFun x <$> (getNormalizedType <$> tyReduce ty) <*> pure ty')
tyReduce (TyLam x tn k ty)                                                   = NormalizedType <$> (TyLam x tn k <$> (getNormalizedType <$> tyReduce ty))
tyReduce (TyApp x ty ty') = do

    let modTy = if isTypeValue ty
        then fmap getNormalizedType . tyReduce
        else pure

    tyRed <- getNormalizedType <$> tyReduce ty
    let preTy = TyApp x tyRed <$> modTy ty' -- FIXME: shouldn't such reductions happen one-at-a-time?

    if isTyLam tyRed
        then tyReduce =<< preTy
        else NormalizedType <$> preTy

tyReduce ty@(TyVar _ (TyNameWithKind (TyName (Name _ _ u)))) = do
    (st, _) <- get
    case IM.lookup (unUnique u) st of
        Just ty' -> NormalizedType <$> cloneType (getNormalizedType ty')
        Nothing  -> pure $ NormalizedType ty
tyReduce x                                                                   = pure $ NormalizedType x
