{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings   #-}

module Language.PlutusCore.TypeSynthesis ( typecheckProgram
                                         , typecheckTerm
                                         , kindCheck
                                         , TypeCheckM
                                         , BuiltinTable (..)
                                         , TypeError (..)
                                         ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Class
import           Control.Monad.Trans.State.Strict hiding (get, modify)
import           Data.Functor.Foldable
import qualified Data.Map                         as M
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

-- | The type checking monad contains the 'BuiltinTable' and it lets us throw
-- 'TypeError's.
type TypeCheckM a = StateT Natural (ReaderT BuiltinTable (Either (TypeError a)))

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

-- | Type-check a PLC program, returning the inferred normalized type.
typecheckProgram :: (MonadError (Error a) m, MonadQuote m) => Natural -> Program TyNameWithKind NameWithType a -> m (NormalizedType TyNameWithKind a)
typecheckProgram n (Program _ _ t) = typecheckTerm n t

-- | Type-check a PLC term, returning the inferred normalized type.
typecheckTerm :: (MonadError (Error a) m, MonadQuote m) => Natural -> Term TyNameWithKind NameWithType a -> m (NormalizedType TyNameWithKind a)
typecheckTerm n t = convertErrors asError $ runTypeCheckM n (typeOf t)

-- | Kind-check a PLC term.
kindCheck :: (MonadError (Error a) m, MonadQuote m) => Natural -> Type TyNameWithKind a -> m (Kind a)
kindCheck n t = convertErrors asError $ runTypeCheckM n (kindOf t)

-- | Run the type checker with a default context.
runTypeCheckM :: (MonadError (TypeError a) m, MonadQuote m)
              => Natural -- ^ Amount of gas to provide typechecker
              -> TypeCheckM a b
              -> m b
runTypeCheckM i tc = do
    table <- defaultTable
    liftEither $ fst <$> runReaderT (runStateT tc i) table

typeCheckStep :: TypeCheckM a ()
typeCheckStep = do
    i <- get
    if i == 0
        then throwError OutOfGas
        else modify (subtract 1)

-- | Extract kind information from a type.
kindOf :: Type TyNameWithKind a -> TypeCheckM a (Kind a)
kindOf (TyInt x _) = pure (Size x)
kindOf (TyFun x ty' ty'') = do
    k <- kindOf ty'
    k' <- kindOf ty''
    if isType k && isType k'
        then pure (Type x)
        else
            if isType k
                then throwError (KindMismatch x ty'' k' (Type x))
                else throwError (KindMismatch x ty' k (Type x))
kindOf (TyForall x _ _ ty) = do
    k <- kindOf ty
    if isType k
        then pure (Type x)
        else throwError (KindMismatch x ty (Type x) k)
kindOf (TyLam x _ k ty) =
    [ KindArrow x k k' | k' <- kindOf ty ]
kindOf (TyVar _ (TyNameWithKind (TyName (Name (_, k) _ _)))) = pure k
kindOf (TyBuiltin x b) = do
    (BuiltinTable tyst _) <- ask
    case M.lookup b tyst of
        Just k -> pure $ x <$ k
        _      -> throwError InternalError
kindOf (TyFix x _ ty) = do
    k <- kindOf ty
    if isType k
        then pure (Type x)
        else throwError (KindMismatch x ty (Type x) k)
kindOf (TyApp x ty ty') = do
    k <- kindOf ty
    case k of
        KindArrow _ k' k'' -> do
            k''' <- kindOf ty'
            typeCheckStep
            if void k' == void k'''
                then pure k''
                else throwError (KindMismatch x ty' k'' k''') -- this is the branch that fails!
        _ -> throwError (KindMismatch x ty' (KindArrow x (Type x) (Type x)) k)

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
typeOf :: Term TyNameWithKind NameWithType a -> TypeCheckM a (NormalizedType TyNameWithKind a)
typeOf (Var _ (NameWithType (Name (_, ty) _ _))) = pure (NormalizedType ty) -- annotations on types must be normalized
typeOf (LamAbs x _ ty t)                         = NormalizedType <$> (TyFun x ty <$> (getNormalizedType <$> typeOf t))
typeOf (Error x ty)                              = do
    k <- kindOf ty
    case k of
        Type{} -> pure (NormalizedType ty) -- annotations on types must be normalized
        _      -> throwError (KindMismatch x ty (Type x) k)
typeOf (TyAbs x n k t)                           = NormalizedType <$> (TyForall x n k <$> (getNormalizedType <$> typeOf t))
typeOf (Constant x (BuiltinName _ n)) = do
    (BuiltinTable _ st) <- ask
    case M.lookup n st of
        Just k -> pure $ x <$ k
        _      -> throwError InternalError
typeOf (Constant x (BuiltinInt _ n _))           = pure (x <$ integerType n)
typeOf (Constant x (BuiltinBS _ n _))            = pure (x <$ bsType n)
typeOf (Constant x (BuiltinSize _ n))            = pure (x <$ sizeType n)
typeOf (Apply x fun arg) = do
    nFunTy@(NormalizedType funTy) <- typeOf fun
    case funTy of
        TyFun _ inTy outTy -> do
            nArgTy@(NormalizedType argTy) <- typeOf arg
            typeCheckStep
            if void inTy == void argTy
                then pure $ NormalizedType outTy -- subpart of a normalized type, so normalized
                else throwError (TypeMismatch x arg inTy nArgTy)
        _ -> throwError (TypeMismatch x fun (TyFun x (x <$ dummyType) (x <$ dummyType)) nFunTy)
typeOf (TyInst x body ty) = do
    nBodyTy@(NormalizedType bodyTy) <- typeOf body
    case bodyTy of
        TyForall _ n k absTy -> do
            k' <- kindOf ty
            typeCheckStep
            if void k == void k'
                then pure (tyReduce (tySubstitute (extractUnique n) (NormalizedType ty) (NormalizedType absTy)))
                else throwError (KindMismatch x ty k k')
        _ -> throwError (TypeMismatch x body (TyForall x (x <$ dummyTyName) (x <$ dummyKind) (x <$ dummyType)) nBodyTy)
typeOf (Unwrap x body) = do
    nBodyTy@(NormalizedType bodyTy) <- typeOf body
    case bodyTy of
        TyFix _ n fixTy -> do
            let subst = tySubstitute (extractUnique n) nBodyTy (NormalizedType fixTy)
            pure (tyReduce subst)
        _             -> throwError (TypeMismatch x body (TyFix x (x <$ dummyTyName) (x <$ dummyType)) nBodyTy)
typeOf (Wrap x n ty body) = do
    nBodyTy <- typeOf body
    let fixed = tySubstitute (extractUnique n) (NormalizedType $ TyFix x n ty) (NormalizedType ty)
    typeCheckStep
    if void (tyReduce fixed) == void nBodyTy
        then pure $ NormalizedType (TyFix x n ty) -- type annotations on terms must be normalized
        else throwError (TypeMismatch x body fixed nBodyTy)

extractUnique :: TyNameWithKind a -> Unique
extractUnique = nameUnique . unTyName . unTyNameWithKind

-- TODO: make type substitutions occur in a state monad + benchmark
-- | Substitute the given type into another type. The input types must be normalized - this prevents us creating redundant work. The
-- output type is not normalized, since we may introduce new redexes.
tySubstitute :: Unique -- ^ Unique associated with type variable
             -> NormalizedType TyNameWithKind a -- ^ Type we are binding to free variable
             -> NormalizedType TyNameWithKind a -- ^ Type we are substituting in
             -> Type TyNameWithKind a
tySubstitute u (NormalizedType ty) = cata a . getNormalizedType where
    a (TyVarF _ (TyNameWithKind (TyName (Name _ _ u')))) | u == u' = ty
    a x                                                  = embed x

-- also this should involve contexts
-- | Reduce any redexes inside a type.
tyReduce :: Type TyNameWithKind a -> NormalizedType TyNameWithKind a
-- TODO: is this case actually safe? Don't we need to reduce again after substituting?
tyReduce (TyApp _ (TyLam _ (TyNameWithKind (TyName (Name _ _ u))) _ ty) ty') = NormalizedType $ tySubstitute u (NormalizedType ty') (tyReduce ty) -- TODO: use the substitution monad here
tyReduce (TyForall x tn k ty)                                                = NormalizedType $ TyForall x tn k (getNormalizedType $ tyReduce ty)
tyReduce (TyFun x ty ty') | isTypeValue ty                                   = NormalizedType $ TyFun x (getNormalizedType $ tyReduce ty) (getNormalizedType $ tyReduce ty')
                          | otherwise                                        = NormalizedType $ TyFun x (getNormalizedType $ tyReduce ty) ty'
tyReduce (TyLam x tn k ty)                                                   = NormalizedType $ TyLam x tn k (getNormalizedType $ tyReduce ty)
tyReduce (TyApp x ty ty') | isTypeValue ty                                   = NormalizedType $ TyApp x (getNormalizedType $ tyReduce ty) (getNormalizedType $ tyReduce ty')
                          | otherwise                                        = NormalizedType $ TyApp x (getNormalizedType $ tyReduce ty) ty'
tyReduce x                                                                   = NormalizedType x
