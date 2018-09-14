{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MonadComprehensions  #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}

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
import           Data.Functor.Foldable.Monadic
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
data BuiltinTable = BuiltinTable (M.Map TypeBuiltin (Kind ())) (M.Map BuiltinName (Type TyNameWithKind ()))

-- | The type checking monad contains the 'BuiltinTable' and it lets us throw
-- 'TypeError's.
type TypeCheckM a = StateT Natural (ReaderT BuiltinTable (ExceptT (TypeError a) Quote))

instance MonadQuote (TypeCheckM a) where

isType :: Kind a -> Bool
isType Type{} = True
isType _      = False

-- | Create a new 'Type' for an integer operation.
intop :: (MonadQuote m) => m (Type TyNameWithKind ())
intop = do
    nam <- newTyName (Size ())
    let ity = TyApp () (TyBuiltin () TyInteger) (TyVar () nam)
        fty = TyFun () ity (TyFun () ity ity)
    pure $ TyForall () nam (Size ()) fty

-- | Create a new 'Type' for an integer relation
intRel :: (MonadQuote m)  => m (Type TyNameWithKind ())
intRel = builtinRel TyInteger

bsRel :: (MonadQuote m) => m (Type TyNameWithKind ())
bsRel = builtinRel TyByteString

-- | Create a dummy 'TyName'
newTyName :: (MonadQuote m) => Kind () -> m (TyNameWithKind ())
newTyName k = do
    u <- liftQuote freshUnique
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

txHash :: Type TyNameWithKind ()
txHash = TyApp () (TyBuiltin () TyByteString) (TyInt () 256)

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
        termTable = f intTypes is <> f intRelTypes irs <> f [TxHash, EqByteString ] [txHash, bsRelType ]

    pure $ BuiltinTable tyTable termTable

-- | Type-check a PLC program.
typecheckProgram :: (MonadError (Error a) m, MonadQuote m) => Natural -> Program TyNameWithKind NameWithType a -> m (Type TyNameWithKind ())
typecheckProgram n (Program _ _ t) = typecheckTerm n t

-- | Type-check a PLC term.
typecheckTerm :: (MonadError (Error a) m, MonadQuote m) => Natural -> Term TyNameWithKind NameWithType a -> m (Type TyNameWithKind ())
typecheckTerm n t = convertErrors asError $ runTypeCheckM n (typeOf t)

-- | Kind-check a PLC term.
kindCheck :: (MonadError (Error a) m, MonadQuote m) => Natural -> Type TyNameWithKind a -> m (Kind ())
kindCheck n t = convertErrors asError $ runTypeCheckM n (kindOf t)

-- | Run the type checker with a default context.
runTypeCheckM :: Natural -- ^ Amount of gas to provide typechecker
              -> TypeCheckM a b
              -> ExceptT (TypeError a) Quote b
runTypeCheckM i tc = do
    table <- defaultTable
    runReaderT (evalStateT tc i) table

typeCheckStep :: TypeCheckM a ()
typeCheckStep = do
    i <- get
    if i == 0
        then throwError OutOfGas
        else modify (subtract 1)

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
    (BuiltinTable tyst _) <- ask
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
                else throwError (KindMismatch x (void ty') k'' k''') -- this is the branch that fails!
        _ -> throwError (KindMismatch x (void ty') (KindArrow () (Type ()) (Type ())) k)

intApp :: Type a () -> Natural -> Type a ()
intApp ty n = TyApp () ty (TyInt () n)

integerType :: Natural -> Type a ()
integerType = intApp (TyBuiltin () TyInteger)

bsType :: Natural -> Type a ()
bsType = intApp (TyBuiltin () TyByteString)

sizeType :: Natural -> Type a ()
sizeType = intApp (TyBuiltin () TySize)

dummyUnique :: Unique
dummyUnique = Unique 0

dummyTyName :: TyNameWithKind ()
dummyTyName = TyNameWithKind (TyName (Name ((), Type ()) "*" dummyUnique))

dummyKind :: Kind ()
dummyKind = Type ()

dummyType :: Type TyNameWithKind ()
dummyType = TyVar () dummyTyName

-- | Extract type of a term.
typeOf :: Term TyNameWithKind NameWithType a -> TypeCheckM a (Type TyNameWithKind ())
typeOf (Var _ (NameWithType (Name (_, ty) _ _))) = pure (void ty)
typeOf (LamAbs _ _ ty t)                         = TyFun () (void ty) <$> typeOf t
typeOf (Error x ty)                              = do
    k <- kindOf ty
    case k of
        Type{} -> pure (void ty)
        _      -> throwError (KindMismatch x (void ty) (Type ()) k)
typeOf (TyAbs _ n k t)                           = TyForall () (void n) (void k) <$> typeOf t
typeOf (Constant _ (BuiltinName _ n)) = do
    (BuiltinTable _ st) <- ask
    case M.lookup n st of
        Just k -> pure k
        _      -> throwError InternalError
typeOf (Constant _ (BuiltinInt _ n _))           = pure (integerType n)
typeOf (Constant _ (BuiltinBS _ n _))            = pure (bsType n)
typeOf (Constant _ (BuiltinSize _ n))            = pure (sizeType n)
typeOf (Apply x t t') = do
    ty <- typeOf t
    case ty of
        TyFun _ ty' ty'' -> do
            ty''' <- typeOf t'
            if ty' == ty'''
                then pure ty''
                else throwError (TypeMismatch x (void t') ty' ty''')
        _ -> throwError (TypeMismatch x (void t) (TyFun () dummyType dummyType) ty)
typeOf (TyInst x t ty) = do
    ty' <- typeOf t
    case ty' of
        TyForall _ n k ty'' -> do
            k' <- kindOf ty
            typeCheckStep
            if k == k'
                then tyReduce =<< tySubstitute (extractUnique n) (void ty) ty''
                else throwError (KindMismatch x (void ty) k k')
        _ -> throwError (TypeMismatch x (void t) (TyForall () dummyTyName dummyKind dummyType) (void ty'))
typeOf (Unwrap x t) = do
    ty <- typeOf t
    case ty of
        TyFix _ n ty' -> do
            subst <- tySubstitute (extractUnique n) ty ty'
            typeCheckStep
            tyReduce subst
        _             -> throwError (TypeMismatch x (void t) (TyFix () dummyTyName dummyType) (void ty))
typeOf (Wrap x n ty t) = do
    ty' <- typeOf t
    fixed <- tySubstitute (extractUnique n) (TyFix () (void n) (void ty)) (void ty)
    typeCheckStep
    red <- tyReduce fixed
    if red == ty'
        then pure (TyFix () (void n) (void ty))
        else throwError (TypeMismatch x (void t) fixed (void ty'))

extractUnique :: TyNameWithKind a -> Unique
extractUnique = nameUnique . unTyName . unTyNameWithKind

fixUniversals :: MonadQuote m => Type TyNameWithKind a -> m (Type TyNameWithKind a)
fixUniversals = cataM a where
    a (TyForallF x tn@(TyNameWithKind (TyName (Name x' s _))) k ty) = do
        u <- liftQuote freshUnique
        let tn' = TyNameWithKind (TyName (Name x' s u))
        TyForall x tn' k <$> tySubstitute (extractUnique tn) (TyVar (fst x') tn') ty
    a x = pure (embed x)

-- TODO: make type substitutions occur in a state monad + benchmark
tySubstitute :: MonadQuote m
             => Unique -- ^ Unique associated with type variable
             -> Type TyNameWithKind a -- ^ Type we are binding to free variable
             -> Type TyNameWithKind a -- ^ Type we are substituting in
             -> m (Type TyNameWithKind a)
tySubstitute u ty = cataM a where
    a (TyVarF _ (TyNameWithKind (TyName (Name _ _ u')))) | u == u' = fixUniversals ty
    a x                                                  = pure (embed x)

-- also this should involve contexts
tyReduce :: MonadQuote m => Type TyNameWithKind a -> m (Type TyNameWithKind a)
tyReduce (TyApp _ (TyLam _ (TyNameWithKind (TyName (Name _ _ u))) _ ty) ty') = tySubstitute u ty' =<< tyReduce ty -- TODO: use the substitution monad here
tyReduce (TyForall x tn k ty)                                                = TyForall x tn k <$> tyReduce ty
tyReduce (TyFun x ty ty') | isTypeValue ty                                   = TyFun x <$> tyReduce ty <*> tyReduce ty'
                          | otherwise                                        = TyFun x <$> tyReduce ty <*> pure ty'
tyReduce (TyLam x tn k ty)                                                   = TyLam x tn k <$> tyReduce ty
tyReduce (TyApp x ty ty') | isTypeValue ty                                   = TyApp x <$> tyReduce ty <*> tyReduce ty'
                          | otherwise                                        = TyApp x <$> tyReduce ty <*> pure ty'
tyReduce x                                                                   = pure x
