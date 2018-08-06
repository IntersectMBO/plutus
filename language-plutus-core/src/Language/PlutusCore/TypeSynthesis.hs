{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings   #-}

module Language.PlutusCore.TypeSynthesis ( kindOf
                                         , typeOf
                                         , runTypeCheckM
                                         , TypeError (..)
                                         ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Class
import           Control.Monad.Trans.State      hiding (get, modify)
import           Data.Functor.Foldable
import qualified Data.Map                       as M
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | A builtin table contains the kinds of builtin types and the types of
-- builtin names.
data BuiltinTable = BuiltinTable (M.Map TypeBuiltin (Kind ())) (M.Map BuiltinName (Type TyNameWithKind ()))

-- | The type checking monad contains the 'BuiltinTable' and it lets us throw
-- 'TypeError's.
type TypeCheckM a = StateT Natural (ReaderT BuiltinTable (Either (TypeError a)))

data TypeError a = InternalError -- ^ This is thrown if builtin lookup fails
                 | KindMismatch a (Type TyNameWithKind ()) (Kind ()) (Kind ())
                 | TypeMismatch a (Term TyNameWithKind NameWithType ()) (Type TyNameWithKind ()) (Type TyNameWithKind ())
                 | OutOfGas

instance Pretty a => Pretty (TypeError a) where
    pretty InternalError    = "Internal error."
    pretty (KindMismatch x ty k k') = "Kind mismatch at" <+> pretty x <+> "in type" <+> squotes (pretty ty) <> ". Expected kind" <+> squotes (pretty k) <+> ", found kind" <+> squotes (pretty k')
    pretty (TypeMismatch x t ty ty') = "Type mismatch at" <+> pretty x <+> "in term" <+> squotes (pretty t) <> ". Expected type" <+> squotes (pretty ty) <+> ", found type" <+> squotes (pretty ty')
    pretty OutOfGas = "Type checking ran out of gas."

isType :: Kind a -> Bool
isType Type{} = True
isType _      = False

-- | Create a dummy 'TyName'
newTyName :: (MonadState Int m) => Kind () -> m (TyNameWithKind ())
newTyName k = do
    i <- get
    modify (+1)
    pure $ TyNameWithKind (TyName (Name ((), k) "" (Unique $ i+1)))

-- | Create a new 'Type' for an integer operation.
intop :: MonadState Int m => m (Type TyNameWithKind ())
intop = do
    nam <- newTyName (Size ())
    let ity = TyApp () (TyBuiltin () TyInteger) (TyVar () nam)
        fty = TyFun () ity (TyFun () ity ity)
    pure $ TyForall () nam (Size ()) fty

unit :: MonadState Int m => m (Type TyNameWithKind ())
unit =
    [ TyForall () nam (Type ()) (TyVar () nam) | nam <- newTyName (Type ()) ]

boolean :: MonadState Int m => m (Type TyNameWithKind ())
boolean = do
    nam <- newTyName (Type ())
    u <- unit
    let var = TyVar () nam
        unitVar = TyFun () u var
    pure $ TyForall () nam (Type ()) (TyFun () unitVar (TyFun () unitVar var))

-- | Create a new 'Type' for an integer relation
intRel :: MonadState Int m => m (Type TyNameWithKind ())
intRel = do
    nam <- newTyName (Size ())
    b <- boolean
    let ity = TyApp () (TyBuiltin () TyInteger) (TyVar () nam)
        fty = TyFun () ity (TyFun () ity b)
    pure $ TyForall () nam (Size ()) fty

defaultTable :: MonadState Int m => m BuiltinTable
defaultTable = do
    let tyTable = M.fromList [ (TyByteString, KindArrow () (Size ()) (Type ()))
                             , (TySize, Size ())
                             , (TyInteger, KindArrow () (Size ()) (Type ()))
                             ]
        intTypes = [ AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, RemainderInteger ]
        intRelTypes = [ LessThanInteger, LessThanEqInteger, GreaterThanInteger, GreaterThanEqInteger, EqInteger ]

    is <- replicateM (length intTypes) intop
    irs <- replicateM (length intRelTypes) intRel
    let termTable = M.fromList (zip intTypes is ++ zip intRelTypes irs)

    pure $ BuiltinTable tyTable termTable

-- | Run the type checker with a default context.
runTypeCheckM :: Int
              -> Natural -- ^ Amount of gas to provide typechecker
              -> TypeCheckM a b
              -> Either (TypeError a) b
runTypeCheckM i = flip runReaderT (evalState defaultTable i) .* flip evalStateT

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
typeOf (Error _ ty)                              = pure (void ty) -- FIXME should check that it has appropriate kind?
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
            if k == k'
                then pure (tySubstitute (extractUnique n) (void ty) ty'')
                else throwError (KindMismatch x (void ty) k k')
        _ -> throwError (TypeMismatch x (void t) (TyForall () dummyTyName dummyKind dummyType) (void ty))
typeOf (Unwrap x t) = do
    ty <- typeOf t
    case ty of
        TyFix _ n ty' -> do
            let subst = tySubstitute (extractUnique n) ty ty'
            pure subst
        _             -> throwError (TypeMismatch x (void t) (TyFix () dummyTyName dummyType) (void ty))
typeOf t@(Wrap x n@(TyNameWithKind (TyName (Name _ _ u))) ty t') = do
    k <- kindOf ty
    case k of
        Type{} -> pure ()
        _      -> throwError (KindMismatch x (void ty) (Type ()) (void k))
    ty' <- typeOf t'
    let fixed = tySubstitute u (TyFix () (void n) (void ty)) (void ty)
    if tyReduce fixed == ty'
        then pure (TyFix () (void n) (void ty))
        else throwError (TypeMismatch x (void t) (void ty') fixed)

extractUnique :: TyNameWithKind a -> Unique
extractUnique = nameUnique . unTyName . unTyNameWithKind

-- TODO: make type substitutions occur in a state monad + benchmark
tySubstitute :: Unique -- ^ Unique associated with type variable
             -> Type TyNameWithKind a -- ^ Type we are binding to free variable
             -> Type TyNameWithKind a -- ^ Type we are substituting in
             -> Type TyNameWithKind a
tySubstitute u ty = cata a where
    a (TyVarF _ (TyNameWithKind (TyName (Name _ _ u')))) | u == u' = ty
    a x                                                  = embed x

-- TODO: add left-instatiation etc.
tyReduce :: Type TyNameWithKind a -> Type TyNameWithKind a
tyReduce (TyApp _ (TyLam _ (TyNameWithKind (TyName (Name _ _ u))) _ ty) ty') = tySubstitute u ty' ty
tyReduce x                                                                   = x
