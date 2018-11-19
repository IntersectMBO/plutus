{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings   #-}

module Language.PlutusCore.TypeSynthesis ( typecheckProgram
                                         , typecheckTerm
                                         , kindCheck
                                         , normalizeType
                                         , runTypeCheckM
                                         , dynamicBuiltinNameMeaningsToTypes
                                         , DynamicBuiltinNameTypes (..)
                                         , TypeCheckM
                                         , TypeError (..)
                                         , TypeConfig (..)
                                         , TypeCheckCfg (..)
                                         ) where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer.Type     hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer        (annotateType)
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Monad.Error.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Class
import           Control.Monad.Trans.State          hiding (get, modify)
import           Data.Map                           (Map)
import qualified Data.Map                           as Map

-- | Mapping from 'DynamicBuiltinName's to their 'Type's.
newtype DynamicBuiltinNameTypes = DynamicBuiltinNameTypes
    { unDynamicBuiltinNameTypes :: Map DynamicBuiltinName (Quote (Type TyName ()))
    } deriving (Semigroup, Monoid)

-- | Configuration of the type checker.
data TypeConfig = TypeConfig
    { _typeConfigNormalize           :: Bool
      -- ^ Whether to normalize type annotations
    , _typeConfigDynBuiltinNameTypes :: DynamicBuiltinNameTypes
    }

newtype TypeCheckSt = TypeCheckSt
    { _gas :: Natural
    }

data TypeCheckCfg = TypeCheckCfg
    { _cfgGas        :: Natural     -- ^ Gas to be provided to the typechecker
    , _cfgTypeConfig :: TypeConfig
    }

-- | The type checking monad contains the 'BuiltinTable' and it lets us throw
-- 'TypeError's.
type TypeCheckM a = StateT TypeCheckSt (ReaderT TypeConfig (ExceptT (TypeError a) Quote))

gas :: Lens' TypeCheckSt Natural
gas f s = fmap (\x -> s { _gas = x }) (f (_gas s))

sizeToType :: Kind ()
sizeToType = KindArrow () (Size ()) (Type ())

-- | Get the 'Kind' of a 'TypeBuiltin'.
kindOfTypeBuiltin :: TypeBuiltin -> Kind ()
kindOfTypeBuiltin TyInteger    = sizeToType
kindOfTypeBuiltin TyByteString = sizeToType
kindOfTypeBuiltin TySize       = sizeToType

-- | Annotate a 'Type'. Invariant: the type must be in normal form. The invariant is not checked.
-- In case a type is open, an 'OpenTypeOfBuiltin' is returned.
-- We use this for annotating types of built-ins (both static and dynamic).
annotateClosedNormalType
    :: (AsTypeError e a, MonadError e m)
    => a -> Builtin () -> Type TyName () -> m (NormalizedType TyNameWithKind ())
annotateClosedNormalType ann con ty = case annotateType ty of
    Left  (_::RenameError ()) -> throwing _TypeError $ InternalTypeErrorE ann $ OpenTypeOfBuiltin ty con
    Right annTyOfName         -> pure $ NormalizedType annTyOfName

-- | Annotate the type of a 'BuiltinName' and return it wrapped in 'NormalizedType'.
normalizedAnnotatedTypeOfBuiltinName
    :: (MonadError (TypeError a) m, MonadQuote m)
    => a -> BuiltinName -> m (NormalizedType TyNameWithKind ())
normalizedAnnotatedTypeOfBuiltinName ann name = do
    tyOfName <- liftQuote $ typeOfBuiltinName name
    annotateClosedNormalType ann (BuiltinName () name) tyOfName

-- | Extract the 'TypeScheme' from a 'DynamicBuiltinNameMeaning' and convert it to the
-- corresponding @Type TyName@ for each row of a 'DynamicBuiltinNameMeanings'.
dynamicBuiltinNameMeaningsToTypes :: DynamicBuiltinNameMeanings -> DynamicBuiltinNameTypes
dynamicBuiltinNameMeaningsToTypes (DynamicBuiltinNameMeanings means) =
    DynamicBuiltinNameTypes $ fmap dynamicBuiltinNameMeaningToType means

-- | Type-check a program, returning a normalized type.
typecheckProgram :: (AsTypeError e a, MonadError e m, MonadQuote m)
                 => TypeCheckCfg
                 -> Program TyNameWithKind NameWithType a
                 -> m (NormalizedType TyNameWithKind ())
typecheckProgram cfg (Program _ _ t) = typecheckTerm cfg t

-- | Type-check a term, returning a normalized type.
typecheckTerm :: (AsTypeError e a, MonadError e m, MonadQuote m)
              => TypeCheckCfg
              -> Term TyNameWithKind NameWithType a
              -> m (NormalizedType TyNameWithKind ())
typecheckTerm cfg t = throwingEither _TypeError =<< (liftQuote $ runExceptT $ runTypeCheckM cfg (typeOf t))

-- | Kind-check a PLC type.
kindCheck :: (AsTypeError e a, MonadError e m, MonadQuote m)
          => TypeCheckCfg
          -> Type TyNameWithKind a
          -> m (Kind ())
kindCheck cfg t = throwingEither _TypeError =<< (liftQuote $ runExceptT $ runTypeCheckM cfg (kindOf t))

-- | Run the type checker with a default context.
runTypeCheckM :: TypeCheckCfg
              -> TypeCheckM a b
              -> ExceptT (TypeError a) Quote b
runTypeCheckM (TypeCheckCfg i typeConfig) tc =
    runReaderT (evalStateT tc (TypeCheckSt i)) typeConfig

typeCheckStep :: TypeCheckM a ()
typeCheckStep = do
    (TypeCheckSt i) <- get
    if i == 0
        then throwError OutOfGas
        else modify (over gas (subtract 1))

-- | Extract kind information from a type.
kindOf :: Type TyNameWithKind a -> TypeCheckM a (Kind ())
kindOf TyInt{} = pure (Size ())
kindOf (TyFun x dom cod) = do
    kindCheckM x dom $ Type ()
    kindCheckM x cod $ Type ()
    pure $ Type ()
kindOf (TyForall x _ _ ty) = do
    kindCheckM x ty $ Type ()
    pure $ Type ()
kindOf (TyLam _ _ argK body) = KindArrow () (void argK) <$> kindOf body
kindOf (TyVar _ (TyNameWithKind (TyName (Name (_, k) _ _)))) = pure (void k)
kindOf (TyBuiltin _ b) = pure $ kindOfTypeBuiltin b
kindOf (TyFix x _ pat) = do
    kindCheckM x pat $ Type ()
    pure $ Type ()
kindOf (TyApp x fun arg) = do
    funK <- kindOf fun
    case funK of
        KindArrow _ argK resK -> do
            typeCheckStep
            kindCheckM x arg argK
            pure resK
        _ -> throwError $ KindMismatch x (void fun) (KindArrow () dummyKind dummyKind) funK

-- | Check a 'Type' against a 'Kind'.
kindCheckM :: a -> Type TyNameWithKind a -> Kind () -> TypeCheckM a ()
kindCheckM x ty k = do
    tyK <- kindOf ty
    when (tyK /= k) $ throwError (KindMismatch x (void ty) k tyK)

-- | Apply a 'TypeBuiltin' to a 'Size' and wrap in 'NormalizedType'.
applySizedNormalized :: TypeBuiltin -> Size -> NormalizedType tyname ()
applySizedNormalized tb = NormalizedType . TyApp () (TyBuiltin () tb) . TyInt ()

dummyUnique :: Unique
dummyUnique = Unique 0

dummyTyName :: TyNameWithKind ()
dummyTyName = TyNameWithKind (TyName (Name ((), Type ()) "*" dummyUnique))

dummyKind :: Kind ()
dummyKind = Type ()

dummyType :: Type TyNameWithKind ()
dummyType = TyVar () dummyTyName

-- | Look up a 'DynamicBuiltinName' in the 'DynBuiltinNameTypes' environment.
lookupDynamicBuiltinName :: a -> DynamicBuiltinName -> TypeCheckM a (NormalizedType TyNameWithKind ())
lookupDynamicBuiltinName ann name = do
    dbnts <- asks $ unDynamicBuiltinNameTypes . _typeConfigDynBuiltinNameTypes
    case Map.lookup name dbnts of
        Nothing    ->
            throwError $ UnknownDynamicBuiltinName ann (UnknownDynamicBuiltinNameErrorE name)
        Just quoTy -> do
            ty <- liftQuote quoTy
            annotateClosedNormalType ann (DynBuiltinName () name) ty

-- | Get the 'Type' of a 'Constant' wrapped in 'NormalizedType'.
typeOfConstant :: Constant a -> NormalizedType TyNameWithKind ()
typeOfConstant (BuiltinInt  _ size _) = applySizedNormalized TyInteger    size
typeOfConstant (BuiltinBS   _ size _) = applySizedNormalized TyByteString size
typeOfConstant (BuiltinSize _ size)   = applySizedNormalized TySize       size

typeOfBuiltin :: Builtin a -> TypeCheckM a (NormalizedType TyNameWithKind ())
typeOfBuiltin (BuiltinName    ann name) = normalizedAnnotatedTypeOfBuiltinName ann name
typeOfBuiltin (DynBuiltinName ann name) = lookupDynamicBuiltinName ann name

{- Note [Type rules]
We write type rules in the bidirectional style.

[infer| x : a] -- means that the inferred type of 'x' is 'a'. 'a' is not necessary a varible, e.g.
[infer| fun : dom -> cod] is fine too. It reads as follows: "infer the type of 'fun', check that its
functional and bind the 'dom' variable to the domain and the 'cod' variable to the codomain of this type".
Analogously, [infer| t :: k] means that the inferred kind of 't' is 'k'.
The [infer| x : a] judgement appears in conclusions in the clauses of the 'typeOf' function.

[check| x : a] -- check that the type of 'x' is 'a'. Since Plutus Core is fully elaborated language,
this amounts to inferring the type of 'x' and checking that it's equal to 'a'.
The equality check is denoted as "a ~ b".
Analogously, [check| t :: k] means "check that the kind of 't' is 'k'".
The [check| x : a] judgement appears in the conclusion in the sole clause of the 'typeCheckM' function.

The "a ~> b" notation reads as "normalize 'a' to 'b'".
The "a ~>? b" notations reads as "optionally normalize 'a' to 'b'". The "optionally" part is due to the
fact that we allow non-normalized types during development, but do not allow to submit them on a chain.
-}

{- Note [Type environments]
Type checking works using type environments to handle substitutions efficiently. We
keep a type environment which holds all substitutions which should be in
scope at any given moment. After any lookups, we clone the looked-up type in
order to maintain global uniqueness.

This is all tracked in a state monad, and we simply delete any substitutions
once they go out of scope; this is permissible since 'Unique's are globally
unique and so we will not delete the wrong thing.
-}

-- See the [Type rules] and [Type environments] notes.
-- | Synthesize the type of a term, returning a normalized type.
typeOf :: Term TyNameWithKind NameWithType a -> TypeCheckM a (NormalizedType TyNameWithKind ())

-- v : ty    ty ~>? vTy
-- --------------------
-- [infer| var v : vTy]
typeOf (Var _ (NameWithType (Name (_, ty) _ _))) =
    -- Since we kind check types at lambdas, we can normalize types here without kind checking.
    -- Type normalization at each variable is inefficient and we may consider something else later.
    normalizeTypeOpt $ void ty

-- [check| dom :: *]    dom ~>? vDom    [infer| body : vCod]
-- ---------------------------------------------------------
-- [infer| lam n dom body : vDom -> vCod]
typeOf (LamAbs x _ dom body)                     = do
    kindCheckM x dom $ Type ()
    TyFun () <<$>> normalizeTypeOpt (void dom) <<*>> typeOf body

-- [check| ty :: *]    ty ~>? vTy
-- ------------------------------
-- [infer| error ty : vTy]
typeOf (Error x ty)                              = do
    kindCheckM x ty $ Type ()
    normalizeType $ void ty

-- [infer| body : vBodyTy]
-- ----------------------------------------------
-- [infer| abs n nK body : all (n :: nK) vBodyTy]
typeOf (TyAbs _ n nK body)                       = TyForall () (void n) (void nK) <<$>> typeOf body

-- c : vTy
-- --------------------
-- [infer| con c : vTy]
typeOf (Constant _ con)                          = pure (typeOfConstant con)
typeOf (Builtin _ bi) = typeOfBuiltin bi

-- [infer| fun : vDom -> vCod]    [check| arg : vDom]
-- --------------------------------------------------
-- [infer| [fun arg] : vCod]
typeOf (Apply x fun arg) = do
    vFunTy <- typeOf fun
    case getNormalizedType vFunTy of
        TyFun _ vDom vCod -> do
            typeCheckStep
            typeCheckM x arg $ NormalizedType vDom  -- Subpart of a normalized type, so normalized.
            pure $ NormalizedType vCod              -- Subpart of a normalized type, so normalized.
        _ -> throwError (TypeMismatch x (void fun) (TyFun () dummyType dummyType) vFunTy)

-- [infer| body : all (n :: nK) vCod]    [check| ty :: tyK]    ty ~>? vTy    [vTy / n] vCod ~> vRes
-- ------------------------------------------------------------------------------------------------
-- [infer| {body ty} : vRes]
typeOf (TyInst x body ty) = do
    vBodyTy <- typeOf body
    case getNormalizedType vBodyTy of
        TyForall _ n nK vCod -> do
            kindCheckM x ty nK
            vTy <- normalizeTypeOpt $ void ty
            typeCheckStep
            substituteNormalizeType vTy n vCod
        _ -> throwError (TypeMismatch x (void body) (TyForall () dummyTyName dummyKind dummyType) vBodyTy)

-- [infer| term : fix n vPat]    [fix n vPat / n] vPat ~> vRes
-- -----------------------------------------------------------
-- [infer| unwrap n term : vRes]
typeOf (Unwrap x term) = do
    vTermTy <- typeOf term
    case getNormalizedType vTermTy of
        TyFix _ n vPat -> substituteNormalizeType vTermTy n vPat
        _              -> throwError (TypeMismatch x (void term) (TyFix () dummyTyName dummyType) vTermTy)

-- [check| pat :: *]    pat ~>? vPat    [fix n vPat / n] vPat ~> vTermTy'    [check| term : vTermTy]
-- -------------------------------------------------------------------------------------------------
-- [infer| wrap n pat term : fix n vPat]
typeOf (Wrap x n pat term) = do
    kindCheckM x pat $ Type ()
    vPat <- normalizeTypeOpt $ void pat
    vTermTy <- substituteNormalizeType (TyFix () (void n) <$> vPat) (void n) $ getNormalizedType vPat
    typeCheckStep
    typeCheckM x term vTermTy
    pure $ TyFix () (void n) <$> vPat

-- | Check a 'Term' against a 'NormalizedType'.
typeCheckM :: a
           -> Term TyNameWithKind NameWithType a
           -> NormalizedType TyNameWithKind ()
           -> TypeCheckM a ()

-- [infer| term : vTermTy]    vTermTy ~ vTy
-- ----------------------------------------
-- [check| term : vTy]
typeCheckM x term vTy = do
    vTermTy <- typeOf term
    when (vTermTy /= vTy) $ throwError (TypeMismatch x (void term) (getNormalizedType vTermTy) vTy)

-- this will reduce a type, or simply wrap it in a 'NormalizedType' constructor
-- if we are working with normalized type annotations
normalizeTypeOpt :: Type TyNameWithKind () -> TypeCheckM a (NormalizedType TyNameWithKind ())
normalizeTypeOpt ty = do
    typeConfig <- ask
    if _typeConfigNormalize typeConfig
        then normalizeType ty
        else pure $ NormalizedType ty
