-- 'makeLenses' produces unused lenses.
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TemplateHaskell     #-}

module Language.PlutusCore.TypeSynthesis ( typecheckProgram
                                         , typecheckTerm
                                         , kindCheck
                                         , runTypeCheckM
                                         , runInTypeCheckM
                                         , dynamicBuiltinNameMeaningsToTypes
                                         , DynamicBuiltinNameTypes (..)
                                         , TypeCheckM
                                         , TypeError (..)
                                         , TypeConfig (..)
                                         ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer.Type hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer    (rename)
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Lens.TH                (makeLenses)
import           Control.Monad.Error.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Map                       (Map)
import qualified Data.Map                       as Map

{- Note [Costs]
Typechecking costs are relatively simple: it costs 1 gas to perform a reduction.
Substitution does not in general cost anything.

Costs are reset every time we enter 'NormalizeTypeT'.

In unlimited mode, gas is not tracked and we do not fail even on large numbers of reductions.
-}

-- | Mapping from 'DynamicBuiltinName's to their 'Type's.
newtype DynamicBuiltinNameTypes = DynamicBuiltinNameTypes
    { unDynamicBuiltinNameTypes :: Map DynamicBuiltinName (NormalizedType TyName ())
    } deriving (Semigroup, Monoid)

type TyVarKinds = UniqueMap TypeUnique (Kind ())
type VarTypes   = UniqueMap TermUnique (NormalizedType TyName ())

-- TODO: split 'TypeConfig' to 'TypeEnv' and 'TypeConfig'.

-- | Configuration of the type checker.
data TypeConfig = TypeConfig
    { _typeConfigNormalize           :: Bool
      -- ^ Whether to normalize type annotations.
    , _typeConfigDynBuiltinNameTypes :: DynamicBuiltinNameTypes
    , _typeConfigTyVarKinds          :: TyVarKinds
    , _typeConfigVarTypes            :: VarTypes
    , _typeConfigGas                 :: Maybe Gas
       -- ^ The upper limit on the length of type reductions.
       -- If set to 'Nothing', type reductions will be unbounded.
    }

-- | The type checking monad contains the 'TypeConfig' and it lets us throw 'TypeError's.
type TypeCheckM ann = ReaderT TypeConfig (ExceptT (TypeError ann) Quote)

makeLenses ''TypeConfig

-- | Run a 'NormalizeTypeT' computation in the 'TypeCheckM' context.
-- Depending on whether gas is finite or infinite, calls either
-- 'runNormalizeTypeDownM' or 'runNormalizeTypeGasM'.
-- Throws 'OutOfGas' if type normalization runs out of gas.
runInTypeCheckM :: (forall m. MonadQuote m => NormalizeTypeT m tyname ann1 a) -> TypeCheckM ann2 a
runInTypeCheckM a = do
    mayGas <- asks _typeConfigGas
    case mayGas of
        Nothing  -> runNormalizeTypeDownM a
        Just gas -> do
            mayX <- runNormalizeTypeGasM gas a
            case mayX of
                Nothing -> throwing _TypeError OutOfGas
                Just x  -> pure x

withTyVar :: TyName ann -> Kind () -> TypeCheckM ann a -> TypeCheckM ann a
withTyVar name = local . over typeConfigTyVarKinds . insertByName name

withVar :: Name ann -> NormalizedType TyName () -> TypeCheckM ann a -> TypeCheckM ann a
withVar name = local . over typeConfigVarTypes . insertByName name

-- | Normalize a 'Type'.
normalizeTypeTcm :: Type TyName () -> TypeCheckM a (NormalizedType TyName ())
normalizeTypeTcm ty = runInTypeCheckM $ normalizeTypeM ty

-- | Substitute a type for a variable in a type and normalize the result.
substituteNormalizeTypeTcm
    :: NormalizedType TyName ()                 -- ^ @ty@
    -> TyName ()                                -- ^ @name@
    -> Type TyName ()                           -- ^ @body@
    -> TypeCheckM a (NormalizedType TyName ())
substituteNormalizeTypeTcm ty name body = runInTypeCheckM $ substituteNormalizeTypeM ty name body

-- | Normalize a 'Type' or simply wrap it in the 'NormalizedType' constructor
-- if we are working with normalized type annotations.
normalizeTypeOptTcm :: Type TyName () -> TypeCheckM a (NormalizedType TyName ())
normalizeTypeOptTcm ty = do
    normalize <- asks _typeConfigNormalize
    if normalize
        then normalizeTypeTcm ty
        else pure $ NormalizedType ty

sizeToType :: Kind ()
sizeToType = KindArrow () (Size ()) (Type ())

-- | Get the 'Kind' of a 'TypeBuiltin'.
kindOfTypeBuiltin :: TypeBuiltin -> Kind ()
kindOfTypeBuiltin TyInteger    = sizeToType
kindOfTypeBuiltin TyByteString = sizeToType
kindOfTypeBuiltin TySize       = sizeToType
kindOfTypeBuiltin TyString     = Type ()

-- TODO: move me to a separate API module once it's there.
-- | Extract the 'TypeScheme' from a 'DynamicBuiltinNameMeaning' and convert it to the
-- corresponding @Type TyName@ for each row of a 'DynamicBuiltinNameMeanings'.
dynamicBuiltinNameMeaningsToTypes :: DynamicBuiltinNameMeanings -> DynamicBuiltinNameTypes
dynamicBuiltinNameMeaningsToTypes (DynamicBuiltinNameMeanings means) =
    DynamicBuiltinNameTypes $ fmap toType means where
        -- TODO: kind check the types before normalizing them. We can't do that right now
        -- in a nice way, because 'kindCheck' infers the kind of a type rather than checks a type
        -- against a kind.
        -- We call 'runQuote' here in order to prevent renormalization at each look-up.
        -- It's fine to do so, because we rename types in 'lookupDynamicBuiltinName'.
        toType mean = runQuote $ dynamicBuiltinNameMeaningToType mean >>= rename >>= normalizeTypeDown

-- | Type-check a program, returning a normalized type.
typecheckProgram :: (AsTypeError e a, MonadError e m, MonadQuote m)
                 => TypeConfig
                 -> Program TyName Name a
                 -> m (NormalizedType TyName ())
typecheckProgram cfg (Program _ _ t) = typecheckTerm cfg t

-- | Type-check a term, returning a normalized type.
typecheckTerm :: (AsTypeError e a, MonadError e m, MonadQuote m)
              => TypeConfig
              -> Term TyName Name a
              -> m (NormalizedType TyName ())
typecheckTerm cfg t = throwingEither _TypeError =<< (liftQuote $ runExceptT $ runTypeCheckM cfg (typeOf t))

-- | Kind-check a PLC type.
kindCheck :: (AsTypeError e a, MonadError e m, MonadQuote m)
          => TypeConfig
          -> Type TyName a
          -> m (Kind ())
kindCheck cfg t = throwingEither _TypeError =<< (liftQuote $ runExceptT $ runTypeCheckM cfg (kindOf t))

-- | Run the type checker with a default context.
runTypeCheckM :: TypeConfig
              -> TypeCheckM a b
              -> ExceptT (TypeError a) Quote b
runTypeCheckM typeConfig tc = runReaderT tc typeConfig

-- | Infer the kind of a type variable by looking it up in the current context.
kindOfTyVar :: TyName a -> TypeCheckM a (Kind ())
kindOfTyVar name = do
    mayKind <- asks $ lookupName name . _typeConfigTyVarKinds
    case mayKind of
        Nothing   -> throwError $ FreeTypeVariableE name
        Just kind -> pure kind

-- | Infer the type of a variable by looking it up in the current context.
typeOfVar :: Name a -> TypeCheckM a (NormalizedType TyName ())
typeOfVar name = do
    mayTy <- asks $ lookupName name . _typeConfigVarTypes
    case mayTy of
        Nothing -> throwError $ FreeVariableE name
        Just ty -> rename ty

-- | Infer the kind of a type.
kindOf :: Type TyName a -> TypeCheckM a (Kind ())

-- ---------------------------
-- [infer| G !- con i :: size]
kindOf TyInt{}               = pure (Size ())

-- [check| G !- a :: *]    [check| G !- b :: *]
-- --------------------------------------------
-- [infer| G !- a -> b :: *]
kindOf (TyFun x dom cod)     = do
    kindCheckM x dom $ Type ()
    kindCheckM x cod $ Type ()
    pure $ Type ()

-- [check| G , n :: k !- body :: *]
-- ---------------------------------------
-- [infer| G !- (all (n :: k). body) :: *]
kindOf (TyForall x n k body) = do
    withTyVar n (void k) $ kindCheckM x body (Type ())
    pure $ Type ()

-- [infer| G , n :: dom !- body :: cod]
-- -------------------------------------------------
-- [infer| G !- (\(n :: dom) -> body) :: dom -> cod]
kindOf (TyLam _ n dom body)  = do
    let dom_ = void dom
    withTyVar n dom_ $ KindArrow () dom_ <$> kindOf body

-- [infer| G !- v :: k]
-- ------------------------
-- [infer| G !- var v :: k]
kindOf (TyVar _ v)           = kindOfTyVar v

-- [infer| G !- b :: k]
-- ------------------------
-- [infer| G !- con b :: k]
kindOf (TyBuiltin _ b)       = pure $ kindOfTypeBuiltin b

-- [infer| G !- arg :: k]    [check| G !- pat :: (k -> *) -> k -> *]
-- -----------------------------------------------------------------
-- [infer| G !- ifix pat arg :: *]
kindOf (TyIFix x pat arg)    = do
    k <- kindOf arg
    kindCheckPatternFunctorM x pat k
    pure $ Type ()

-- [infer| G !- fun :: dom -> cod]    [check| G !- arg :: dom]
-- -----------------------------------------------------------
-- [infer| G !- fun arg :: cod]
kindOf (TyApp x fun arg)     = do
    funKind <- kindOf fun
    case funKind of
        KindArrow _ dom cod -> do
            kindCheckM x arg dom
            pure cod
        _ -> throwError $ KindMismatch x (void fun) (KindArrow () dummyKind dummyKind) funKind

-- | Check a 'Type' against a 'Kind'.
kindCheckM :: a -> Type TyName a -> Kind () -> TypeCheckM a ()

-- [infer| G !- ty : tyK]    tyK ~ k
-- ---------------------------------
-- [check| G !- ty : k]
kindCheckM x ty k = do
    tyK <- kindOf ty
    when (tyK /= k) $ throwError (KindMismatch x (void ty) k tyK)

-- | Check that the kind of a pattern functor is @(k -> *) -> k -> *@.
kindCheckPatternFunctorM
    :: ann
    -> Type TyName ann  -- ^ A pattern functor.
    -> Kind ()          -- ^ @k@.
    -> TypeCheckM ann ()
kindCheckPatternFunctorM ann pat k =
    kindCheckM ann pat $ KindArrow () (KindArrow () k (Type ())) (KindArrow () k (Type ()))

-- | Apply a 'TypeBuiltin' to a 'Size' and wrap in 'NormalizedType'.
applySizedNormalized :: TypeBuiltin -> Size -> NormalizedType tyname ()
applySizedNormalized tb = NormalizedType . TyApp () (TyBuiltin () tb) . TyInt ()

dummyUnique :: Unique
dummyUnique = Unique 0

dummyTyName :: TyName ()
dummyTyName = TyName (Name () "*" dummyUnique)

dummyKind :: Kind ()
dummyKind = Type ()

dummyType :: Type TyName ()
dummyType = TyVar () dummyTyName

-- | Look up a 'DynamicBuiltinName' in the 'DynBuiltinNameTypes' environment.
lookupDynamicBuiltinName :: a -> DynamicBuiltinName -> TypeCheckM a (NormalizedType TyName ())
lookupDynamicBuiltinName ann name = do
    dbnts <- asks $ unDynamicBuiltinNameTypes . _typeConfigDynBuiltinNameTypes
    case Map.lookup name dbnts of
        Nothing ->
            throwError $ UnknownDynamicBuiltinName ann (UnknownDynamicBuiltinNameErrorE name)
        Just ty -> rename ty

-- | Get the 'Type' of a 'Constant' wrapped in 'NormalizedType'.
typeOfConstant :: Constant a -> NormalizedType TyName ()
typeOfConstant (BuiltinInt  _ size _) = applySizedNormalized TyInteger    size
typeOfConstant (BuiltinBS   _ size _) = applySizedNormalized TyByteString size
typeOfConstant (BuiltinSize _ size)   = applySizedNormalized TySize       size
typeOfConstant (BuiltinStr _ _)       = NormalizedType $ TyBuiltin () TyString

typeOfBuiltin :: Builtin a -> TypeCheckM a (NormalizedType TyName ())
-- We have a weird corner case here: the type of a 'BuiltinName' can contain 'TypedBuiltinDyn', i.e.
-- a static built-in name is allowed to depend on a dynamic built-in type which are not required
-- to be normalized. For dynamic built-in names we store a map from them to their *normalized types*,
-- with the normalization happening in this module, but what should we do for static built-in names?
-- Right now we just renormalize the type of a static built-in name each time we encounter that name.
typeOfBuiltin (BuiltinName    _   name) =
    liftQuote (typeOfBuiltinName name) >>= rename >>= normalizeTypeDown
typeOfBuiltin (DynBuiltinName ann name) = lookupDynamicBuiltinName ann name

{- Note [Type rules]
We write type rules in the bidirectional style.

[infer| G !- x : a] -- means that the inferred type of 'x' in the context 'G' is 'a'.
'a' is not necessary a varible, e.g. [infer| G !- fun : dom -> cod] is fine too.
It reads as follows: "infer the type of 'fun' in the context 'G', check that it's functional and
bind the 'dom' variable to the domain and the 'cod' variable to the codomain of this type".

Analogously, [infer| G !- t :: k] means that the inferred kind of 't' in the context 'G' is 'k'.
The [infer| G !- x : a] judgement appears in conclusions in the clauses of the 'typeOf' function.

[check| G !- x : a] -- check that the type of 'x' in the context 'G' is 'a'.
Since Plutus Core is a fully elaborated language, this amounts to inferring the type of 'x' and
checking that it's equal to 'a'.

Analogously, [check| G !- t :: k] means "check that the kind of 't' in the context 'G' is 'k'".
The [check| G !- x : a] judgement appears in the conclusion in the sole clause of
the 'typeCheckM' function.

The equality check is denoted as "a ~ b".

We use unified contexts, i.e. a context can carry type variables as well as term variables.

The "NORM a" notation reads as "normalize 'a'".

The "a ~>? b" notations reads as "optionally normalize 'a' to 'b'". The "optionally" part is due to the
fact that we allow non-normalized types during development, but do not allow to submit them on a chain.
-}

-- See the [Type rules] and [Type environments] notes.
-- | Synthesize the type of a term, returning a normalized type.
typeOf :: Term TyName Name a -> TypeCheckM a (NormalizedType TyName ())

-- [infer| G !- v : ty]    ty ~>? vTy
-- ----------------------------------
-- [infer| G !- var v : vTy]
typeOf (Var _ name)                              = typeOfVar name

-- [check| G !- dom :: *]    dom ~>? vDom    [infer| G , n : dom !- body : vCod]
-- -----------------------------------------------------------------------------
-- [infer| G !- lam n dom body : vDom -> vCod]
typeOf (LamAbs x n dom body)                     = do
    kindCheckM x dom $ Type ()
    vDom <- normalizeTypeOptTcm $ void dom
    TyFun () <<$>> pure vDom <<*>> withVar n vDom (typeOf body)

-- [check| G !- ty :: *]    ty ~>? vTy
-- -----------------------------------
-- [infer| G !- error ty : vTy]
typeOf (Error x ty)                              = do
    kindCheckM x ty $ Type ()
    normalizeTypeOptTcm $ void ty

-- [infer| G , n :: nK !- body : vBodyTy]
-- ---------------------------------------------------
-- [infer| G !- abs n nK body : all (n :: nK) vBodyTy]
typeOf (TyAbs _ n nK body)                       = do
    let nK_ = void nK
    TyForall () (void n) nK_ <<$>> withTyVar n nK_ (typeOf body)

-- [infer| G !- c : vTy]
-- -------------------------
-- [infer| G !- con c : vTy]
typeOf (Constant _ con)                          = pure (typeOfConstant con)

-- [infer| G !- bi : vTy]
-- ------------------------------
-- [infer| G !- builtin bi : vTy]
typeOf (Builtin _ bi)                            = typeOfBuiltin bi

-- [infer| G !- fun : vDom -> vCod]    [check| G !- arg : vDom]
-- ------------------------------------------------------------
-- [infer| G !- fun arg : vCod]
typeOf (Apply x fun arg)                         = do
    vFunTy <- typeOf fun
    case getNormalizedType vFunTy of
        TyFun _ vDom vCod -> do
            typeCheckM x arg $ NormalizedType vDom  -- Subpart of a normalized type, so normalized.
            pure $ NormalizedType vCod              -- Subpart of a normalized type, so normalized.
        _ -> throwError (TypeMismatch x (void fun) (TyFun () dummyType dummyType) vFunTy)

-- [infer| G !- body : all (n :: nK) vCod]    [check| G !- ty :: tyK]    ty ~>? vTy
-- --------------------------------------------------------------------------------
-- [infer| G !- body {ty} : NORM ([vTy / n] vCod)]
typeOf (TyInst x body ty)                        = do
    vBodyTy <- typeOf body
    case getNormalizedType vBodyTy of
        TyForall _ n nK vCod -> do
            kindCheckM x ty nK
            vTy <- normalizeTypeOptTcm $ void ty
            substituteNormalizeTypeTcm vTy n vCod
        _ -> throwError (TypeMismatch x (void body) (TyForall () dummyTyName dummyKind dummyType) vBodyTy)

-- [infer| G !- term : ifix vPat vArg]    [infer| G !- vArg :: k]
-- -----------------------------------------------------------------------
-- [infer| G !- unwrap term : NORM (vPat (\(a :: k) -> ifix vPat a) vArg)]
typeOf (Unwrap x term)                           = do
    vTermTy <- typeOf term
    case getNormalizedType vTermTy of
        TyIFix _ vPat vArg -> do
            k <- kindOf $ x <$ vArg
            -- Subparts of a normalized type, so normalized.
            unfoldFixOf (NormalizedType vPat) (NormalizedType vArg) k
        _                  -> throwError (TypeMismatch x (void term) (TyIFix () dummyType dummyType) vTermTy)

-- [infer| G !- arg :: k]    [check| G !- pat :: (k -> *) -> k -> *]    pat ~>? vPat    arg ~>? vArg
-- [check| G !- term : NORM (vPat (\(a :: k) -> ifix vPat a) vArg)]
-- -------------------------------------------------------------------------------------------------
-- [infer| G !- iwrap pat arg term : ifix vPat vArg]
typeOf (IWrap x pat arg term) = do
    k <- kindOf arg
    kindCheckPatternFunctorM x pat k
    vPat <- normalizeTypeOptTcm $ void pat
    vArg <- normalizeTypeOptTcm $ void arg
    typeCheckM x term =<< unfoldFixOf vPat vArg k
    return $ TyIFix () <$> vPat <*> vArg

-- | Check a 'Term' against a 'NormalizedType'.
typeCheckM :: a -> Term TyName Name a -> NormalizedType TyName () -> TypeCheckM a ()

-- [infer| G !- term : vTermTy]    vTermTy ~ vTy
-- ---------------------------------------------
-- [check| G !- term : vTy]
typeCheckM x term vTy = do
    vTermTy <- typeOf term
    when (vTermTy /= vTy) $ throwError (TypeMismatch x (void term) (getNormalizedType vTermTy) vTy)

-- | @unfoldFixOf pat arg k = NORM (vPat (\(a :: k) -> ifix vPat a) arg)@
unfoldFixOf
    :: NormalizedType TyName ()  -- ^ @vPat@
    -> NormalizedType TyName ()  -- ^ @vArg@
    -> Kind ()                   -- ^ @k@
    -> TypeCheckM a (NormalizedType TyName ())
unfoldFixOf pat arg k = do
    let vPat = getNormalizedType pat
        vArg = getNormalizedType arg
    a <- liftQuote $ freshTyName () "a"
    normalizeTypeTcm $
        foldl' (TyApp ()) vPat
            [ TyLam () a k . TyIFix () vPat $ TyVar () a
            , vArg
            ]
