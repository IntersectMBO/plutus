-- | The internal module of the type checker that defines the actual algorithms,
-- but not the user-facing API.

-- 'makeLenses' produces an unused lens.
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}

module Language.PlutusCore.TypeCheck.Internal
    ( DynamicBuiltinNameTypes (..)
    , TypeCheckConfig (..)
    , TypeCheckM
    , tccDoNormTypes
    , tccDynamicBuiltinNameTypes
    , tccMayGas
    , runTypeCheckM
    , kindOfTypeBuiltin
    , inferKindM
    , checkKindM
    , checkKindOfPatternFunctorM
    , typeOfConstant
    , typeOfBuiltinName
    , inferTypeM
    , checkTypeM
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Error
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Normalize
import qualified Language.PlutusCore.Normalize.Internal as Norm
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename
import           PlutusPrelude

import           Control.Lens.TH                        (makeLenses)
import           Control.Monad.Error.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Map                               (Map)
import qualified Data.Map                               as Map

{- Note [Global uniqueness]
WARNING: type inference/checking works under the assumption that the global uniqueness condition
is satisfied. The invariant is not checked, enforced or automatically fulfilled. So you must ensure
that the global uniqueness condition is satisfied before calling 'inferTypeM' or 'checkTypeM'.

The invariant is preserved. In future we will enforce the invariant.
-}

{- Note [Notation]
We write type rules in the bidirectional style.

[infer| G !- x : a] -- means that the inferred type of 'x' in the context 'G' is 'a'.
'a' is not necessary a varible, e.g. [infer| G !- fun : dom -> cod] is fine too.
It reads as follows: "infer the type of 'fun' in the context 'G', check that it's functional and
bind the 'dom' variable to the domain and the 'cod' variable to the codomain of this type".

Analogously, [infer| G !- t :: k] means that the inferred kind of 't' in the context 'G' is 'k'.
The [infer| G !- x : a] judgement appears in conclusions in the clauses of the 'inferTypeM'
function.

[check| G !- x : a] -- check that the type of 'x' in the context 'G' is 'a'.
Since Plutus Core is a fully elaborated language, this amounts to inferring the type of 'x' and
checking that it's equal to 'a'.

Analogously, [check| G !- t :: k] means "check that the kind of 't' in the context 'G' is 'k'".
The [check| G !- x : a] judgement appears in the conclusion in the sole clause of
the 'checkTypeM' function.

The equality check is denoted as "a ~ b".

We use unified contexts in rules, i.e. a context can carry type variables as well as term variables.

The "NORM a" notation reads as "normalize 'a'".

The "a ~>? b" notations reads as "optionally normalize 'a' to 'b'". The "optionally" part is
due to the fact that we allow non-normalized types during development, but do not allow to submit
them on a chain.

Functions that can fail start with either @infer@ or @check@ prefixes,
functions that cannot fail looks like this:

    kindOfTypeBuiltin
    typeOfConstant
    typeOfBuiltinName
-}

-- ######################
-- ## Type definitions ##
-- ######################

-- | Mapping from 'DynamicBuiltinName's to their 'Type's.
newtype DynamicBuiltinNameTypes = DynamicBuiltinNameTypes
    { unDynamicBuiltinNameTypes :: Map DynamicBuiltinName (Dupable (Normalized (Type TyName ())))
    } deriving newtype (Semigroup, Monoid)

type TyVarKinds = UniqueMap TypeUnique (Kind ())
type VarTypes   = UniqueMap TermUnique (Dupable (Normalized (Type TyName ())))

-- | Configuration of the type checker.
data TypeCheckConfig = TypeCheckConfig
    { _tccDoNormTypes             :: Bool
      -- ^ Whether to normalize type annotations.
    , _tccDynamicBuiltinNameTypes :: DynamicBuiltinNameTypes
    , _tccMayGas                  :: Maybe Gas
      -- ^ The upper limit on the length of type reductions.
      -- If set to 'Nothing', type reductions will be unbounded.
    }

-- | The environment that the type checker runs in.
data TypeCheckEnv = TypeCheckEnv
    { _tceTypeCheckConfig :: TypeCheckConfig
    , _tceTyVarKinds      :: TyVarKinds
    , _tceVarTypes        :: VarTypes
    }

-- | The type checking monad that the type checker runs in.
-- In contains a 'TypeCheckEnv' and allows to throw 'TypeError's.
type TypeCheckM ann = ReaderT TypeCheckEnv (ExceptT (TypeError ann) Quote)

-- #########################
-- ## Auxiliary functions ##
-- #########################

makeLenses ''TypeCheckConfig
makeLenses ''TypeCheckEnv

-- | Run a 'TypeCheckM' computation by supplying a 'TypeCheckConfig' to it.
runTypeCheckM
    :: (AsTypeError e ann, MonadError e m, MonadQuote m)
    => TypeCheckConfig -> TypeCheckM ann a -> m a
runTypeCheckM config a =
    throwingEither _TypeError =<< liftQuote (runExceptT $ runReaderT a env) where
        env = TypeCheckEnv config mempty mempty

-- | Extend the context of a 'TypeCheckM' computation with a kinded variable.
withTyVar :: TyName ann -> Kind () -> TypeCheckM ann a -> TypeCheckM ann a
withTyVar name = local . over tceTyVarKinds . insertByName name

-- | Extend the context of a 'TypeCheckM' computation with a typed variable.
withVar :: Name ann -> Normalized (Type TyName ()) -> TypeCheckM ann a -> TypeCheckM ann a
withVar name = local . over tceVarTypes . insertByName name . pure

-- | Look up a 'DynamicBuiltinName' in the 'DynBuiltinNameTypes' environment.
lookupDynamicBuiltinNameM
    :: ann -> DynamicBuiltinName -> TypeCheckM ann (Normalized (Type TyName ()))
lookupDynamicBuiltinNameM ann name = do
    DynamicBuiltinNameTypes dbnts <- asks $ _tccDynamicBuiltinNameTypes . _tceTypeCheckConfig
    case Map.lookup name dbnts of
        Nothing ->
            throwError $ UnknownDynamicBuiltinName ann (UnknownDynamicBuiltinNameErrorE name)
        Just ty -> liftDupable ty

-- | Look up a type variable in the current context.
lookupTyVarM :: TyName ann -> TypeCheckM ann (Kind ())
lookupTyVarM name = do
    mayKind <- asks $ lookupName name . _tceTyVarKinds
    case mayKind of
        Nothing   -> throwError $ FreeTypeVariableE name
        Just kind -> pure kind

-- | Look up a term variable in the current context.
lookupVarM :: Name ann -> TypeCheckM ann (Normalized (Type TyName ()))
lookupVarM name = do
    mayTy <- asks $ lookupName name . _tceVarTypes
    case mayTy of
        Nothing -> throwError $ FreeVariableE name
        Just ty -> liftDupable ty

-- #############
-- ## Dummies ##
-- #############

dummyUnique :: Unique
dummyUnique = Unique 0

dummyTyName :: TyName ()
dummyTyName = TyName (Name () "*" dummyUnique)

dummyKind :: Kind ()
dummyKind = Type ()

dummyType :: Type TyName ()
dummyType = TyVar () dummyTyName

-- ########################
-- ## Type normalization ##
-- ########################

-- | Run a 'NormalizeTypeT' computation in the 'TypeCheckM' context.
-- Depending on whether gas is finite or infinite, calls either
-- 'Norm.runNormalizeTypeFullM' or 'Norm.runNormalizeTypeGasM'.
-- Throws 'OutOfGas' if type normalization runs out of gas.
runNormalizeTypeTM
    :: (forall m. MonadQuote m => Norm.NormalizeTypeT m tyname ann1 a) -> TypeCheckM ann2 a
runNormalizeTypeTM a = do
    mayGas <- asks $ _tccMayGas . _tceTypeCheckConfig
    case mayGas of
        Nothing  -> Norm.runNormalizeTypeFullM a
        Just gas -> do
            mayX <- Norm.runNormalizeTypeGasM gas a
            case mayX of
                Nothing -> throwing _TypeError OutOfGas
                Just x  -> pure x

-- | Normalize a 'Type'.
normalizeTypeM :: Type TyName () -> TypeCheckM ann (Normalized (Type TyName ()))
normalizeTypeM ty = runNormalizeTypeTM $ Norm.normalizeTypeM ty

-- | Substitute a type for a variable in a type and normalize the result.
substNormalizeTypeM
    :: Normalized (Type TyName ())  -- ^ @ty@
    -> TyName ()                    -- ^ @name@
    -> Type TyName ()               -- ^ @body@
    -> TypeCheckM ann (Normalized (Type TyName ()))
substNormalizeTypeM ty name body = runNormalizeTypeTM $ Norm.substNormalizeTypeM ty name body

-- | Normalize a 'Type' or simply wrap it in the 'NormalizedType' constructor
-- if we are working with normalized type annotations.
normalizeTypeOptM :: Type TyName () -> TypeCheckM ann (Normalized (Type TyName ()))
normalizeTypeOptM ty = do
    normTypes <- asks $ _tccDoNormTypes . _tceTypeCheckConfig
    if normTypes
        then normalizeTypeM ty
        else pure $ Normalized ty

-- ###################
-- ## Kind checking ##
-- ###################

-- | Get the 'Kind' of a 'TypeBuiltin'.
kindOfTypeBuiltin :: TypeBuiltin -> Kind ()
kindOfTypeBuiltin = \case
    TyInteger    -> Type ()
    TyByteString -> Type ()
    TyString     -> Type ()

-- | Infer the kind of a type.
inferKindM :: Type TyName ann -> TypeCheckM ann (Kind ())

-- b :: k
-- ------------------------
-- [infer| G !- con b :: k]
inferKindM (TyBuiltin _ b)         =
    pure $ kindOfTypeBuiltin b

-- [infer| G !- v :: k]
-- ------------------------
-- [infer| G !- var v :: k]
inferKindM (TyVar _ v)             =
    lookupTyVarM v

-- [infer| G , n :: dom !- body :: cod]
-- -------------------------------------------------
-- [infer| G !- (\(n :: dom) -> body) :: dom -> cod]
inferKindM (TyLam _ n dom body)    = do
    let dom_ = void dom
    withTyVar n dom_ $ KindArrow () dom_ <$> inferKindM body

-- [infer| G !- fun :: dom -> cod]    [check| G !- arg :: dom]
-- -----------------------------------------------------------
-- [infer| G !- fun arg :: cod]
inferKindM (TyApp ann fun arg)     = do
    funKind <- inferKindM fun
    case funKind of
        KindArrow _ dom cod -> do
            checkKindM ann arg dom
            pure cod
        _ -> throwError $ KindMismatch ann (void fun) (KindArrow () dummyKind dummyKind) funKind

-- [check| G !- a :: *]    [check| G !- b :: *]
-- --------------------------------------------
-- [infer| G !- a -> b :: *]
inferKindM (TyFun ann dom cod)     = do
    checkKindM ann dom $ Type ()
    checkKindM ann cod $ Type ()
    pure $ Type ()

-- [check| G , n :: k !- body :: *]
-- ---------------------------------------
-- [infer| G !- (all (n :: k). body) :: *]
inferKindM (TyForall ann n k body) = do
    withTyVar n (void k) $ checkKindM ann body (Type ())
    pure $ Type ()

-- [infer| G !- arg :: k]    [check| G !- pat :: (k -> *) -> k -> *]
-- -----------------------------------------------------------------
-- [infer| G !- ifix pat arg :: *]
inferKindM (TyIFix ann pat arg)    = do
    k <- inferKindM arg
    checkKindOfPatternFunctorM ann pat k
    pure $ Type ()

-- | Check a 'Type' against a 'Kind'.
checkKindM :: ann -> Type TyName ann -> Kind () -> TypeCheckM ann ()

-- [infer| G !- ty : tyK]    tyK ~ k
-- ---------------------------------
-- [check| G !- ty : k]
checkKindM ann ty k = do
    tyK <- inferKindM ty
    when (tyK /= k) $ throwError (KindMismatch ann (void ty) k tyK)

-- | Check that the kind of a pattern functor is @(k -> *) -> k -> *@.
checkKindOfPatternFunctorM
    :: ann
    -> Type TyName ann  -- ^ A pattern functor.
    -> Kind ()          -- ^ @k@.
    -> TypeCheckM ann ()
checkKindOfPatternFunctorM ann pat k =
    checkKindM ann pat $ KindArrow () (KindArrow () k (Type ())) (KindArrow () k (Type ()))

-- ###################
-- ## Type checking ##
-- ###################

-- | Get the 'Type' of a 'Constant' wrapped in 'NormalizedType'.
typeOfConstant :: Constant ann -> Normalized (Type TyName ())
typeOfConstant = \case
    BuiltinInt  _ _ -> Normalized $ TyBuiltin () TyInteger
    BuiltinBS   _ _ -> Normalized $ TyBuiltin () TyByteString
    BuiltinStr _ _  -> Normalized $ TyBuiltin () TyString

-- | Return the 'Type' of a 'BuiltinName'.
typeOfBuiltinName :: BuiltinName -> Type TyName ()
typeOfBuiltinName bn = withTypedBuiltinName bn typeOfTypedBuiltinName

-- | @unfoldFixOf pat arg k = NORM (vPat (\(a :: k) -> ifix vPat a) arg)@
unfoldFixOf
    :: Normalized (Type TyName ())  -- ^ @vPat@
    -> Normalized (Type TyName ())  -- ^ @vArg@
    -> Kind ()                      -- ^ @k@
    -> TypeCheckM ann (Normalized (Type TyName ()))
unfoldFixOf pat arg k = do
    let vPat = unNormalized pat
        vArg = unNormalized arg
    a <- liftQuote $ freshTyName () "a"
    normalizeTypeM $
        mkIterTyApp () vPat
            [ TyLam () a k . TyIFix () vPat $ TyVar () a
            , vArg
            ]

-- | Infer the type of a 'Builtin'.
inferTypeOfBuiltinM :: Builtin ann -> TypeCheckM ann (Normalized (Type TyName ()))
-- We have a weird corner case here: the type of a 'BuiltinName' can contain 'TypedBuiltinDyn', i.e.
-- a static built-in name is allowed to depend on a dynamic built-in type which are not required
-- to be normalized. For dynamic built-in names we store a map from them to their *normalized types*,
-- with the normalization happening in this module, but what should we do for static built-in names?
-- Right now we just renormalize the type of a static built-in name each time we encounter that name.
inferTypeOfBuiltinM (BuiltinName    _   name) = normalizeTypeFull $ typeOfBuiltinName name
-- TODO: inline this definition once we have only dynamic built-in names.
inferTypeOfBuiltinM (DynBuiltinName ann name) = lookupDynamicBuiltinNameM ann name

-- See the [Global uniqueness] and [Type rules] notes.
-- | Synthesize the type of a term, returning a normalized type.
inferTypeM :: Term TyName Name ann -> TypeCheckM ann (Normalized (Type TyName ()))

-- c : vTy
-- -------------------------
-- [infer| G !- con c : vTy]
inferTypeM (Constant _ con)         =
    pure $ typeOfConstant con

-- [infer| G !- bi : vTy]
-- ------------------------------
-- [infer| G !- builtin bi : vTy]
inferTypeM (Builtin _ bi)           =
    inferTypeOfBuiltinM bi

-- [infer| G !- v : ty]    ty ~>? vTy
-- ----------------------------------
-- [infer| G !- var v : vTy]
inferTypeM (Var _ name)             =
    lookupVarM name

-- [check| G !- dom :: *]    dom ~>? vDom    [infer| G , n : dom !- body : vCod]
-- -----------------------------------------------------------------------------
-- [infer| G !- lam n dom body : vDom -> vCod]
inferTypeM (LamAbs ann n dom body)  = do
    checkKindM ann dom $ Type ()
    vDom <- normalizeTypeOptM $ void dom
    TyFun () <<$>> pure vDom <<*>> withVar n vDom (inferTypeM body)

-- [infer| G , n :: nK !- body : vBodyTy]
-- ---------------------------------------------------
-- [infer| G !- abs n nK body : all (n :: nK) vBodyTy]
inferTypeM (TyAbs _ n nK body)      = do
    let nK_ = void nK
    TyForall () (void n) nK_ <<$>> withTyVar n nK_ (inferTypeM body)

-- [infer| G !- fun : vDom -> vCod]    [check| G !- arg : vDom]
-- ------------------------------------------------------------
-- [infer| G !- fun arg : vCod]
inferTypeM (Apply ann fun arg)      = do
    vFunTy <- inferTypeM fun
    case unNormalized vFunTy of
        TyFun _ vDom vCod -> do
            -- Subparts of a normalized type, so normalized.
            checkTypeM ann arg $ Normalized vDom
            pure $ Normalized vCod
        _ -> throwError (TypeMismatch ann (void fun) (TyFun () dummyType dummyType) vFunTy)

-- [infer| G !- body : all (n :: nK) vCod]    [check| G !- ty :: tyK]    ty ~>? vTy
-- --------------------------------------------------------------------------------
-- [infer| G !- body {ty} : NORM ([vTy / n] vCod)]
inferTypeM (TyInst ann body ty)     = do
    vBodyTy <- inferTypeM body
    case unNormalized vBodyTy of
        TyForall _ n nK vCod -> do
            checkKindM ann ty nK
            vTy <- normalizeTypeOptM $ void ty
            substNormalizeTypeM vTy n vCod
        _ -> throwError (TypeMismatch ann (void body) (TyForall () dummyTyName dummyKind dummyType) vBodyTy)

-- [infer| G !- arg :: k]    [check| G !- pat :: (k -> *) -> k -> *]    pat ~>? vPat    arg ~>? vArg
-- [check| G !- term : NORM (vPat (\(a :: k) -> ifix vPat a) vArg)]
-- -------------------------------------------------------------------------------------------------
-- [infer| G !- iwrap pat arg term : ifix vPat vArg]
inferTypeM (IWrap ann pat arg term) = do
    k <- inferKindM arg
    checkKindOfPatternFunctorM ann pat k
    vPat <- normalizeTypeOptM $ void pat
    vArg <- normalizeTypeOptM $ void arg
    checkTypeM ann term =<< unfoldFixOf vPat vArg k
    pure $ TyIFix () <$> vPat <*> vArg

-- [infer| G !- term : ifix vPat vArg]    [infer| G !- vArg :: k]
-- -----------------------------------------------------------------------
-- [infer| G !- unwrap term : NORM (vPat (\(a :: k) -> ifix vPat a) vArg)]
inferTypeM (Unwrap ann term)        = do
    vTermTy <- inferTypeM term
    case unNormalized vTermTy of
        TyIFix _ vPat vArg -> do
            k <- inferKindM $ ann <$ vArg
            -- Subparts of a normalized type, so normalized.
            unfoldFixOf (Normalized vPat) (Normalized vArg) k
        _                  -> throwError (TypeMismatch ann (void term) (TyIFix () dummyType dummyType) vTermTy)

-- [check| G !- ty :: *]    ty ~>? vTy
-- -----------------------------------
-- [infer| G !- error ty : vTy]
inferTypeM (Error ann ty)           = do
    checkKindM ann ty $ Type ()
    normalizeTypeOptM $ void ty

-- See the [Global uniqueness] and [Type rules] notes.
-- | Check a 'Term' against a 'NormalizedType'.
checkTypeM :: ann -> Term TyName Name ann -> Normalized (Type TyName ()) -> TypeCheckM ann ()

-- [infer| G !- term : vTermTy]    vTermTy ~ vTy
-- ---------------------------------------------
-- [check| G !- term : vTy]
checkTypeM ann term vTy = do
    vTermTy <- inferTypeM term
    when (vTermTy /= vTy) $ throwError (TypeMismatch ann (void term) (unNormalized vTermTy) vTy)
