-- | The internal module of the type checker that defines the actual algorithms,
-- but not the user-facing API.

{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}

module PlutusCore.TypeCheck.Internal
    ( -- export all because a lot are used by the pir-typechecker
      module PlutusCore.TypeCheck.Internal
    , MonadNormalizeType
    ) where

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Error
import PlutusCore.MkPlc
import PlutusCore.Name
import PlutusCore.Normalize.Internal (MonadNormalizeType)
import PlutusCore.Normalize.Internal qualified as Norm
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusPrelude

import Control.Lens
import Control.Monad.Error.Lens
import Control.Monad.Except
-- Using @transformers@ rather than @mtl@, because the former doesn't impose the 'Monad' constraint
-- on 'local'.
import Control.Monad.Trans.Reader
import Data.Array
import Universe

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

The "a ~> b" notations reads as "normalize 'a' to 'b'".

Functions that can fail start with either @infer@ or @check@ prefixes,
functions that cannot fail look like this:

    kindOfBuiltinType
    typeOfBuiltinFunction
-}

-- ######################
-- ## Type definitions ##
-- ######################

-- | Mapping from 'Builtin's to their 'Type's.
newtype BuiltinTypes uni fun = BuiltinTypes
    { unBuiltinTypes :: Array fun (Dupable (Normalized (Type TyName uni ())))
    }

type TyVarKinds = UniqueMap TypeUnique (Kind ())
type VarTypes uni = UniqueMap TermUnique (Dupable (Normalized (Type TyName uni ())))

-- | Configuration of the type checker.
newtype TypeCheckConfig uni fun = TypeCheckConfig
    { _tccBuiltinTypes :: BuiltinTypes uni fun
    }
makeClassy ''TypeCheckConfig

-- | The environment that the type checker runs in.
data TypeCheckEnv uni fun cfg = TypeCheckEnv
    { _tceTypeCheckConfig :: cfg
    , _tceTyVarKinds      :: TyVarKinds
    , _tceVarTypes        :: VarTypes uni
    }
makeLenses ''TypeCheckEnv

-- | The type checking monad that the type checker runs in.
-- In contains a 'TypeCheckEnv' and allows to throw 'TypeError's.
type TypeCheckT uni fun cfg m = ReaderT (TypeCheckEnv uni fun cfg) m

-- | The constraints that are required for kind checking.
type MonadKindCheck err term uni fun ann m =
    ( MonadError err m                  -- Kind/type checking can fail
    , AsTypeError err term uni fun ann  -- with a 'TypeError'.
    , ToKind uni                        -- For getting the kind of a built-in type.
    )

-- | The general constraints that are required for type checking a Plutus AST.
type MonadTypeCheck err term uni fun ann m =
    ( MonadKindCheck err term uni fun ann m  -- Kind checking is run during type checking
                                             -- (this includes the constraint for throwing errors).
    , Norm.MonadNormalizeType uni m          -- Type lambdas open up type computation.
    , GEq uni                                -- For checking equality of built-in types.
    , Ix fun                                 -- For indexing into the precomputed array of types of
                                             -- built-in functions.
    )

-- | The constraints that are required for type checking Plutus Core.
type MonadTypeCheckPlc err uni fun ann m =
    MonadTypeCheck err (Term TyName Name uni fun ()) uni fun ann m

-- #########################
-- ## Auxiliary functions ##
-- #########################


-- | Run a 'TypeCheckM' computation by supplying a 'TypeCheckConfig' to it.
--
-- Used for both type and kind checking, because we need to do kind checking during type checking
-- and so it makes sense to keep a single monad. However type checking requires a 'TypeCheckConfig',
-- while kind checking doesn't, hence we keep the kind checker fully polymorphic over the type of
-- config, so that the kinder checker can be run with an empty config (such as @()@) and access to
-- a 'TypeCheckConfig' is not needed.
runTypeCheckM :: cfg -> TypeCheckT uni fun cfg m a -> m a
runTypeCheckM config a = runReaderT a $ TypeCheckEnv config mempty mempty

-- | Extend the context of a 'TypeCheckM' computation with a kinded variable.
withTyVar :: TyName -> Kind () -> TypeCheckT uni fun cfg m a -> TypeCheckT uni fun cfg m a
withTyVar name = local . over tceTyVarKinds . insertByName name

-- | Look up the type of a built-in function.
lookupBuiltinM
    :: (MonadTypeCheck err term uni fun ann m, HasTypeCheckConfig cfg uni fun)
    => ann -> fun -> TypeCheckT uni fun cfg m (Normalized (Type TyName uni ()))
lookupBuiltinM ann fun = do
    BuiltinTypes arr <- view $ tceTypeCheckConfig . tccBuiltinTypes
    -- Believe it or not, but 'Data.Array' doesn't seem to expose any way of indexing into an array
    -- safely.
    case preview (ix fun) arr of
        Nothing -> throwing _TypeError $ UnknownBuiltinFunctionE ann fun
        Just ty -> liftDupable ty

-- | Extend the context of a 'TypeCheckM' computation with a typed variable.
withVar
    :: Name
    -> Normalized (Type TyName uni ())
    -> TypeCheckT uni fun cfg m a
    -> TypeCheckT uni fun cfg m a
withVar name = local . over tceVarTypes . insertByName name . dupable

-- | Look up a type variable in the current context.
lookupTyVarM
    :: MonadKindCheck err term uni fun ann m
    => ann -> TyName -> TypeCheckT uni fun cfg m (Kind ())
lookupTyVarM ann name = do
    mayKind <- asks $ lookupName name . _tceTyVarKinds
    case mayKind of
        Nothing   -> throwing _TypeError $ FreeTypeVariableE ann name
        Just kind -> pure kind

-- | Look up a term variable in the current context.
lookupVarM
    :: MonadTypeCheck err term uni fun ann m
    => ann -> Name -> TypeCheckT uni fun cfg m (Normalized (Type TyName uni ()))
lookupVarM ann name = do
    mayTy <- asks $ lookupName name . _tceVarTypes
    case mayTy of
        Nothing -> throwing _TypeError $ FreeVariableE ann name
        Just ty -> liftDupable ty

-- #############
-- ## Dummies ##
-- #############

dummyUnique :: Unique
dummyUnique = Unique 0

dummyTyName :: TyName
dummyTyName = TyName (Name "*" dummyUnique)

dummyKind :: Kind ()
dummyKind = Type ()

dummyType :: Type TyName uni ()
dummyType = TyVar () dummyTyName

-- ########################
-- ## Type normalization ##
-- ########################

-- | Normalize a 'Type'.
normalizeTypeM
    :: MonadNormalizeType uni m
    => Type TyName uni ann
    -> TypeCheckT uni fun cfg m (Normalized (Type TyName uni ann))
normalizeTypeM ty = Norm.runNormalizeTypeT $ Norm.normalizeTypeM ty

-- | Substitute a type for a variable in a type and normalize the result.
substNormalizeTypeM
    :: MonadNormalizeType uni m
    => Normalized (Type TyName uni ())  -- ^ @ty@
    -> TyName                           -- ^ @name@
    -> Type TyName uni ()               -- ^ @body@
    -> TypeCheckT uni fun cfg m (Normalized (Type TyName uni ()))
substNormalizeTypeM ty name body = Norm.runNormalizeTypeT $ Norm.substNormalizeTypeM ty name body

-- ###################
-- ## Kind checking ##
-- ###################

-- | Infer the kind of a type.
inferKindM
    :: MonadKindCheck err term uni fun ann m
    => Type TyName uni ann -> TypeCheckT uni fun cfg m (Kind ())

-- b :: k
-- ------------------------
-- [infer| G !- con b :: k]
inferKindM (TyBuiltin _ (SomeTypeIn uni)) =
    pure $ kindOfBuiltinType uni

-- [infer| G !- v :: k]
-- ------------------------
-- [infer| G !- var v :: k]
inferKindM (TyVar ann v)           =
    lookupTyVarM ann v

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
        _ -> throwing _TypeError $ KindMismatch ann (void fun) (KindArrow () dummyKind dummyKind) funKind

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
checkKindM
    :: MonadKindCheck err term uni fun ann m
    => ann -> Type TyName uni ann -> Kind () -> TypeCheckT uni fun cfg m ()

-- [infer| G !- ty : tyK]    tyK ~ k
-- ---------------------------------
-- [check| G !- ty : k]
checkKindM ann ty k = do
    tyK <- inferKindM ty
    when (tyK /= k) $ throwing _TypeError (KindMismatch ann (void ty) k tyK)

-- | Check that the kind of a pattern functor is @(k -> *) -> k -> *@.
checkKindOfPatternFunctorM
    :: MonadKindCheck err term uni fun ann m
    => ann
    -> Type TyName uni ann  -- ^ A pattern functor.
    -> Kind ()              -- ^ @k@.
    -> TypeCheckT uni fun cfg m ()
checkKindOfPatternFunctorM ann pat k =
    checkKindM ann pat $ KindArrow () (KindArrow () k (Type ())) (KindArrow () k (Type ()))

-- ###################
-- ## Type checking ##
-- ###################

-- | @unfoldIFixOf pat arg k = NORM (vPat (\(a :: k) -> ifix vPat a) arg)@
unfoldIFixOf
    :: MonadNormalizeType uni m
    => Normalized (Type TyName uni ())  -- ^ @vPat@
    -> Normalized (Type TyName uni ())  -- ^ @vArg@
    -> Kind ()                          -- ^ @k@
    -> TypeCheckT uni fun cfg m (Normalized (Type TyName uni ()))
unfoldIFixOf pat arg k = do
    let vPat = unNormalized pat
        vArg = unNormalized arg
    a <- liftQuote $ freshTyName "a"
    -- We need to rename @vPat@, otherwise it would be used twice below, which would break global
    -- uniqueness. Alternatively, we could use 'normalizeType' instead of 'normalizeTypeM' as the
    -- former performs renaming before doing normalization, but renaming the entire type implicitly
    -- would be less efficient than renaming a subpart of the type explicitly.
    --
    -- Note however that breaking global uniqueness here most likely would not result in buggy
    -- behavior, see https://github.com/input-output-hk/plutus/pull/2219#issuecomment-672815272
    -- But breaking global uniqueness is a bad idea regardless.
    vPat' <- rename vPat
    normalizeTypeM $
        mkIterTyApp () vPat'
            [ TyLam () a k . TyIFix () vPat $ TyVar () a
            , vArg
            ]

-- See the [Global uniqueness] and [Type rules] notes.
-- | Synthesize the type of a term, returning a normalized type.
inferTypeM
    :: (MonadTypeCheckPlc err uni fun ann m, HasTypeCheckConfig cfg uni fun)
    => Term TyName Name uni fun ann -> TypeCheckT uni fun cfg m (Normalized (Type TyName uni ()))

-- c : vTy
-- -------------------------
-- [infer| G !- con c : vTy]
inferTypeM (Constant _ (Some (ValueOf uni _))) =
    -- See Note [Normalization of built-in types].
    normalizeTypeM $ mkTyBuiltinOf () uni

-- [infer| G !- bi : vTy]
-- ------------------------------
-- [infer| G !- builtin bi : vTy]
inferTypeM (Builtin ann fun) =
    lookupBuiltinM ann fun

-- [infer| G !- v : ty]    ty ~> vTy
-- ---------------------------------
-- [infer| G !- var v : vTy]
inferTypeM (Var ann name) =
    lookupVarM ann name

-- [check| G !- dom :: *]    dom ~> vDom    [infer| G , n : dom !- body : vCod]
-- ----------------------------------------------------------------------------
-- [infer| G !- lam n dom body : vDom -> vCod]
inferTypeM (LamAbs ann n dom body) = do
    checkKindM ann dom $ Type ()
    vDom <- normalizeTypeM $ void dom
    TyFun () <<$>> pure vDom <<*>> withVar n vDom (inferTypeM body)

-- [infer| G , n :: nK !- body : vBodyTy]
-- ---------------------------------------------------
-- [infer| G !- abs n nK body : all (n :: nK) vBodyTy]
inferTypeM (TyAbs _ n nK body) = do
    let nK_ = void nK
    TyForall () n nK_ <<$>> withTyVar n nK_ (inferTypeM body)

-- [infer| G !- fun : vDom -> vCod]    [check| G !- arg : vDom]
-- ------------------------------------------------------------
-- [infer| G !- fun arg : vCod]
inferTypeM (Apply ann fun arg) = do
    vFunTy <- inferTypeM fun
    case unNormalized vFunTy of
        TyFun _ vDom vCod -> do
            -- Subparts of a normalized type, so normalized.
            checkTypeM ann arg $ Normalized vDom
            pure $ Normalized vCod
        _ -> throwing _TypeError (TypeMismatch ann (void fun) (TyFun () dummyType dummyType) vFunTy)

-- [infer| G !- body : all (n :: nK) vCod]    [check| G !- ty :: tyK]    ty ~> vTy
-- -------------------------------------------------------------------------------
-- [infer| G !- body {ty} : NORM ([vTy / n] vCod)]
inferTypeM (TyInst ann body ty) = do
    vBodyTy <- inferTypeM body
    case unNormalized vBodyTy of
        TyForall _ n nK vCod -> do
            checkKindM ann ty nK
            vTy <- normalizeTypeM $ void ty
            substNormalizeTypeM vTy n vCod
        _ -> throwing _TypeError (TypeMismatch ann (void body) (TyForall () dummyTyName dummyKind dummyType) vBodyTy)

-- [infer| G !- arg :: k]    [check| G !- pat :: (k -> *) -> k -> *]    pat ~> vPat    arg ~> vArg
-- [check| G !- term : NORM (vPat (\(a :: k) -> ifix vPat a) vArg)]
-- -----------------------------------------------------------------------------------------------
-- [infer| G !- iwrap pat arg term : ifix vPat vArg]
inferTypeM (IWrap ann pat arg term) = do
    k <- inferKindM arg
    checkKindOfPatternFunctorM ann pat k
    vPat <- normalizeTypeM $ void pat
    vArg <- normalizeTypeM $ void arg
    checkTypeM ann term =<< unfoldIFixOf vPat vArg k
    pure $ TyIFix () <$> vPat <*> vArg

-- [infer| G !- term : ifix vPat vArg]    [infer| G !- vArg :: k]
-- -----------------------------------------------------------------------
-- [infer| G !- unwrap term : NORM (vPat (\(a :: k) -> ifix vPat a) vArg)]
inferTypeM (Unwrap ann term) = do
    vTermTy <- inferTypeM term
    case unNormalized vTermTy of
        TyIFix _ vPat vArg -> do
            k <- inferKindM $ ann <$ vArg
            -- Subparts of a normalized type, so normalized.
            unfoldIFixOf (Normalized vPat) (Normalized vArg) k
        _                  -> throwing _TypeError (TypeMismatch ann (void term) (TyIFix () dummyType dummyType) vTermTy)

-- [check| G !- ty :: *]    ty ~> vTy
-- ----------------------------------
-- [infer| G !- error ty : vTy]
inferTypeM (Error ann ty) = do
    checkKindM ann ty $ Type ()
    normalizeTypeM $ void ty

-- See the [Global uniqueness] and [Type rules] notes.
-- | Check a 'Term' against a 'NormalizedType'.
checkTypeM
    :: (MonadTypeCheckPlc err uni fun ann m, HasTypeCheckConfig cfg uni fun)
    => ann
    -> Term TyName Name uni fun ann
    -> Normalized (Type TyName uni ())
    -> TypeCheckT uni fun cfg m ()

-- [infer| G !- term : vTermTy]    vTermTy ~ vTy
-- ---------------------------------------------
-- [check| G !- term : vTy]
checkTypeM ann term vTy = do
    vTermTy <- inferTypeM term
    when (vTermTy /= vTy) $ throwing _TypeError (TypeMismatch ann (void term) (unNormalized vTy) vTermTy)
