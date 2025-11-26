-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-| The internal module of the type checker that defines the actual algorithms,
but not the user-facing API. -}
module PlutusCore.TypeCheck.Internal
  ( -- export all because a lot are used by the pir-typechecker
    module PlutusCore.TypeCheck.Internal
  , MonadNormalizeType
  ) where

import PlutusCore.Builtin
import PlutusCore.Core.Type (Kind (..), Normalized (..), Term (..), Type (..), toPatFuncKind)
import PlutusCore.Error (ExpectedShapeOr (ExpectedExact, ExpectedShape), TypeError (..))
import PlutusCore.MkPlc (mkIterTyAppNoAnn, mkIterTyFun, mkTyBuiltinOf)
import PlutusCore.Name.Unique
  ( HasText (theText)
  , Name (Name)
  , Named (Named)
  , TermUnique
  , TyName (TyName)
  , TypeUnique
  , theUnique
  )
import PlutusCore.Name.UniqueMap (UniqueMap, insertNamed, lookupName)
import PlutusCore.Normalize.Internal (MonadNormalizeType)
import PlutusCore.Normalize.Internal qualified as Norm
import PlutusCore.Quote (MonadQuote (liftQuote), freshTyName)
import PlutusCore.Rename (Dupable, Rename (rename), dupable, liftDupable)
import PlutusPrelude (Lens', lens, over, view, void, zipExact, (<<$>>), (<<*>>), (^.))

import Control.Lens (Ixed (ix), makeClassy, makeLenses, preview, (^?))
import Control.Monad (when)
import Control.Monad.Except (MonadError, throwError)

-- Using @transformers@ rather than @mtl@, because the former doesn't impose the 'Monad' constraint
-- on 'local'.
import Control.Monad.Trans.Reader (ReaderT (runReaderT), ask, local)
import Data.Array (Array, Ix)
import Data.Foldable (for_)
import Data.List.Extras (wix)
import Data.Text qualified as Text
import Universe.Core (GEq, Some (Some), SomeTypeIn (SomeTypeIn), ValueOf (ValueOf))

{- Note [Global uniqueness in the type checker]
WARNING: type inference/checking works under the assumption that the global uniqueness condition
is satisfied. The invariant is not checked, enforced or automatically fulfilled. So you must ensure
that the global uniqueness condition is satisfied before calling 'inferTypeM' or 'checkTypeM'.

The invariant is preserved. In future we will enforce the invariant.
-}

{- Note [Typing rules]
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

-- | Mapping from 'Builtin's to their 'Normalized' 'Type's.
newtype BuiltinTypes uni fun = BuiltinTypes
  { unBuiltinTypes :: Array fun (Dupable (Normalized (Type TyName uni ())))
  }

type TyVarKinds = UniqueMap TypeUnique (Named (Kind ()))
type VarTypes uni = UniqueMap TermUnique (Named (Dupable (Normalized (Type TyName uni ()))))

{-| Decides what to do upon encountering a variable whose name doesn't match the name of the
variable with the same unique that is currently in the scope. Consider for example this type:

    \(a_0 :: *) (b_0 :: *) -> a_0

here @b_0@ shadows @a_0@ and so any variable having the @0@th unique within the body of the
lambda references @b_0@, but we have @a_0@ there and so there's a name mismatch. Technically,
it's not a type error to have a name mismatch, because uniques are the single source of truth,
however a name mismatch is deeply suspicious and is likely to be caused by a bug somewhere.

We perform the same check for term-level variables too. -}
data HandleNameMismatches
  = -- | Throw upon encountering such a name.
    DetectNameMismatches
  | -- | Ignore it.
    IgnoreNameMismatches
  deriving stock (Show, Eq)

{- Note [Alignment of kind and type checker configs]
Kind checking is performed as a part of type checking meaning we always need a kind checking config
whenever a type checking one is required. There are three ways we can align the two sorts of config:

1. store them separately and require the caller to provide both
2. put the type checking config into the kind checking config
3. put the kind checking config into the type checking config

1 is straightforward, but makes the caller provide one config for kind checking and two configs for
type checking, which is inconsistent boilerplate and so it's not really a good option.

2 is better: it makes the caller provide only one config: the type checking config stored in the
kind checking config. However that makes the type signatures unwieldy:

    KindCheckConfig (TypeCheckConfig uni fun) => <...>

plus it's kinda weird to put the type checking config inside the kind checking one.

3 is what we choose. It makes the caller only worry about the type checking config when doing type
checking, hence no syntactical or semantical overhead, plus it makes the type signatures symmetric:

    (MonadKindCheck err term uni fun ann m, HasKindCheckConfig cfg) => <...>

vs

    (MonadTypeCheck err term uni fun ann m, HasTypeCheckConfig cfg uni fun) => <...>

This approach does require a bit of boilerplate at the definition site (see 'HasTypeCheckConfig'),
but it's not much and it doesn't proliferate into user space unlike with the other approaches.
-}

-- | Configuration of the kind checker.
newtype KindCheckConfig = KindCheckConfig
  { _kccHandleNameMismatches :: HandleNameMismatches
  }

makeClassy ''KindCheckConfig

-- | Configuration of the type checker.
data TypeCheckConfig uni fun = TypeCheckConfig
  { _tccKindCheckConfig :: KindCheckConfig
  , _tccBuiltinTypes :: BuiltinTypes uni fun
  }

{-| We want 'HasKindCheckConfig' to be a superclass of 'HasTypeCheckConfig' for being able to
seamlessly call the kind checker from the type checker, hence we're rolling out our own
'makeClassy' here just to add the constraint. -}
class HasKindCheckConfig cfg => HasTypeCheckConfig cfg uni fun | cfg -> uni fun where
  typeCheckConfig :: Lens' cfg (TypeCheckConfig uni fun)

  tccKindCheckConfig :: Lens' cfg KindCheckConfig
  tccKindCheckConfig =
    typeCheckConfig . lens _tccKindCheckConfig (\s b -> s {_tccKindCheckConfig = b})

  tccBuiltinTypes :: Lens' cfg (BuiltinTypes uni fun)
  tccBuiltinTypes =
    typeCheckConfig . lens _tccBuiltinTypes (\s b -> s {_tccBuiltinTypes = b})

instance HasKindCheckConfig (TypeCheckConfig uni fun) where
  kindCheckConfig = tccKindCheckConfig

instance HasTypeCheckConfig (TypeCheckConfig uni fun) uni fun where
  typeCheckConfig = id

-- | The environment that the type checker runs in.
data TypeCheckEnv uni fun cfg = TypeCheckEnv
  { _tceTypeCheckConfig :: cfg
  , _tceTyVarKinds :: TyVarKinds
  , _tceVarTypes :: VarTypes uni
  }

makeLenses ''TypeCheckEnv

{-| The type checking monad that the type checker runs in.
In contains a 'TypeCheckEnv' and allows to throw 'TypeError's. -}
type TypeCheckT uni fun cfg m = ReaderT (TypeCheckEnv uni fun cfg) m

-- | The constraints that are required for kind checking.
type MonadKindCheck err term uni fun ann m =
  ( MonadError err m -- Kind/type checking can fail
  , ToKind uni -- For getting the kind of a built-in type.
  )

-- | The general constraints that are required for type checking a Plutus AST.
type MonadTypeCheck err term uni fun ann m =
  ( MonadKindCheck err term uni fun ann m -- Kind checking is run during type checking (this
  -- includes the constraint for throwing errors).
  , Norm.MonadNormalizeType uni m -- Type lambdas open up type computation.
  , AnnotateCaseBuiltin uni
  , GEq uni -- For checking equality of built-in types.
  , Ix fun -- For indexing into the precomputed array of
  -- types of built-in functions.
  )

-- | The PLC type error type.
type TypeErrorPlc uni fun ann = TypeError (Term TyName Name uni fun ()) uni fun ann

-- | The constraints that are required for type checking Plutus Core.
type MonadTypeCheckPlc uni fun ann m =
  MonadTypeCheck
    (TypeErrorPlc uni fun ann)
    (Term TyName Name uni fun ())
    uni
    fun
    ann
    m

-- #########################
-- ## Auxiliary functions ##
-- #########################

{-| Run a 'TypeCheckM' computation by supplying a 'TypeCheckConfig' to it.

Used for both type and kind checking, because we need to do kind checking during type checking
and so it makes sense to keep a single monad. However type checking requires a 'TypeCheckConfig',
while kind checking doesn't, hence we keep the kind checker fully polymorphic over the type of
config, so that the kinder checker can be run with an empty config (such as @()@) and access to
a 'TypeCheckConfig' is not needed. -}
runTypeCheckM :: cfg -> TypeCheckT uni fun cfg m a -> m a
runTypeCheckM config a = runReaderT a $ TypeCheckEnv config mempty mempty

-- | Extend the context of a 'TypeCheckM' computation with a kinded variable.
withTyVar :: TyName -> Kind () -> TypeCheckT uni fun cfg m a -> TypeCheckT uni fun cfg m a
withTyVar name = local . over tceTyVarKinds . insertNamed name

-- | Look up the type of a built-in function.
lookupBuiltinM
  :: (MonadTypeCheck (TypeError term uni fun ann) term uni fun ann m, HasTypeCheckConfig cfg uni fun)
  => ann -> fun -> TypeCheckT uni fun cfg m (Normalized (Type TyName uni ()))
lookupBuiltinM ann fun = do
  BuiltinTypes arr <- view $ tceTypeCheckConfig . tccBuiltinTypes
  -- Believe it or not, but 'Data.Array' doesn't seem to expose any way of indexing into an array
  -- safely.
  case preview (ix fun) arr of
    Nothing -> throwError $ UnknownBuiltinFunctionE ann fun
    Just ty -> liftDupable ty

-- | Extend the context of a 'TypeCheckM' computation with a typed variable.
withVar
  :: Name
  -> Normalized (Type TyName uni ())
  -> TypeCheckT uni fun cfg m a
  -> TypeCheckT uni fun cfg m a
withVar name = local . over tceVarTypes . insertNamed name . dupable

-- | Look up a type variable in the current context.
lookupTyVarM
  :: (MonadKindCheck (TypeError term uni fun ann) term uni fun ann m, HasKindCheckConfig cfg)
  => ann -> TyName -> TypeCheckT uni fun cfg m (Kind ())
lookupTyVarM ann name = do
  env <- ask
  let handleNameMismatches = env ^. tceTypeCheckConfig . kccHandleNameMismatches
  case lookupName name $ _tceTyVarKinds env of
    Nothing -> throwError $ FreeTypeVariableE ann name
    Just (Named nameOrig kind) ->
      if handleNameMismatches == IgnoreNameMismatches || view theText name == nameOrig
        then pure kind
        else
          throwError $
            TyNameMismatch ann (TyName . Name nameOrig $ name ^. theUnique) name

-- | Look up a term variable in the current context.
lookupVarM
  :: (MonadTypeCheck (TypeError term uni fun ann) term uni fun ann m, HasTypeCheckConfig cfg uni fun)
  => ann -> Name -> TypeCheckT uni fun cfg m (Normalized (Type TyName uni ()))
lookupVarM ann name = do
  env <- ask
  let handleNameMismatches =
        env ^. tceTypeCheckConfig . tccKindCheckConfig . kccHandleNameMismatches
  case lookupName name $ _tceVarTypes env of
    Nothing -> throwError $ FreeVariableE ann name
    Just (Named nameOrig ty) ->
      if handleNameMismatches == IgnoreNameMismatches || view theText name == nameOrig
        then liftDupable ty
        else
          throwError $
            NameMismatch ann (Name nameOrig $ name ^. theUnique) name

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
  => Normalized (Type TyName uni ())
  -- ^ @ty@
  -> TyName
  -- ^ @name@
  -> Type TyName uni ()
  -- ^ @body@
  -> TypeCheckT uni fun cfg m (Normalized (Type TyName uni ()))
substNormalizeTypeM ty name body = Norm.runNormalizeTypeT $ Norm.substNormalizeTypeM ty name body

-- ###################
-- ## Kind checking ##
-- ###################

-- | Infer the kind of a type.
inferKindM
  :: (MonadKindCheck (TypeError term uni fun ann) term uni fun ann m, HasKindCheckConfig cfg)
  => Type TyName uni ann -> TypeCheckT uni fun cfg m (Kind ())
-- b :: k
-- ------------------------
-- [infer| G !- con b :: k]
inferKindM (TyBuiltin _ (SomeTypeIn uni)) =
  pure $ kindOfBuiltinType uni
-- [infer| G !- v :: k]
-- ------------------------
-- [infer| G !- var v :: k]
inferKindM (TyVar ann v) =
  lookupTyVarM ann v
-- [infer| G , n :: dom !- body :: cod]
-- -------------------------------------------------
-- [infer| G !- (\(n :: dom) -> body) :: dom -> cod]
inferKindM (TyLam _ n dom body) = do
  let dom_ = void dom
  withTyVar n dom_ $ KindArrow () dom_ <$> inferKindM body

-- [infer| G !- fun :: dom -> cod]    [check| G !- arg :: dom]
-- -----------------------------------------------------------
-- [infer| G !- fun arg :: cod]
inferKindM (TyApp ann fun arg) = do
  funKind <- inferKindM fun
  case funKind of
    KindArrow _ dom cod -> do
      checkKindM ann arg dom
      pure cod
    _ -> do
      let expectedKindArrow = ExpectedShape "fun k l" ["k", "l"]
      throwError $ KindMismatch ann (void fun) expectedKindArrow funKind

-- [check| G !- a :: *]    [check| G !- b :: *]
-- --------------------------------------------
-- [infer| G !- a -> b :: *]
inferKindM (TyFun ann dom cod) = do
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
inferKindM (TyIFix ann pat arg) = do
  k <- inferKindM arg
  checkKindM ann pat $ toPatFuncKind k
  pure $ Type ()

-- s_0 = [p_0_0 ... p_0_m]   [check| G !- p_0_0 :: *] ... [check| G !- p_0_m :: *]
-- ...
-- s_n = [p_n_0 ... p_n_m]   [check| G !- p_n_0 :: *] ... [check| G !- p_n_m :: *]
-- -------------------------------------------------------------------------------
-- [infer| G !- sop s_0 ... s_n :: *]
inferKindM (TySOP ann tyls) = do
  for_ tyls $ \tyl -> for_ tyl $ \ty -> checkKindM ann ty (Type ())
  pure $ Type ()

-- | Check a 'Type' against a 'Kind'.
checkKindM
  :: (MonadKindCheck (TypeError term uni fun ann) term uni fun ann m, HasKindCheckConfig cfg)
  => ann -> Type TyName uni ann -> Kind () -> TypeCheckT uni fun cfg m ()
-- [infer| G !- ty : tyK]    tyK ~ k
-- ---------------------------------
-- [check| G !- ty : k]
checkKindM ann ty k = do
  tyK <- inferKindM ty
  when (tyK /= k) $ throwError (KindMismatch ann (void ty) (ExpectedExact k) tyK)

-- ###################
-- ## Type checking ##
-- ###################

-- | @unfoldIFixOf pat arg k = NORM (vPat (\(a :: k) -> ifix vPat a) arg)@
unfoldIFixOf
  :: MonadNormalizeType uni m
  => Normalized (Type TyName uni ())
  -- ^ @vPat@
  -> Normalized (Type TyName uni ())
  -- ^ @vArg@
  -> Kind ()
  -- ^ @k@
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
  -- behavior, see https://github.com/IntersectMBO/plutus/pull/2219#issuecomment-672815272
  -- But breaking global uniqueness is a bad idea regardless.
  vPat' <- rename vPat
  normalizeTypeM $
    mkIterTyAppNoAnn
      vPat'
      [ TyLam () a k . TyIFix () vPat $ TyVar () a
      , vArg
      ]

-- See Note [Global uniqueness in the type checker].
-- See Note [Typing rules].
-- | Synthesize the type of a term, returning a normalized type.
inferTypeM
  :: (MonadTypeCheckPlc uni fun ann m, HasTypeCheckConfig cfg uni fun)
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
    _ -> do
      let expectedTyFun = ExpectedShape "fun k l" ["k", "l"]
      throwError (TypeMismatch ann (void fun) expectedTyFun vFunTy)

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
    _ -> do
      let expectedTyForall = ExpectedShape "all a kind body" ["a", "kind", "body"]
      throwError (TypeMismatch ann (void body) expectedTyForall vBodyTy)

-- [infer| G !- arg :: k]    [check| G !- pat :: (k -> *) -> k -> *]    pat ~> vPat    arg ~> vArg
-- [check| G !- term : NORM (vPat (\(a :: k) -> ifix vPat a) vArg)]
-- -----------------------------------------------------------------------------------------------
-- [infer| G !- iwrap pat arg term : ifix vPat vArg]
inferTypeM (IWrap ann pat arg term) = do
  k <- inferKindM arg
  checkKindM ann pat $ toPatFuncKind k
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
    _ -> do
      let expectedTyIFix = ExpectedShape "ifix pat arg" ["pat", "arg"]
      throwError (TypeMismatch ann (void term) expectedTyIFix vTermTy)

-- [check| G !- ty :: *]    ty ~> vTy
-- ----------------------------------
-- [infer| G !- error ty : vTy]
inferTypeM (Error ann ty) = do
  checkKindM ann ty $ Type ()
  normalizeTypeM $ void ty

-- resTy ~> vResTy     vResTy = sop s_0 ... s_i ... s_n
-- s_i = [p_i_0 ... p_i_m]   [check| G !- t_0 : p_i_0] ... [check| G !- t_m : p_i_m]
-- ---------------------------------------------------------------------------------
-- [infer| G !- constr resTy i t_0 ... t_m : vResTy]
inferTypeM t@(Constr ann resTy i args) = do
  vResTy <- normalizeTypeM $ void resTy

  -- We don't know exactly what to expect, we only know what the i-th sum should look like, so we
  -- assert that we should have some types in the sum up to there, and then the known product type.
  let
    -- 'toInteger' is necessary, because @i@ is a @Word64@ and therefore @i - 1@ would be
    -- @maxBound :: Word64@ for @i = 0@ if we didn't have 'toInteger'.
    prodPrefix = map (\j -> "prod_" <> Text.pack (show j)) [0 .. toInteger i - 1]
    fields = map (\k -> "field_" <> Text.pack (show k)) [0 .. length args - 1]
    prod_i = "[" <> Text.intercalate " " fields <> "]"
    shape = "sop " <> foldMap (<> " ") prodPrefix <> prod_i <> " ..."
    vars = prodPrefix ++ fields
    expectedSop = ExpectedShape shape vars
  case unNormalized vResTy of
    TySOP _ vSTys -> case vSTys ^? wix i of
      Just pTys -> case zipExact args pTys of
        -- pTy is a sub-part of a normalized type, so normalized
        Just ps -> for_ ps $ \(arg, pTy) -> checkTypeM ann arg (Normalized pTy)
        -- the number of args does not match the number of types in the i'th SOP
        -- alternative
        Nothing -> throwError (TypeMismatch ann (void t) expectedSop vResTy)
      -- result type does not contain an i'th sum alternative
      Nothing -> throwError (TypeMismatch ann (void t) expectedSop vResTy)
    -- result type is not a SOP type
    _ -> throwError (TypeMismatch ann (void t) expectedSop vResTy)

  pure vResTy

-- resTy ~> vResTy   [infer| G !- scrut : sop s_0 ... s_n]
-- s_0 = [p_0_0 ... p_0_m]   [check| G !- c_0 : p_0_0 -> ... -> p_0_m -> vResTy]
-- ...
-- s_n = [p_n_0 ... p_n_m]   [check| G !- c_n : p_n_0 -> ... -> p_n_m -> vResTy]
-- -----------------------------------------------------------------------------
-- [infer| G !- case resTy scrut c_0 ... c_n : vResTy]
inferTypeM (Case ann resTy scrut branches) = do
  vResTy <- normalizeTypeM $ void resTy
  vScrutTy <- inferTypeM scrut

  -- We don't know exactly what to expect, we only know that it should
  -- be a SOP with the right number of sum alternatives when type of scrutinee is SOP
  let prods = map (\j -> "prod_" <> Text.pack (show j)) [0 .. length branches - 1]
      expectedSop = ExpectedShape (Text.intercalate " " $ "sop" : prods) prods
  case unNormalized vScrutTy of
    TySOP _ sTys -> case zipExact branches sTys of
      Just branchesAndArgTypes -> for_ branchesAndArgTypes $ \(c, argTypes) ->
        -- made of sub-parts of a normalized type, so normalized
        checkTypeM ann c (Normalized $ mkIterTyFun () argTypes (unNormalized vResTy))
      -- scrutinee does not have a SOP type with the right number of alternatives
      -- for the number of branches
      Nothing -> throwError (TypeMismatch ann (void scrut) expectedSop vScrutTy)
    vTy -> case annotateCaseBuiltin vTy branches of
      Right branchesAndArgTypes -> for_ branchesAndArgTypes $ \(c, argTypes) -> do
        vArgTypes <- traverse (fmap unNormalized . normalizeTypeM) argTypes
        -- made of sub-parts of a normalized type, so normalized
        checkTypeM ann c (Normalized $ mkIterTyFun () vArgTypes (unNormalized vResTy))
      Left err -> throwError $ UnsupportedCaseBuiltin ann err

  -- If we got through all that, then every case type is correct, including that
  -- they all result in vResTy, so we can safely conclude that that is the type of the
  -- whole expression.
  pure vResTy

-- See Note [Global uniqueness in the type checker].
-- See Note [Typing rules].
-- | Check a 'Term' against a 'NormalizedType'.
checkTypeM
  :: (MonadTypeCheckPlc uni fun ann m, HasTypeCheckConfig cfg uni fun)
  => ann
  -> Term TyName Name uni fun ann
  -> Normalized (Type TyName uni ())
  -> TypeCheckT uni fun cfg m ()
-- [infer| G !- term : vTermTy]    vTermTy ~ vTy
-- ---------------------------------------------
-- [check| G !- term : vTy]
checkTypeM ann term vTy = do
  vTermTy <- inferTypeM term
  when (vTermTy /= vTy) $ do
    let expectedVTy = ExpectedExact $ unNormalized vTy
    throwError $ TypeMismatch ann (void term) expectedVTy vTermTy
