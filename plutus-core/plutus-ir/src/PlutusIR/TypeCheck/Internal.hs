-- | The internal module of the type checker that defines the actual algorithms,
-- but not the user-facing API.

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeOperators      #-}
module PlutusIR.TypeCheck.Internal
    ( BuiltinTypes (..)
    , TypeCheckConfig (..)
    , TypeCheckM
    , tccBuiltinTypes
    , PirTCConfig (..)
    , AllowEscape (..)
    , inferTypeM
    , checkTypeM
    , runTypeCheckM
    ) where


import           Control.Monad.Error.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Foldable
import           Data.Ix
import           PlutusCore                    (ToKind (..), typeAnn)
import           PlutusCore.Error              as PLC
import           PlutusCore.Quote
import           PlutusCore.Rename             as PLC
import           PlutusCore.Universe
import           PlutusIR
import           PlutusIR.Compiler.Datatype
import           PlutusIR.Compiler.Provenance
import           PlutusIR.Compiler.Types
import           PlutusIR.Error
import           PlutusIR.Transform.Rename     ()
import           PlutusPrelude

-- we mirror inferTypeM, checkTypeM of plc-tc and extend it for plutus-ir terms
import           PlutusCore.TypeCheck.Internal hiding (checkTypeM, inferTypeM, runTypeCheckM)
import qualified PlutusIR.MkPir                as PIR

{- Note [PLC Typechecker code reuse]
For PIR kind-checking, we reuse `checkKindM`, `inferKindM` directly from the PLC typechecker.
For PIR type-checking, we port the `checkTypeM` and `inferTypeM` from PLC typechecker.
The port is a direct copy, except for the modifications of `Term` to `PIR.Term`
and error type signatures and `throwError` to accomodate for the new pir type-errors.
These modifications are currently necesessary since PIR.Term ADT /= PLC.Term ADT.
We then extend this ported `PIR.inferTypeM` with cases for inferring type of LetRec and LetNonRec.

See Note [Notation] of PlutusCore.TypeCheck.Internal for the notation of inference rules, which appear in the comments.
-}

{- Note [PIR vs Paper Syntax Difference]
Link to the paper: <https://hydra.iohk.io/job/Cardano/plutus/linux.papers.unraveling-recursion/latest/download-by-type/doc-pdf/unraveling-recursion>
FIR's syntax requires that the data-constructor is annotated with a *list of its argument types* (domain),
instead of requiring a single valid type T (usually in the form `dataconstr : arg1 -> arg2 ->... argn`)
The codomain is also left out of the syntax and implied to be of the type `[TypeCons tyarg1 tyarg2 ... tyargn]`
(what would be expected for a non-GADT). Finally, the leading "forall type-parameters" are implicit (since they are consider in scope).

PIR's syntax requires that a full (valid) type is written for the data-constructor, using the syntax for types
(the forall type-parameters remains implicit). This means that the codomain has to be be explicitly given in PIR.
To make sure that the PIR-user has written down the expected non-GADT type we do an extra codomainCheck.
This codomainCheck will have to be relaxed if/when PIR introduces GADTs.
More importantly, since the type for the PIR data-constructor can be any syntax-valid type,
the PIR user may have placed inside there a non-normalized type there. Currently, the PIR typechecker will
assume the types of all data-constructors are prior normalized *before* type-checking, otherwise
the PIR typechecking and PIR compilation will fail.
See NOTE [Normalization of data-constructors' types] at PlutusIR.Compiler.Datatype
-}

{- Note [PIR vs Paper Escaping Types Difference]
Link to the paper: <https://hydra.iohk.io/job/Cardano/plutus/linux.papers.unraveling-recursion/latest/download-by-type/doc-pdf/unraveling-recursion>
In FIR paper's Fig.6, T-Let and T-LetRec rules dictate that: Gamma !- inTerm :: * for two reasons:
1. check (locally) that the kind of the in-term's inferred type is indeed *
2. ensure that the inferred type does not escaping its scope (hence Gamma)

This is in general true for the PIR implementation as well, except in the special
case when a Type is inferred for the top-level expression (`program`-level).
In contrast to (2), we allow such a "top-level" type to escape its scope;
the reasoning is that PIR programs with toplevel escaping types would behave correctly when they are translated down to PLC.
Even in the case where we let the type variables escape, (1) must still hold:
the kind of the escaping type should still be star. Unfortunately, in order to check that we'd have to use the variables
which are no longer in scope. So we skip the rule (Gamma !- inTermTopLevel :: *) in case of top-level inferred types.

The implementation has a user-configurable flag to let the typechecker know if the current term under examination
is at the program's "top-level" position, and thus allow its type to escape. The flag is automatically set to no-type-escape
when typechecking inside a let termbind's rhs term.
-}

-- | a shorthand for our pir-specialized tc functions
type PirTCEnv uni fun e a = TypeCheckM uni fun (PirTCConfig uni fun) e a

-- ###########################
-- ## Port of Type checking ##
-- ##########################
--  Taken from `PlutusCore.Typecheck.Internal`

-- See the [Global uniqueness] and [Type rules] notes.
-- | Check a 'Term' against a 'NormalizedType'.
checkTypeM
    :: (GShow uni, GEq uni, Ix fun, AsTypeErrorExt e uni ann, AsTypeError e (Term TyName Name uni fun ()) uni fun ann, ToKind uni)
    => ann -> Term TyName Name uni fun ann -> Normalized (Type TyName uni ()) -> PirTCEnv uni fun e ()
-- [infer| G !- term : vTermTy]    vTermTy ~ vTy
-- ---------------------------------------------
-- [check| G !- term : vTy]
checkTypeM ann term vTy = do
    vTermTy <- inferTypeM term
    when (vTermTy /= vTy) $ throwing _TypeError (TypeMismatch ann (void term) (unNormalized vTermTy) vTy)

-- See the [Global uniqueness] and [Type rules] notes.
-- | Synthesize the type of a term, returning a normalized type.
inferTypeM
    :: forall uni fun ann e. (GShow uni, GEq uni, Ix fun, AsTypeError e (Term TyName Name uni fun ()) uni fun ann, ToKind uni, AsTypeErrorExt e uni ann)
    => Term TyName Name uni fun ann -> PirTCEnv uni fun e (Normalized (Type TyName uni ()))
-- c : vTy
-- -------------------------
-- [infer| G !- con c : vTy]
inferTypeM (Constant _ (Some (ValueOf uni _))) =
    -- See Note [PLC types and universes].
    pure . Normalized . TyBuiltin () $ Some (TypeIn uni)

-- [infer| G !- bi : vTy]
-- ------------------------------
-- [infer| G !- builtin bi : vTy]
inferTypeM (Builtin ann bn)         =
    lookupBuiltinM ann bn

-- [infer| G !- v : ty]    ty ~> vTy
-- ---------------------------------
-- [infer| G !- var v : vTy]
inferTypeM (Var ann name)           =
    lookupVarM ann name

-- [check| G !- dom :: *]    dom ~> vDom    [infer| G , n : dom !- body : vCod]
-- ----------------------------------------------------------------------------
-- [infer| G !- lam n dom body : vDom -> vCod]
inferTypeM (LamAbs ann n dom body)  = do
    checkKindM ann dom $ Type ()
    vDom <- normalizeTypeM $ void dom
    TyFun () <<$>> pure vDom <<*>> withVar n vDom (inferTypeM body)

-- [infer| G , n :: nK !- body : vBodyTy]
-- ---------------------------------------------------
-- [infer| G !- abs n nK body : all (n :: nK) vBodyTy]
inferTypeM (TyAbs _ n nK body)      = do
    let nK_ = void nK
    TyForall () n nK_ <<$>> withTyVar n nK_ (inferTypeM body)

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
        _ -> throwing _TypeError (TypeMismatch ann (void fun) (TyFun () dummyType dummyType) vFunTy)

-- [infer| G !- body : all (n :: nK) vCod]    [check| G !- ty :: tyK]    ty ~> vTy
-- -------------------------------------------------------------------------------
-- [infer| G !- body {ty} : NORM ([vTy / n] vCod)]
inferTypeM (TyInst ann body ty)     = do
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
inferTypeM (Unwrap ann term)        = do
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
inferTypeM (Error ann ty)           = do
    checkKindM ann ty $ Type ()
    normalizeTypeM $ void ty
-- ##############
-- ## Port end ##
-- ##############

-- Note on symbols:  '=>' means implies

{-
checkKindFromBinding(G,b) checkTypeFromBinding(G,b)
!null(bs) => [infer| G,withVarsOfBinding(b),withTyVarsOfBinding(b) !- (let nonrec {bs} in inT) : ty]
null(bs) => [infer| G,withVarsOfBinding(b),withTyVarsOfBinding(b) !- inT : ty]
ty ~> vTy
-------------------------------------------------
[infer| G !- (let nonrec {b ; bs} in inT) : vTy]
-}
inferTypeM (Let ann r@NonRec bs inTerm) = do
    -- Check each binding individually, then if ok, introduce its new type/vars to the (linearly) next let or inTerm
    ty <- foldr checkBindingThenScope (inferTypeM inTerm) bs
    -- check the in-term's inferred type has kind * (except at toplevel)
    checkStarInferred ann ty
    pure ty
 where
   checkBindingThenScope :: Binding TyName Name uni fun ann -> PirTCEnv uni fun e res -> PirTCEnv uni fun e res
   checkBindingThenScope b acc = do
       -- check that the kinds of the declared types are correct
       checkKindFromBinding b
       -- check that the types of declared terms are correct
       checkTypeFromBinding r b
       -- add new *normalized* termvariables to env
       -- Note that the order of adding typesVSkinds here does not matter
       withTyVarsOfBinding b $
           withVarsOfBinding r b acc

{-
G'=G,withTyVarsOfBindings(bs)
forall b in bs. checkKindFromBinding(G', b)
G''=G',withVarsOfBindings(bs)
forall b in bs. checkTypeFromBinding(G'', b)
[infer| G'' !- inT : ty] ty ~> vTy
-------------------------------------------------
[infer| G !- (let rec bs in inT) : vTy]
-}
inferTypeM (Let ann r@Rec bs inTerm) = do
    ty <- withTyVarsOfBindings bs $ do
       -- check that the kinds of the declared types *over all bindings* are correct
       -- Note that, compared to NonRec, we need the newtyvars in scope to do kindchecking
       for_ bs checkKindFromBinding
       withVarsOfBindings r bs $ do
              -- check that the types of declared terms are correct
              -- Note that, compared to NonRec, we need the newtyvars+newvars in scope to do typechecking
              for_ bs $ checkTypeFromBinding r
              inferTypeM inTerm
    -- check the in-term's inferred type has kind * (except at toplevel)
    checkStarInferred ann ty
    pure ty

{-| This checks that a newly-introduced type variable is correctly kinded.

(b is ty::K = rhs) => [check| G !- rhs :: K]
(b is term (X::T) => [check| G !- T :: *])
(b is data (X::K) tyarg1::K1 ... tyargN::KN  = _) => [check| G, X::K, tyarg1::K1...tyargN::KN !- [X tyarg1 ... tyargN] :: *]
--------------------------------------------------------------------------------------
checkKindFromBinding(G,b)
-}
checkKindFromBinding :: forall e uni fun ann.
                   (AsTypeError e (Term TyName Name uni fun ()) uni fun ann, ToKind uni)
                 => Binding TyName Name uni fun ann
                 -> PirTCEnv uni fun e ()
checkKindFromBinding = \case
    -- For a type binding, correct means that the the RHS is indeed kinded by the declared kind.
    TypeBind _ (TyVarDecl ann _ k) rhs ->
        checkKindM ann rhs $ void k
    -- For a term binding, correct means that the declared type has kind *.
    TermBind _ _ (VarDecl _ _ ty) _ ->
        checkKindM (typeAnn ty) ty $ Type ()
    -- For a datatype binding, correct means that the type constructor has kind * when fully-applied to its type arguments.
    DatatypeBind _ dt@(Datatype ann tycon tyargs _ vdecls) ->
        -- tycon+tyargs must be in scope during kindchecking
        withTyVarDecls (tycon:tyargs) $ do
          -- the fully-applied type-constructor must be *-kinded
          checkKindM ann appliedTyCon $ Type ()
          -- the types of all the data-constructors must be *-kinded
          for_ (varDeclType <$> vdecls) $
               checkKindM ann `flip` Type ()
     where
       appliedTyCon :: Type TyName uni ann = mkDatatypeValueType ann dt


{- | This checks that a newly-introduced variable has declared the *right type* for its term
(rhs term in case of termbind or implicit constructor term in case of dataconstructor).

(b is t:ty = _) => [check| G !- t : nTy]  ty ~> vTy
---------------------------------------------------
checkTypeFromBinding(G,b)
-}
checkTypeFromBinding :: forall e uni fun a. (GShow uni, GEq uni, Ix fun, AsTypeError e (Term TyName Name uni fun ()) uni fun a, ToKind uni, AsTypeErrorExt e uni a)
                 => Recursivity -> Binding TyName Name uni fun a -> PirTCEnv uni fun e ()
checkTypeFromBinding recurs = \case
    TypeBind{} -> pure () -- no types to check
    TermBind _ _ (VarDecl ann _ ty) rhs ->
        -- See Note [PIR vs Paper Escaping Types Difference]
        withNoEscapingTypes (checkTypeM ann rhs . fmap void =<< normalizeTypeM ty)
    DatatypeBind _ dt@(Datatype ann _ tyargs _ constrs) ->
        for_ (varDeclType <$> constrs) $
            \ ty -> checkConRes ty *> checkNonRecScope ty
      where
       appliedTyCon :: Type TyName uni a = mkDatatypeValueType ann dt
       checkConRes :: Type TyName uni a -> PirTCEnv uni fun e ()
       checkConRes ty =
           -- We earlier checked that datacons' type is *-kinded (using checkKindBinding), but this is not enough:
           -- we must also check that its result type is EXACTLY `[[TypeCon tyarg1] ... tyargn]`
           when (funResultType ty /= appliedTyCon) .
               throwing _TypeErrorExt $ MalformedDataConstrResType ann appliedTyCon

       -- if nonrec binding, make sure that type-constructor is not part of the data-constructor's argument types.
       checkNonRecScope :: Type TyName uni a -> PirTCEnv uni fun e ()
       checkNonRecScope ty = case recurs of
           Rec -> pure ()
           NonRec ->
               -- now we make sure that dataconstructor is not self-recursive, i.e. funargs don't contain tycon
               withTyVarDecls tyargs $ -- tycon not in scope here
                      -- OPTIMIZE: we use inferKind for scope-checking, but a simple ADT-traversal would suffice
                      for_ (funTyArgs ty) inferKindM

-- | Check that the in-Term's inferred type of a Let has kind *.
-- Skip this check at the top-level, to allow top-level types to escape; see Note [PIR vs Paper Escaping Types Difference].
checkStarInferred :: (AsTypeError e term uni fun ann, ToKind uni)
                  => ann -> Normalized (Type TyName uni b) -> PirTCEnv uni fun e ()
checkStarInferred ann t = do
    allowEscape <- view $ tceTypeCheckConfig . pirConfigAllowEscape
    case allowEscape of
        NoEscape  -> checkKindM ann (ann <$ unNormalized t) $ Type ()
        -- NOTE: we completely skip the check in case of toplevel because we would need an *final, extended Gamma environment*
        -- to run the kind-check in, but we cannot easily get that since we are using a Reader for environments and not State
        YesEscape -> pure ()


-- | Changes the flag in nested-lets so to disallow returning a type outside of the type's scope
withNoEscapingTypes :: PirTCEnv uni fun e a -> PirTCEnv uni fun e a
withNoEscapingTypes = local $ set (tceTypeCheckConfig.pirConfigAllowEscape) NoEscape

-- | Run a 'TypeCheckM' computation by supplying a 'TypeCheckConfig' to it.
-- Differs from its PLC version in that is passes an extra env flag 'YesEscape'.
runTypeCheckM :: (MonadError e m, MonadQuote m)
              => PirTCConfig uni fun -> PirTCEnv uni fun e a -> m a
runTypeCheckM config a =
    liftEither =<< liftQuote (runExceptT $ runReaderT a env) where
        env = TypeCheckEnv config mempty mempty

-- Helpers
----------

-- | For a single binding, generate the newly-introduce term-variables' types,
-- normalize them, rename them and add them into scope.
-- Newly-declared term variables are: variables of termbinds, constructors, destructor
-- Note: Assumes that the input is globally-unique and preserves global-uniqueness
-- Note to self: actually passing here recursivity is unnecessary, but we do it for sake of compiler/datatype.hs api
withVarsOfBinding :: forall uni fun c e a res.
                    Recursivity -> Binding TyName Name uni fun a
                  -> TypeCheckM uni fun c e res -> TypeCheckM uni fun c e res
withVarsOfBinding _ TypeBind{} k = k
withVarsOfBinding _ (TermBind _ _ vdecl _) k = do
    vTy <- normalizeTypeM $ varDeclType vdecl
    -- no need to rename here
    withVar (varDeclName vdecl) (void <$> vTy) k
withVarsOfBinding r (DatatypeBind _ dt) k = do
    -- generate all the definitions
    (_tyconstrDef, constrDefs, destrDef) <- compileDatatypeDefs r (original dt)
    -- ignore the generated rhs terms of constructors/destructor
    let structorDecls = PIR.defVar <$> destrDef:constrDefs
    -- normalize, then rename, then only introduce the vardecl to scope
    foldr normRenameScope k structorDecls
    where
      normRenameScope :: VarDecl TyName Name uni fun (Provenance a)
                      -> TypeCheckM uni fun c e res -> TypeCheckM uni fun c e res
      normRenameScope v acc = do
          normRenamedTy <- rename =<< (normalizeTypeM $ varDeclType v)
          withVar (varDeclName v) (void <$> normRenamedTy) acc


withVarsOfBindings :: Foldable t => Recursivity -> t (Binding TyName Name uni fun a)
                   -> TypeCheckM uni fun c e res -> TypeCheckM uni fun c e res
withVarsOfBindings r bs k = foldr (withVarsOfBinding r) k bs

-- | Scope a typechecking computation with the given binding's newly-introducing type (if there is one)
withTyVarsOfBinding :: Binding TyName name uni fun ann -> TypeCheckM uni fun c e res -> TypeCheckM uni fun c e res
withTyVarsOfBinding = \case
       TypeBind _ tvdecl _                      -> withTyVarDecls [tvdecl]
       DatatypeBind _ (Datatype _ tvdecl _ _ _) -> withTyVarDecls [tvdecl]
       TermBind{}                               -> id -- no type to introduce

-- | Extend the typecheck reader environment with the kinds of the newly-introduced type variables of a binding.
withTyVarsOfBindings :: Foldable f => f (Binding TyName name uni fun ann) -> TypeCheckM uni fun c e res -> TypeCheckM uni fun c e res
withTyVarsOfBindings = flip $ foldr withTyVarsOfBinding

-- | Helper to add type variables into a computation's environment.
withTyVarDecls :: [TyVarDecl TyName ann] -> TypeCheckM uni fun c e a -> TypeCheckM uni fun c e a
withTyVarDecls = flip . foldr $ \(TyVarDecl _ n k) -> withTyVar n $ void k
