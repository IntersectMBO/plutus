-- | The internal module of the type checker that defines the actual algorithms,
-- but not the user-facing API.

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE TypeOperators      #-}
module Language.PlutusIR.TypeCheck.Internal
    ( BuiltinTypes (..)
    , TypeCheckConfig (..)
    , TypeCheckM
    , tccBuiltinTypes
    , inferTypeM
    , checkTypeM
    ) where


import           Control.Monad.Error.Lens
import           Control.Monad.Except
import           Data.Foldable
import           Language.PlutusCore                    (typeAnn)
import           Language.PlutusCore.Error              as PLC
import           Language.PlutusCore.Rename             as PLC
import           Language.PlutusCore.Universe
import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Datatype
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Error
import           PlutusPrelude

-- we mirror inferTypeM, checkTypeM of plc-tc and extend it for plutus-ir terms
import           Language.PlutusCore.TypeCheck.Internal hiding (checkTypeM, inferTypeM)
import qualified Language.PlutusIR.MkPir                as PIR

{- Note [PLC Typechecker code reuse]
For PIR kind-checking, we reuse `checkKindM`, `inferKindM` directly from the PLC typechecker.
For PIR type-checking, we port the `checkTypeM` and `inferTypeM` from PLC typechecker.
The port is a direct copy, except for the modifications of `Term` to `PIR.Term`
and error type signatures and `throwError` to accomodate for the new pir type-errors.
These modifications are currently necesessary since PIR.Term ADT /= PLC.Term ADT.
We then extend this ported `PIR.inferTypeM` with cases for inferring type of LetRec and LetNonRec.

See Note [Notation] of Language.PlutusCore.TypeCheck.Internal for the notation of inference rules, which appear in the comments.
-}

{- Note [PIR vs paper FIR differences]
Link to the paper: <https://hydra.iohk.io/job/Cardano/plutus/linux.papers.unraveling-recursion/latest/download-by-type/doc-pdf/unraveling-recursion>

Difference1:

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
See NOTE [Normalization of data-constructors' types] at Language.PlutusIR.Compiler.Datatype

Difference2:

In FIR paper's Fig.6, T-Let and T-LetRec rules dictate that: G !- inTerm :: *
In the implemenetation, however, we do not have this check and instead rely
in the proof-by-construction: "All terms that can be constructed have types that are *-kinded."
-}

{- NOTE [TODO: Unexpose Escaping Types]
 The let datatypebinds and/or typebinds introduce new types which may be exposed to the user
from the "inferred type" of the PIRs' inTerm.
e.g. `let data List a = Nil | Cons a (List a) in Nil :: List Integer` will infer the overall type `List Integer`,
which exposes the List to the outside of the let.

Although such programs compile fine to PLC , are PLC typechecked and run correctly (e.g. the program at `./test/recursion/even3Eval`),
their inferred types have to be constrained in terms of PIR typechecking.

The PIR typechecker has to be modified to not expose the types of such programs (still to be implemented).
For more please see the more elaborate documentation about PIR typechecking at
<https://github.com/effectfully/plutus-prototype/blob/master/language-plutus-core/docs/Typechecking%20PIR.md>
and the discussion at <https://groups.google.com/a/iohk.io/forum/#!msg/plutus/6ycMTngVomc/VKeb00DuHwAJ>
-}


-- ###########################
-- ## Port of Type checking ##
-- ##########################
--  Taken from `Language.PlutusCore.Typecheck.Internal`

-- See the [Global uniqueness] and [Type rules] notes.
-- | Check a 'Term' against a 'NormalizedType'.
checkTypeM
    :: (GShow uni, GEq uni, DefaultUni <: uni, AsTypeErrorExt e uni ann, AsTypeError e (Term TyName Name uni fun ()) uni ann)
    => ann -> Term TyName Name uni fun ann -> Normalized (Type TyName uni ()) -> TypeCheckM uni e ()
-- [infer| G !- term : vTermTy]    vTermTy ~ vTy
-- ---------------------------------------------
-- [check| G !- term : vTy]
checkTypeM ann term vTy = do
    vTermTy <- inferTypeM term
    when (vTermTy /= vTy) $ throwing _TypeError (TypeMismatch ann (void term) (unNormalized vTermTy) vTy)

-- See the [Global uniqueness] and [Type rules] notes.
-- | Synthesize the type of a term, returning a normalized type.
inferTypeM
    :: forall uni fun ann e. (GShow uni, GEq uni, DefaultUni <: uni, AsTypeError e (Term TyName Name uni fun ()) uni ann, AsTypeErrorExt e uni ann)
    => Term TyName Name uni fun ann -> TypeCheckM uni e (Normalized (Type TyName uni ()))
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
    inferTypeOfBuiltinM ann bn

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
inferTypeM (Let _ r@NonRec bs inTerm) =
    -- Check each binding individually, then if ok, introduce its new type/vars to the (linearly) next let or inTerm
    foldr checkBindingThenScope (inferTypeM inTerm) bs
 where
   checkBindingThenScope :: Binding TyName Name uni fun ann -> TypeCheckM uni e res -> TypeCheckM uni e res
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
inferTypeM (Let _ r@Rec bs inTerm) =
    withTyVarsOfBindings bs $ do
       -- check that the kinds of the declared types *over all bindings* are correct
       -- Note that, compared to NonRec, we need the newtyvars in scope to do kindchecking
       for_ bs checkKindFromBinding
       withVarsOfBindings r bs $ do
              -- check that the types of declared terms are correct
              -- Note that, compared to NonRec, we need the newtyvars+newvars in scope to do typechecking
              for_ bs $ checkTypeFromBinding r
              inferTypeM inTerm

{-| This checks that a newly-introduced type variable is correctly kinded.

(b is ty::K = _) => [check| G !- ty :: K]
(b is term (X::T) => [check| G !- T :: *])
(b is data (X::K) tyarg1::K1 ... tyargN::KN  = _) => [check| G, X::K, tyarg1::K1...tyargN::KN !- [X tyarg1 ... tyargN] :: *]
--------------------------------------------------------------------------------------
checkKindFromBinding(G,b)
-}
checkKindFromBinding :: forall e uni fun ann.
                   AsTypeError e (Term TyName Name uni fun ()) uni ann
                 => Binding TyName Name uni fun ann
                 -> TypeCheckM uni e ()
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
          -- the types of all the data-constructors types must be *-kinded
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
checkTypeFromBinding :: forall e uni fun a. (GShow uni, GEq uni, DefaultUni <: uni, AsTypeError e (Term TyName Name uni fun ()) uni a, AsTypeErrorExt e uni a)
                 => Recursivity ->Binding TyName Name uni fun a  -> TypeCheckM uni e ()
checkTypeFromBinding recurs = \case
    TypeBind{} -> pure () -- no types to check
    TermBind _ _ (VarDecl ann _ ty) rhs ->
        checkTypeM ann rhs . fmap void =<< normalizeTypeM ty
    DatatypeBind _ dt@(Datatype ann _ tyargs _ constrs) ->
        for_ (varDeclType <$> constrs) $
            \ ty -> checkConRes ty *> checkNonRecScope ty
      where
       appliedTyCon :: Type TyName uni a = mkDatatypeValueType ann dt
       checkConRes :: Type TyName uni a -> TypeCheckM uni e ()
       checkConRes ty =
           -- We earlier checked that datacons' type is *-kinded (using checkKindBinding), but this is not enough:
           -- we must also check that its result type is EXACTLY `[[TypeCon tyarg1] ... tyargn]`
           when (funResultType ty /= appliedTyCon) .
               throwing _TypeErrorExt $ MalformedDataConstrResType ann appliedTyCon

       -- if nonrec binding, make sure that type-constructor is not part of the data-constructor's argument types.
       checkNonRecScope :: Type TyName uni a -> TypeCheckM uni e ()
       checkNonRecScope ty = case recurs of
           Rec -> pure ()
           NonRec ->
               -- now we make sure that dataconstructor is not self-recursive, i.e. funargs don't contain tycon
               withTyVarDecls tyargs $ -- tycon not in scope here
                      -- OPTIMIZE: we use inferKind for scope-checking, but a simple ADT-traversal would suffice
                      for_ (funTyArgs ty) inferKindM

-- Helpers
----------


-- | For a single binding, generate the newly-introduce term-variables' types,
-- normalize them, rename them and add them into scope.
-- Newly-declared term variables are: variables of termbinds, constructors, destructor
-- Note: Assumes that the input is globally-unique and preserves global-uniqueness
-- Note to self: actually passing here recursivity is unnecessary, but we do it for sake of compiler/datatype.hs api
withVarsOfBinding :: forall uni fun e a res.
                    Recursivity -> Binding TyName Name uni fun a
                  -> TypeCheckM uni e res -> TypeCheckM uni e res
withVarsOfBinding _ TypeBind{} k = k
withVarsOfBinding _ (TermBind _ _ vdecl _) k = do
    vTy <- normalizeTypeM $ varDeclType vdecl
    -- no need to rename here
    withVar (varDeclName vdecl) (void <$> vTy) k
withVarsOfBinding r (DatatypeBind _ dt) k = do
    -- generate all the definitions
    (_tyconstrDef, constrDefs, destrDef) <- compileDatatypeDefs r (original dt)
    -- ignore the generated rhs terms of constructors/destructor
    let structorDecls = fmap (PIR.defVar) $ destrDef:constrDefs
    -- normalize, then rename, then only introduce the vardecl to scope
    foldr normRenameScope k structorDecls
    where
      normRenameScope :: VarDecl TyName Name uni fun (Provenance a)
                      -> TypeCheckM uni e res -> TypeCheckM uni e res
      normRenameScope v acc = do
          normRenamedTy <- rename =<< (normalizeTypeM $ varDeclType v)
          withVar (varDeclName v) (void <$> normRenamedTy) acc


withVarsOfBindings :: Foldable t => Recursivity -> t (Binding TyName Name uni fun a)
                   -> TypeCheckM uni e res -> TypeCheckM uni e res
withVarsOfBindings r bs k = foldr (withVarsOfBinding r) k bs


-- | Scope a typechecking computation with the given binding's newly-introducing type (if there is one)
withTyVarsOfBinding :: Binding TyName name uni fun ann -> TypeCheckM uni e res -> TypeCheckM uni e res
withTyVarsOfBinding = \case
       TypeBind _ tvdecl _ -> withTyVarDecls [tvdecl]
       DatatypeBind _ (Datatype _ tvdecl _ _ _) -> withTyVarDecls [tvdecl]
       TermBind{} -> id -- no type to introduce

-- | Extend the typecheck reader environment with the kinds of the newly-introduced type variables of a binding.
withTyVarsOfBindings :: Foldable f => f (Binding TyName name uni fun ann) -> TypeCheckM uni e res -> TypeCheckM uni e res
withTyVarsOfBindings = flip $ foldr withTyVarsOfBinding

-- | Helper to add type variables into a computation's environment.
withTyVarDecls :: [TyVarDecl TyName ann] -> TypeCheckM uni e a -> TypeCheckM uni e a
withTyVarDecls = flip . foldr $ \(TyVarDecl _ n k) -> withTyVar n $ void k
