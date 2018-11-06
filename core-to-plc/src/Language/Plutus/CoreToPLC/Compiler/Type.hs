{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling GHC types into PlutusCore types, as well as compiling constructors,
-- matchers, and pattern match alternatives.
module Language.Plutus.CoreToPLC.Compiler.Type (
    convType,
    getDataCons,
    getConstructors,
    getConstructorsInstantiated,
    getMatch,
    getMatchInstantiated,
    convAlt,
    NewtypeCoercion (..),
    splitNewtypeCoercion) where

import           Language.Plutus.CoreToPLC.Compiler.Binders
import           Language.Plutus.CoreToPLC.Compiler.Builtins
import           Language.Plutus.CoreToPLC.Compiler.Definitions
import {-# SOURCE #-} Language.Plutus.CoreToPLC.Compiler.Expr
import           Language.Plutus.CoreToPLC.Compiler.Kind
import           Language.Plutus.CoreToPLC.Compiler.Names
import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.Compiler.Utils
import           Language.Plutus.CoreToPLC.Error
import           Language.Plutus.CoreToPLC.Laziness
import           Language.Plutus.CoreToPLC.PLCTypes
import           Language.Plutus.CoreToPLC.Utils

import qualified GhcPlugins                                     as GHC
import qualified Pair                                           as GHC
import qualified PrelNames                                      as GHC
import qualified TysPrim                                        as GHC

import qualified Language.PlutusCore                            as PLC
import qualified Language.PlutusCore.MkPlc                      as PLC
import           Language.PlutusCore.Quote

import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Foldable
import qualified Data.List.NonEmpty                             as NE
import qualified Data.Map                                       as Map
import           Lens.Micro

import           Data.List                                      (elemIndex, reverse, sortBy)

-- Types

convType :: Converting m => GHC.Type -> m PLCType
convType t = withContextM (sdToTxt $ "Converting type:" GHC.<+> GHC.ppr t) $ do
    -- See Note [Scopes]
    ConvertingContext {ccScopes=stack} <- ask
    let top = NE.head stack
    case t of
        -- in scope type name
        (GHC.getTyVar_maybe -> Just (lookupTyName top . GHC.getName -> Just (PLC.TyVarDecl _ name _))) -> pure $ PLC.TyVar () name
        (GHC.getTyVar_maybe -> Just v) -> throwSd FreeVariableError $ "Type variable:" GHC.<+> GHC.ppr v
        (GHC.splitFunTy_maybe -> Just (i, o)) -> PLC.TyFun () <$> convType i <*> convType o
        (GHC.splitTyConApp_maybe -> Just (tc, ts)) -> convTyConApp tc ts
        (GHC.splitForAllTy_maybe -> Just (tv, tpe)) -> mkTyForallScoped tv (convType tpe)
        -- I think it's safe to ignore the coercion here
        (GHC.splitCastTy_maybe -> Just (tpe, _)) -> convType tpe
        _ -> throwSd UnsupportedError $ "Type" GHC.<+> GHC.ppr t

convTyConApp :: (Converting m) => GHC.TyCon -> [GHC.Type] -> m PLCType
convTyConApp tc ts
    -- this is Int
    | tc == GHC.intTyCon = pure $ appSize haskellIntSize (PLC.TyBuiltin () PLC.TyInteger)
    -- this is Int#
    | tc == GHC.intPrimTyCon = pure $ appSize haskellIntSize (PLC.TyBuiltin () PLC.TyInteger)
    -- we don't support Integer
    | GHC.getName tc == GHC.integerTyConName = throwPlain $ UnsupportedError "Integer: use Int instead"
    -- this is Void#, see Note [Value restriction]
    | tc == GHC.voidPrimTyCon = liftQuote errorTy
    | otherwise = do
        tc' <- convTyCon tc
        args' <- mapM convType ts
        pure $ PLC.mkIterTyApp () tc' args'

convTyCon :: (Converting m) => GHC.TyCon -> m PLCType
convTyCon tc = do
    prims <- asks ccPrimTypes
    defs <- gets csTypeDefs
    let tcName = GHC.getName tc
    -- could be a Plutus primitive type
    case Map.lookup tcName prims of
        Just ty -> liftQuote ty
        Nothing -> case Map.lookup tcName defs of
            Just (td, _) -> pure $ tydTy td
            Nothing -> do
                -- See Note [Abstract data types]
                k <- convKind (GHC.tyConKind tc)

                dcs <- getDataCons tc
                usedTcs <- getUsedTcs tc
                let deps = fmap GHC.getName usedTcs ++ fmap GHC.getName dcs

                ty <- do
                    -- this is the name that should be used inside the definition of the type, which
                    -- will be fixed over
                    internalName <- convTyNameFresh tcName

                    -- TODO: it's a bit weird for this to have to have a RHS that we will never use
                    let inProgressDef = Def Abstract (PLC.TyVarDecl () internalName k) (PlainType (PLC.TyVar () internalName))
                    modify $ over typeDefs (Map.insert tcName (inProgressDef, deps))
                    mkTyCon tc

                -- this is the name for the final type itself
                finalName <- convTyNameFresh tcName
                (constrs, match) <- do
                    let visibleDef = Def Visible (PLC.TyVarDecl () finalName k) (PlainType ty)
                    modify $ over typeDefs (Map.insert tcName (visibleDef, deps))
                    -- make the constructor bodies with the type visible
                    constrs <- forM dcs $ \dc -> do
                        constr <- mkConstructor dc
                        pure (dc, constr)
                    match <- mkMatch tc
                    pure (constrs, match)

                -- See Note [Booleans, unit and abstraction]
                let finalVisibility = if tc == GHC.boolTyCon || tc == GHC.unitTyCon then Visible else Abstract
                (constrDefs, matchDef) <- do
                    -- make the constructor *types* with the type abstract
                    let abstractDef = Def finalVisibility (PLC.TyVarDecl () finalName k) (PlainType ty)
                    modify $ over typeDefs (Map.insert tcName (abstractDef, deps))

                    constrDefs <- forM constrs $ \(dc, constr) -> do
                        constrName <- convNameFresh (GHC.getName dc)
                        constrTy <- mkConstructorType dc
                        pure $ Def finalVisibility (PLC.VarDecl () constrName constrTy) constr

                    matchName <- safeFreshName $ (GHC.getOccString $ GHC.getName tc) ++ "_match"
                    matchTy <- mkMatchTy tc
                    let matchDef = Def finalVisibility (PLC.VarDecl () matchName matchTy) match
                    pure (constrDefs, matchDef)

                do
                    -- create the final def with the type abstract and the constructors present
                    let def = Def finalVisibility (PLC.TyVarDecl () finalName k) (DataType ty constrDefs matchDef)
                    modify $ over typeDefs (Map.insert tcName (def, deps))
                    case finalVisibility of
                        Abstract -> pure $ PLC.TyVar () finalName
                        Visible  -> pure ty
-- Newtypes

-- | Wrapper for a pair of types with a direction of wrapping or unwrapping.
data NewtypeCoercion = Wrap GHC.Type GHC.Type
                     | Unwrap GHC.Type GHC.Type

-- | View a 'GHC.Coercion' as possibly a newtype coercion.
splitNewtypeCoercion :: GHC.Coercion -> Maybe NewtypeCoercion
splitNewtypeCoercion coerce = case GHC.coercionKind coerce of
    (GHC.Pair lhs@(GHC.splitTyConApp_maybe -> Just (GHC.unwrapNewTyCon_maybe -> Just (_, inner, _), _)) rhs) | GHC.eqType rhs inner -> Just $ Unwrap lhs rhs
    (GHC.Pair lhs rhs@(GHC.splitTyConApp_maybe -> Just (GHC.unwrapNewTyCon_maybe -> Just (_, inner, _), _))) | GHC.eqType lhs inner -> Just $ Wrap lhs rhs
    _ -> Nothing

-- Recursive types

{- Note [Detecting recursive types in GHC]
This seems to be surprisingly difficult, and as far as I can tell there is nothing built in to
do this.

We can handle the self-recursive case easily enough, since we just look for the very name of
the type constructor we're converting.

For mutually recursive types we'll need to do a SCC analysis on the type dependency graph. We
can do this as we go, but we'll want to cache it. At the moment getting the information to
do this out of GHC seems hard.
-}

getUsedTcs :: (Converting m) => GHC.TyCon -> m [GHC.TyCon]
getUsedTcs tc = do
    dcs <- getDataCons tc
    let usedTcs = GHC.unionManyUniqSets $ (\dc -> GHC.unionManyUniqSets $ GHC.tyConsOfType <$> GHC.dataConRepArgTys dc) <$> dcs
    pure $ GHC.nonDetEltsUniqSet usedTcs

isSelfRecursiveTyCon :: (Converting m) => GHC.TyCon -> m Bool
isSelfRecursiveTyCon tc = do
    -- See Note [Detecting recursive types in GHC]
    usedTcs <- getUsedTcs tc
    pure $ tc `elem` usedTcs

-- | Split out a recursive type (constructed by us) into its pattern functor and the name of the variable.
-- This is a bit of a hack, since it relies on us knowing that the structure will be some number of applications
-- surrounding a fix.
splitPatternFunctor :: PLC.Type PLC.TyName () -> Maybe (PLC.Type PLC.TyName(), PLC.TyName ())
splitPatternFunctor ty =
    let
        (ty', tas) = stripTyApps ty
    in do
    (noFix, fixVar) <- case ty' of
        PLC.TyFix _ fixVar inner -> Just (inner, fixVar)
        _                        -> Nothing
    let withApps = PLC.mkIterTyApp () noFix tas
    pure (withApps, fixVar)

stripTyApps :: PLC.Type PLC.TyName () -> (PLC.Type PLC.TyName(), [PLC.Type PLC.TyName ()])
stripTyApps = \case
    PLC.TyApp _ ty1 ty2 -> let (ty', tas) = stripTyApps ty1 in (ty', ty2:tas)
    x -> (x, [])

-- Data

{- Note [Scott encoding of datatypes]
(This describes the conceptual scheme for converting data types - in fact we translate
them as abstract, so see also Note [Abstract data types].)

We translate our datatypes using the Scott encoding. The fundamental idea is that there is one thing
you can do with a datatype value: pattern match on it. A datatype value is therefore represented by
precisely the thing you need to do a pattern match. Namely, a function that takes functions implementing
each arm of the match, and then gives you a result.

For example, 'Just ' and 'Nothing' are encoded as
\arg1 . \justBranch nothingBranch . justBranch arg1
\justBranch nothingBranch . nothingBranch

We also need to think about the types. In general, we need:
- The type of the datatype
- The type of each constructor
- The value of each constructor

Consider a datatype T with type parameters t_i, constructors c_j with arguments a_c_j_k of types
t_c_j_k. Then:

The polymorphic type of the datatype is:
\t_1 :: (type) .. t_i :: (type) .
  forall r :: (type) .
    (t_1 -> .. -> t_c_1_k -> r) -> .. -> (t_1 -> .. -> t_c_j_k -> r) ->
      r

The polymorphic type of the constructor c_j is:
\t_1 :: (type) .. t_i :: (type) .
  t1 -> .. -> t_c_j_k ->
    T t_1 .. t_i
We never actually use this, since we don't put these as arguments to lambdas.

The value of the constructor c_j applied to arguments t_i is:
\a_1 : t1 .. a_c_j_k : t_c_j_k .
  abs r :: (type) .
    \c_1 : (t_1 -> .. -> t_c_1_k -> r) .. c_j : (t_1 -> .. -> t_c_j_k -> r) .
      c_j a_1 .. a_c_j_k

Pattern matching is very simple:
- We take each alternative, turn it into a function of its bound variables.
- We instantiate the scrutinee (which is polymorphic in the result type) at the
type of the overall case expression.
- We apply the instantiated scrutinee to the functions for each alternative.
-}

{- Note [Abstract data types]
While the Scott encoding makes it easy to simply convert all types inline, it
is convenient for a number of reasons to instead abstract out data types. Namely:
- The resulting code is much more readable, since we have named types instead
of (potentially big) inlined types.
- We generate less code because we're not repeating the definition at every use site.

The basic idea is to "let-bind" types using type abstractions, and values using
lambda abstractions. There are a few considerations that make this tricky, however:
1. When types are inlined, the Scott encoding allows us to construct values by
constructing the matching function inline. When they are abstract, we need to provide
(suitably polymorphic) constructors abstractly.
2. When types are inlined, the Scott encoding allows us to match against a type by
simply using it as a function. When they are abstract, we need to provide a
(suitably polymorphic) matching function abstractly.
3. The definition of a type must be abstract in the binding for the constructors and destructors
(so they can be used alongside the abstract type), but it must *not* be abstract in the
*body* of the constructors or destructors, because they depend on knowing the real structure
of the type.

Consequently, for a single type we end up with something like the following:

(abs ty :: (type) .
  \c1 : forall t_1 :: (type) .. t_i :: (type) . t_1 -> .. -> t_c_1_k -> ty .. c_j : t_1 -> t_c_j_k -> ty
    \match : forall t_1 :: (type) .. t_i :: (type) . forall r :: (type) b. (t_1 -> .. -> t_c_1_k -> r) -> .. -> (t_1 -> t_c_j_k -> r) -> r
      <user term>
)
<defn of t>
<defn of c1>
..
<defn of c_n>
<defn of match>
(see Note [Scott-encoding of datatypes] for how the actual definitions are constructed)

We also have to convert data constructors and case expressions into suitably instantiated
calls to the constructors/destructors instead of converting them directly as described in
Note [Scott encoding of data types]

The requirements imposed by 3. render translation somewhat tricky. We want our translation to be
ambivalent about where we are in the process of creating a type, so we use a richer type
of definitions to handle things gracefully.

(Why do we want to be ambivalent? We want to use e.g. the same code to compile both
`data List a = Nil | Cons a (List a)` and `data ListWrapper a = ListWrapper (List a)`, even though
`List` has to be two different things in the two cases (in the first it will be a reference to
the fixpoint variable, in the second a reference to the abstract type.).)

Definitions consist roughtly of a variable and a value. They can be visible, or abstract. Visible
definitions are inlined, abstract definitions are referenced via their variable. At the end
we bind all abstract definitions as described above. (We also track dependencies between them
so we can do the bindings in the right order.)

When constructing a datatype we therefore carefully construct its pieces in several stages:
- First, we define the datatype by an internal name. This is the name that will be used
  for self-references inside the datatype, and will be used as the fixpoint variable if
  it is recursive.
    - With this in place, we convert the type itself.
- Then we create the final name, and bind the datatype definition to that *visibly*.
    - With this in place, we convert the constructor and destructor *definitions*.
- Then we bind the datatype definition to the final name again, but with its final visibility
  (usually *abstract*).
    - With this in place we convert the constructor and destructor *types*.
- Finally, we bind the datatype definition to the final name again, but with its final visibility
  and with all the constructors and destructors attached.
-}

{- Note [Booleans, unit and abstraction]
While we convert most datatypes as abstract (see Note [Abstract data types]), we do *not*
do so for Booleans and Unit.

This is because the Booleans and Unit appear in our builtins. Booleans are in the spec, and Unit
appears because we need to expose error as `\_ -> error`. But these types will be non-abstract
(i.e. will actually be the Scott-encoded values), and so in order for user code to interoperate
with that we would have to either:
1. Wrap all builtins that use such types to convert them into the abstract types.
2. Leave the types as visible throughout.

At the moment we take option 2 since Bool and Unit are fairly small types, but possibly we should
consider option 1 later.
-}

{- Note [Case expressions and laziness]
PLC is strict, but users *do* expect that, e.g. they can write an if expression and have it be
lazy. This only *matters* because we have 'error', so it's important that 'if false error else ...'
does not evaluate to 'error'!

More generally, we can compile case expressions (of which an if expression is one) lazily, i.e. we add
a unit argument and apply it at the end.

However, we apply an important optimization: we only need to do this if it is not the case that
all the case expressions are values. In the common case they *will* be, so this gives us
significantly better codegen a lot of the time.

The check we do is:
- Alternatives with arguments will be turned into lambdas by us, so will be values.
- Otherwise, we convert the expression (we can do this easily since it doesn't need any variables in scope),
  and check whether it is a value.

This is somewhat wasteful, since we may convert the expression twice, but it's difficult to avoid, and
it's hard to tell if a GHC core expression will be a PLC value or not. Easiest to just try it.
-}

{- Note [Ordering of constructors]
It is very important that we convert types and constructors consistently, especially between
lifting at runtime and compilation via the plugin. The main place we can get bitten is ordering.

GHC is under no obligation to give us any particular ordering of constructors, so we impose
an alphabetical one (with a few exceptions, see [Ensuring compatibility with spec and stdlib types]).

The other place where ordering matters is arguments to constructors, but here there is a
clear natural ordering which we will assume GHC respects.
-}

{- Note [Ensuring compatibility with spec and stdlib types]
Haskell's Bool has its constructors ordered with False before True, which results in the
normal case expression having the oppposite sense to the one in the spec, where
the true branch comes first (which is more logical).

Our options are:
- Reverse the branches in the spec.
    - This is ugly, the plugin details shouldn't influence the spec.
- Rewrite the primitive functions that produce booleans to produce spec booleans.
    - This is pretty bad codegen.
- Special case Bool to swap the order of the cases.

We take the least bad option, option 3.

The same problem arises for List. It's not in the spec, but the stdlib order (and the natural one)
is nil first and then cons, but ":" is less than "[]", so we end up with the wrong order. Again,
we just special case this.
-}

-- See Note [Ordering of constructors]
sortConstructors :: GHC.TyCon -> [GHC.DataCon] -> [GHC.DataCon]
sortConstructors tc cs =
    -- note we compare on the OccName *not* the Name, as the latter compares on uniques, not the string name
    let sorted = sortBy (\dc1 dc2 -> compare (GHC.getOccName dc1) (GHC.getOccName dc2)) cs
    in if tc == GHC.boolTyCon || tc == GHC.listTyCon then reverse sorted else sorted

getDataCons :: (Converting m) =>  GHC.TyCon -> m [GHC.DataCon]
getDataCons tc' = sortConstructors tc' <$> extractDcs tc'
    where
        extractDcs tc
          | GHC.isAlgTyCon tc || GHC.isTupleTyCon tc = case GHC.algTyConRhs tc of
              GHC.AbstractTyCon                -> throwSd UnsupportedError $ "Abstract type:" GHC.<+> GHC.ppr tc
              GHC.DataTyCon{GHC.data_cons=dcs} -> pure dcs
              GHC.TupleTyCon{GHC.data_con=dc}  -> pure [dc]
              GHC.SumTyCon{GHC.data_cons=dcs}  -> pure dcs
              GHC.NewTyCon{GHC.data_con=dc}    -> pure [dc]
          | otherwise = throwSd UnsupportedError $ "Type constructor:" GHC.<+> GHC.ppr tc

-- See Note [Scott encoding of datatypes]
-- | Make the type corresponding to a given 'TyCon'.
mkTyCon :: forall m. Converting m => GHC.TyCon -> m PLCType
mkTyCon tc = do
    -- abstract out the type variables
    -- \t_1 .. t_i . scottTy
    abstracted <- mkIterTyLamScoped (GHC.tyConTyVars tc) $ mkScottTy tc

    -- add the fixpoint, if there is one
    tcDefs <- gets csTypeDefs
    isSelfRecursive <- isSelfRecursiveTyCon tc
    if isSelfRecursive
    then case Map.lookup (GHC.getName tc) tcDefs of
        -- TODO: this is inelegant
        -- we're recursive, therefore the variable stored as our definition is the fixpoint variable
        Just (Def{dVis=Abstract,dVar=(PLC.TyVarDecl _ tyname _)}, _) -> pure $ PLC.TyFix () tyname abstracted
        _                                             -> throwPlain $ ConversionError "Could not find var to fix over"
    else pure abstracted

-- See Note [Scott encoding of datatypes]
-- | Make the pure Scott-encoded type of the given 'TyCon'.
mkScottTy :: Converting m => GHC.TyCon -> m PLCType
mkScottTy tc = do
    dcs <- getDataCons tc
    resultType <- safeFreshTyName $ (GHC.getOccString $ GHC.getName tc) ++ "_matchOut"
    -- we can only match into kind Type
    let resultKind = PLC.Type ()
    cases <- mapM (mkCaseType (PLC.TyVar () resultType)) dcs
    -- case_1 -> ... -> case_n -> resultType
    let funcs = PLC.mkIterTyFun () cases (PLC.TyVar () resultType)
    -- forall resultType . funcs
    pure $ PLC.TyForall () resultType resultKind funcs

-- | Makes the type of a matcher for the given 'DataCon' producing the given type.
mkCaseType :: Converting m => PLCType -> GHC.DataCon -> m PLCType
mkCaseType resultType dc = withContextM (sdToTxt $ "Converting data constructor:" GHC.<+> GHC.ppr dc) $
    if not (GHC.isVanillaDataCon dc) then throwSd UnsupportedError $ "Non-vanilla data constructor:" GHC.<+> GHC.ppr dc
    else do
        let argTys = GHC.dataConRepArgTys dc
        args <- mapM convType argTys
        -- t_1 -> ... -> t_m -> resultType
        pure $ PLC.mkIterTyFun () args resultType

-- | Makes the type of the constructor corresponding to the given 'DataCon'.
mkConstructorType :: Converting m => GHC.DataCon -> m PLCType
mkConstructorType dc =
    let argTys = GHC.dataConRepArgTys dc
        tc = GHC.dataConTyCon dc
        tcTyVars = GHC.tyConTyVars tc
    in
        -- See Note [Scott encoding of datatypes]
        withContextM (sdToTxt $ "Converting data constructor type:" GHC.<+> GHC.ppr dc) $
            -- forall . t_1 .. t_i
            mkIterTyForallScoped tcTyVars $ do
                args <- mapM convType argTys
                resultType <- convType (GHC.dataConOrigResTy dc)
                -- t_c_i_1 -> ... -> t_c_i_j -> resultType
                pure $ PLC.mkIterTyFun () args resultType

-- | Makes the constructor for the given 'DataCon'.
mkConstructor :: Converting m => GHC.DataCon -> m PLCTerm
mkConstructor dc =
    let
        tc = GHC.dataConTyCon dc
        tcKind = GHC.tyConKind tc
        tcTyVars = GHC.tyConTyVars tc
        tcName = GHC.getOccString $ GHC.getName tc
        dcName = GHC.getOccString $ GHC.getName dc
    in
        -- See Note [Scott encoding of datatypes]
        withContextM (sdToTxt $ "Converting data constructor:" GHC.<+> GHC.ppr dc) $
            -- no need for a body value check here, we know it's a lambda (see Note [Value restriction])
            -- /\ tv_1 .. tv_n . body
            mkIterTyAbsScoped tcTyVars $ do
                resultType <- safeFreshTyName $ tcName ++ "_matchOut"
                dcs <- getDataCons tc
                index <- case elemIndex dc dcs of
                    Just i  -> pure i
                    Nothing -> throwPlain $ ConversionError "Data constructor not in the type constructor's list of constructors!"

                -- case arguments and their types
                caseTypes <- mapM (mkCaseType (PLC.TyVar () resultType)) dcs
                caseArgNames <- mapM (convNameFresh . GHC.getName) dcs

                -- constructor args and their types
                argTypes <- mapM convType $ GHC.dataConRepArgTys dc
                argNames <- forM [0..(length argTypes -1)] (\i -> safeFreshName $ dcName ++ "_arg" ++ show i)

                -- we need the pattern functor if there is one so we can wrap
                isSelfRecursive <- isSelfRecursiveTyCon tc
                maybePf <- if isSelfRecursive
                          then do
                              tc' <- convTyCon tc
                              case splitPatternFunctor tc' of
                                    Just (pf, n) -> do
                                        k <- convKind tcKind
                                        pure $ Just (PLC.Def (PLC.TyVarDecl () n k) pf)
                                    Nothing -> throwPlain $ ConversionError "Could not compute pattern functor for recursive type"
                          else pure Nothing

                let scottBody = mkScottConstructorBody
                      resultType
                      (zipWith (PLC.VarDecl ()) caseArgNames caseTypes)
                      (zipWith (PLC.VarDecl ()) argNames argTypes)
                      index
                      maybePf
                pure scottBody

mkScottConstructorBody
    :: PLC.TyName () -- ^ Name of the result type
    -> [PLC.VarDecl PLC.TyName PLC.Name ()] -- ^ Names of the case arguments and their types
    -> [PLC.VarDecl PLC.TyName PLC.Name ()] -- ^ Names of the constructor arguments and their types
    -> Int -- ^ Index of this constructor in the list of constructors
    -> Maybe (PLC.Def (PLC.TyVarDecl PLC.TyName ()) (PLC.Type PLC.TyName ())) -- ^ A pattern functor and bound type name if this is constructing a recursive type
    -> PLCTerm
mkScottConstructorBody resultTypeName caseNamesAndTypes argNamesAndTypes index maybePf =
    let
        -- data types are always in kind Type
        resultKind = PLC.Type ()
        thisConstructor = PLC.mkVar () $ caseNamesAndTypes !! index
        -- See Note [Iterated abstraction and application]
        -- c_i a_1 .. a_m
        applied = foldl' (\acc a -> PLC.Apply () acc a) thisConstructor (fmap (PLC.mkVar ()) argNamesAndTypes)
        -- \c_1 .. c_n . applied
        cfuncs = PLC.mkIterLamAbs () caseNamesAndTypes applied
        -- no need for a body value check here, we know it's a lambda (see Note [Value restriction])
        -- forall r . cfuncs
        resAbstracted = PLC.TyAbs () resultTypeName resultKind cfuncs
        -- wrap resAbstracted
        fixed = case maybePf of
            Just (PLC.Def (PLC.TyVarDecl _ n _) pf) -> PLC.Wrap () n pf resAbstracted
            Nothing                                 -> resAbstracted
        -- \a_1 .. a_m . fixed
        afuncs = PLC.mkIterLamAbs () argNamesAndTypes fixed
    in afuncs

-- | Get the constructors of the given 'TyCon' as PLC terms.
getConstructors :: Converting m => GHC.TyCon -> m [PLCTerm]
getConstructors tc = do
    -- make sure the constructors have been created
    _ <- convTyCon tc
    defs <- gets csTypeDefs
    case Map.lookup (GHC.getName tc) defs of
        Just (tydConstrs -> Just constrs, _) -> pure $ tdTerm <$> constrs
        _                                    -> throwPlain $ ConversionError "Constructors have not been converted"

-- | Get the constructors of the given 'Type' (which must be equal to a type constructor application) as PLC terms instantiated for
-- the type constructor argument types.
getConstructorsInstantiated :: Converting m => GHC.Type -> m [PLCTerm]
getConstructorsInstantiated = \case
    (GHC.splitTyConApp_maybe -> Just (tc, args)) -> do
        constrs <- getConstructors tc

        forM constrs $ \c -> do
            args' <- mapM convType args
            pure $ PLC.mkIterInst () c args'
    -- must be a TC app
    _ -> throwPlain $ ConversionError "Type was not a type constructor application"

-- | Make the type of the matcher for a given 'TyCon'.
mkMatchTy :: Converting m => GHC.TyCon -> m PLCType
mkMatchTy tc =
    let
        tyVars = GHC.tyConTyVars tc
    in
        -- forall t_1 .. t_n
        mkIterTyForallScoped tyVars $ do
            -- we essentially "unveil" the abstract type, so this
            -- is a function from the (instantiated, unwrapped) abstract type
            -- to the "real" Scott-encoded type that we can use as
            -- a matcher
            tc' <- convTyCon tc
            -- t t_1 .. t_n
            args <- mapM (convType . GHC.mkTyVarTy) tyVars
            let applied = PLC.mkIterTyApp () tc' args

            scottTy <- mkScottTy tc

            pure $ PLC.TyFun () applied scottTy

-- | Make the matcher for a given 'TyCon'.
mkMatch :: Converting m => GHC.TyCon -> m PLCTerm
mkMatch tc =
    let
        tyVars = GHC.tyConTyVars tc
    in
        -- /\ t_1 .. t_n
        mkIterTyAbsScoped tyVars $ do

            tc' <- convTyCon tc
            -- t t_1 .. t_n
            args <- mapM (convType . GHC.mkTyVarTy) tyVars
            let applied = PLC.mkIterTyApp () tc' args

            -- this is basically the identity! but we do need to unwrap it
            x <- safeFreshName "x"
            isSelfRecursive <- isSelfRecursiveTyCon tc
            let body = PLC.Var () x
            let unwrapped = if isSelfRecursive then PLC.Unwrap () body else body

            pure $ PLC.LamAbs () x applied unwrapped

-- | Get the matcher of the given 'TyCon' as a PLC term
getMatch :: Converting m => GHC.TyCon -> m PLCTerm
getMatch tc = do
    -- ensure the tycon has been converted, which will create the matcher
    _ <- convTyCon tc
    defs <- gets csTypeDefs
    case Map.lookup (GHC.getName tc) defs of
        Just (tydMatch -> Just match, _) -> pure $ tdTerm match
        _                                -> throwPlain $ ConversionError "Match has not been converted"

-- | Get the matcher of the given 'Type' (which must be equal to a type constructor application) as a PLC term instantiated for
-- the type constructor argument types.
getMatchInstantiated :: Converting m => GHC.Type -> m PLCTerm
getMatchInstantiated = \case
    (GHC.splitTyConApp_maybe -> Just (tc, args)) -> do
        match <- getMatch tc

        args' <- mapM convType args
        pure $ PLC.mkIterInst () match args'
    -- must be a TC app
    _ -> throwPlain $ ConversionError "Type was not a type constructor application"

-- | Make the alternative for a given 'CoreAlt'.
convAlt
    :: Converting m
    => Bool -- ^ Whether we must delay the alternative.
    -> GHC.DataCon -- ^ The 'DataCon' for the current alternative.
    -> GHC.CoreAlt -- ^ The 'CoreAlt' representing the branch itself.
    -> m PLCTerm
convAlt mustDelay dc (alt, vars, body) = case alt of
    GHC.LitAlt _  -> throwPlain $ UnsupportedError "Literal case"
    GHC.DEFAULT   -> do
        body' <- convExpr body >>= maybeDelay mustDelay
        -- need to consume the args
        argTypes <- mapM convType $ GHC.dataConRepArgTys dc
        argNames <- forM [0..(length argTypes -1)] (\i -> safeFreshName $ "default_arg" ++ show i)
        pure $ PLC.mkIterLamAbs () (zipWith (PLC.VarDecl ()) argNames argTypes) body'
    -- We just package it up as a lambda bringing all the
    -- vars into scope whose body is the body of the case alternative.
    -- See Note [Iterated abstraction and application]
    -- See Note [Case expressions and laziness]
    GHC.DataAlt _ -> mkIterLamAbsScoped vars (convExpr body >>= maybeDelay mustDelay)
