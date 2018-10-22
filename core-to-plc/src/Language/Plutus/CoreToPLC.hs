{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}

module Language.Plutus.CoreToPLC where

import           Language.Plutus.CoreToPLC.Builtins
import           Language.Plutus.CoreToPLC.Definitions
import           Language.Plutus.CoreToPLC.Error
import           Language.Plutus.CoreToPLC.Laziness
import           Language.Plutus.CoreToPLC.PLCTypes
import qualified Language.Plutus.CoreToPLC.Primitives     as Prims
import           Language.Plutus.CoreToPLC.Types

import qualified CoreUtils                                as GHC
import qualified GhcPlugins                               as GHC
import qualified Kind                                     as GHC
import qualified MkId                                     as GHC
import qualified Pair                                     as GHC
import qualified PrelNames                                as GHC
import qualified PrimOp                                   as GHC
import qualified TysPrim                                  as GHC

import qualified Language.PlutusCore                      as PLC
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Function as Function

import qualified Language.Haskell.TH.Syntax               as TH

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import qualified Data.ByteString.Lazy                     as BSL
import           Data.Char
import           Data.Foldable
import qualified Data.List.NonEmpty                       as NE
import qualified Data.Map                                 as Map
import qualified Data.Text                                as T
import qualified Data.Text.Encoding                       as TE
import           Lens.Micro

import           Data.List                                (elemIndex, reverse, sortBy)

{- Note [System FC and System FW]
Haskell uses system FC, which includes type equalities and coercions.

PLC does *not* have coercions in particular. However, PLC also does not have a nominal
type system - everything is constructed via operators on base types, so we have no
need for coercions to convert between newtypes and datatypes.

So we mostly ignore coercions. The one place that I know of where the mismatch hurts
us is that GHC uses the `Any` type (coercible to and from anything) for unconstrained
function variables, e.g. in polymorphic lambdas. This is annoying for us, since we
really want the version with explicit type abstraction. I don't currently have a fix
for this.
-}

{- Note [Iterated abstraction and application]
PLC doesn't expose iterated abstraction and application.

We typically build these with a fold.
- Iterated application uses a *left* fold, since we want to apply the first variable
first.
- Iterated abstraction uses a *right* fold, since we want to bind the first
variable *last* (so it is on the outside, so will be first when applying).
-}

strToBs :: String -> BSL.ByteString
strToBs = BSL.fromStrict . TE.encodeUtf8 . T.pack

bsToStr :: BSL.ByteString -> String
bsToStr = T.unpack . TE.decodeUtf8 . BSL.toStrict

sdToTxt :: (MonadReader ConvertingContext m) => GHC.SDoc -> m T.Text
sdToTxt sd = do
  ConvertingContext { ccFlags=flags } <- ask
  pure $ T.pack $ GHC.showSDoc flags sd

throwSd :: (MonadError ConvError m, MonadReader ConvertingContext m) => (T.Text -> Error ()) -> GHC.SDoc -> m a
throwSd constr = (throwPlain . constr) <=< sdToTxt

-- Names and scopes

lookupName :: Scope -> GHC.Name -> Maybe (PLC.Name ())
lookupName (Scope ns _) n = Map.lookup n ns

{- Note [PLC names]
We convert names from Haskell names quite frequently here, but PLC admits a much
smaller set of valid identifiers. We compromise by mangling the identifier, but
in the long run it would be nice to have a more principled encoding so we can
support unicode identifiers as well.
-}

safeFreshName :: MonadQuote m => String -> m (PLC.Name ())
safeFreshName s
    -- some special cases
    | s == ":" = safeFreshName "cons"
    | s == "[]" = safeFreshName "list"
    | otherwise =
          let
              -- See Note [PLC names]
              -- first strip out disallowed characters
              stripped = filter (\c -> isLetter c || isDigit c || c == '_' || c == '`') s
              -- now fix up some other bits
              fixed = case stripped of
                -- empty name, just put something to mark that
                []      -> "bad_name"
                -- can't start with these
                ('`':_) -> "p" ++ stripped
                ('_':_) -> "p" ++ stripped
                n       -> n
          in liftQuote $ freshName () $ strToBs fixed

convNameFresh :: MonadQuote m => GHC.Name -> m (PLC.Name ())
convNameFresh n = safeFreshName $ GHC.getOccString n

convVarFresh :: Converting m => GHC.Var -> m (PLCType, PLC.Name ())
convVarFresh v = do
    t' <- convType $ GHC.varType v
    n' <- convNameFresh $ GHC.getName v
    pure (t', n')

lookupTyName :: Scope -> GHC.Name -> Maybe (PLC.TyName ())
lookupTyName (Scope _ tyns) n = Map.lookup n tyns

safeFreshTyName :: MonadQuote m => String -> m (PLC.TyName ())
safeFreshTyName s = PLC.TyName <$> safeFreshName s

convTyNameFresh :: MonadQuote m => GHC.Name -> m (PLC.TyName ())
convTyNameFresh n = PLC.TyName <$> convNameFresh n

convTyVarFresh :: Converting m => GHC.TyVar -> m (PLC.TyName (), PLC.Kind ())
convTyVarFresh v = do
    k' <- convKind $ GHC.tyVarKind v
    t' <- convTyNameFresh $ GHC.getName v
    pure (t', k')

pushName :: GHC.Name -> PLC.Name () -> ScopeStack -> ScopeStack
pushName ghcName n stack = let Scope ns tyns = NE.head stack in Scope (Map.insert ghcName n ns) tyns NE.<| stack

pushTyName :: GHC.Name -> PLC.TyName () -> ScopeStack -> ScopeStack
pushTyName ghcName n stack = let Scope ns tyns = NE.head stack in Scope ns (Map.insert ghcName n tyns) NE.<| stack

-- Types and kinds

convKind :: Converting m => GHC.Kind -> m (PLC.Kind ())
convKind k = withContextM (sdToTxt $ "Converting kind:" GHC.<+> GHC.ppr k) $ case k of
    -- this is a bit weird because GHC uses 'Type' to represent kinds, so '* -> *' is a 'TyFun'
    (GHC.isStarKind -> True)              -> pure $ PLC.Type ()
    (GHC.splitFunTy_maybe -> Just (i, o)) -> PLC.KindArrow () <$> convKind i <*> convKind o
    _                                     -> throwSd UnsupportedError $ "Kind:" GHC.<+> GHC.ppr k


convType :: Converting m => GHC.Type -> m PLCType
convType t = withContextM (sdToTxt $ "Converting type:" GHC.<+> GHC.ppr t) $ do
    -- See Note [Scopes]
    ConvertingContext {ccScopes=stack} <- ask
    let top = NE.head stack
    case t of
        -- in scope type name
        (GHC.getTyVar_maybe -> Just (lookupTyName top . GHC.getName -> Just name)) -> pure $ PLC.TyVar () name
        (GHC.getTyVar_maybe -> Just v) -> throwSd FreeVariableError $ "Type variable:" GHC.<+> GHC.ppr v
        (GHC.splitFunTy_maybe -> Just (i, o)) -> PLC.TyFun () <$> convType i <*> convType o
        (GHC.splitTyConApp_maybe -> Just (tc, ts)) -> convTyConApp tc ts
        (GHC.splitForAllTy_maybe -> Just (tv, tpe)) -> mkTyForall tv (convType tpe)
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
        pure $ mkIterTyApp tc' args'

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
                    let inProgressDef = Def Abstract (internalName, k) (PlainType (PLC.TyVar () internalName))
                    modify $ over typeDefs (Map.insert tcName (inProgressDef, deps))
                    convDataCons tc dcs

                -- this is the name for the final type itself
                finalName <- convTyNameFresh tcName
                (constrs, match) <- do
                    let visibleDef = Def Visible (finalName, k) (PlainType ty)
                    modify $ over typeDefs (Map.insert tcName (visibleDef, deps))
                    -- make the constructor bodies with the type visible
                    constrs <- forM dcs $ \dc -> do
                        constr <- convConstructor dc
                        pure (dc, constr)
                    match <- mkMatch tc
                    pure (constrs, match)

                -- See Note [Booleans and abstraction]
                let finalVisibility = if tc == GHC.boolTyCon then Visible else Abstract
                (constrDefs, matchDef) <- do
                    -- make the constructor *types* with the type abstract
                    let abstractDef = Def finalVisibility (finalName, k) (PlainType ty)
                    modify $ over typeDefs (Map.insert tcName (abstractDef, deps))

                    constrDefs <- forM constrs $ \(dc, constr) -> do
                        constrName <- convNameFresh (GHC.getName dc)
                        constrTy <- dataConType dc
                        pure $ Def finalVisibility (constrName, constrTy) constr

                    matchName <- safeFreshName $ (GHC.getOccString $ GHC.getName tc) ++ "_match"
                    matchTy <- mkMatchTy tc dcs
                    let matchDef = Def finalVisibility (matchName, matchTy) match
                    pure (constrDefs, matchDef)

                do
                    -- create the final def with the type abstract and the constructors present
                    let def = Def finalVisibility (finalName, k) (DataType ty constrDefs matchDef)
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

isSelfRecursiveType :: (Converting m) => GHC.Type -> m Bool
isSelfRecursiveType t = case t of
    -- the only way it can be *self* recursive is if it's type constructor
    (GHC.splitTyConApp_maybe -> Just (tc, _)) -> isSelfRecursiveTyCon tc
    _                                         -> pure False

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
    let withApps = mkIterTyApp noFix tas
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

{- Note [Booleans and abstraction]
While we convert most datatypes as abstract (see Note [Abstract data types]), we do *not*
do so for Booleans. This is because the booleans produced by builtins will be non-abstract
(i.e. will actually be the Scott-encoded values), and so in order for user code to interoperate
with that we would have to either:
1. Wrap all builtins that return booleans to convert them into abstract booleans.
2. Leave booleans as visible throughout.

At the moment we take option 2 since Bool is a fairly small type, but possibly we should
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

-- This is the creation of the Scott-encoded datatype type.
-- See Note [Scott encoding of datatypes]
convDataCons :: forall m. Converting m => GHC.TyCon -> [GHC.DataCon] -> m PLCType
convDataCons tc dcs = do
    abstracted <- flip (foldr (\tv acc -> mkTyLam tv acc)) (GHC.tyConTyVars tc) $ mkScottTy tc dcs

    tcDefs <- gets csTypeDefs
    isSelfRecursive <- isSelfRecursiveTyCon tc
    if isSelfRecursive
    then case Map.lookup (GHC.getName tc) tcDefs of
        Just (Def{dVis=Abstract,dVar=(tyname, _)}, _) -> pure $ PLC.TyFix () tyname abstracted
        _                                             -> throwPlain $ ConversionError "Could not find var to fix over"
    else pure abstracted

mkScottTy :: Converting m => GHC.TyCon -> [GHC.DataCon] -> m PLCType
mkScottTy tc dcs = do
    resultType <- safeFreshTyName $ (GHC.getOccString $ GHC.getName tc) ++ "_matchOut"
    cases <- mapM (dataConCaseType (PLC.TyVar () resultType)) dcs
    pure $ mkScottTyBody resultType cases

mkScottTyBody :: PLC.TyName () -> [PLCType] -> PLCType
mkScottTyBody resultTypeName cases =
    let
        -- we can only match into kind Type
        resultKind = PLC.Type ()
        -- case_1 -> ... -> case_n -> resultType
        funcs = mkIterTyFun cases (PLC.TyVar () resultTypeName)
        -- forall resultType . funcs
        resultAbstracted = PLC.TyForall () resultTypeName resultKind funcs
    in resultAbstracted

dataConCaseType :: Converting m => PLCType -> GHC.DataCon -> m PLCType
dataConCaseType resultType dc = withContextM (sdToTxt $ "Converting data constructor:" GHC.<+> GHC.ppr dc) $
    if not (GHC.isVanillaDataCon dc) then throwSd UnsupportedError $ "Non-vanilla data constructor:" GHC.<+> GHC.ppr dc
    else do
        let argTys = GHC.dataConRepArgTys dc
        args <- mapM convType argTys
        -- t_1 -> ... -> t_m -> resultType
        pure $ mkIterTyFun args resultType

dataConType :: Converting m => GHC.DataCon -> m PLCType
dataConType dc =
    let argTys = GHC.dataConRepArgTys dc
        tc = GHC.dataConTyCon dc
        tcTyVars = GHC.tyConTyVars tc
    in
        withContextM (sdToTxt $ "Converting data constructor type:" GHC.<+> GHC.ppr dc) $
            flip (foldr (\tv acc -> mkTyForall tv acc)) tcTyVars $ do
                args <- mapM convType argTys
                resultType <- convType (GHC.dataConOrigResTy dc)
                -- t_1 -> ... -> t_m -> resultType
                pure $ mkIterTyFun args resultType

-- This is the creation of the Scott-encoded constructor value.
convConstructor :: Converting m => GHC.DataCon -> m PLCTerm
convConstructor dc =
    let
        tc = GHC.dataConTyCon dc
        tcTyVars = GHC.tyConTyVars tc
        tcName = GHC.getOccString $ GHC.getName tc
        dcName = GHC.getOccString $ GHC.getName dc
    in
        withContextM (sdToTxt $ "Converting data constructor:" GHC.<+> GHC.ppr dc) $
            -- no need for a body value check here, we know it's a lambda (see Note [Value restriction])
            -- /\ tv_1 .. tv_n . body
            flip (foldr (\tv acc -> mkTyAbs tv acc)) tcTyVars $ do
                -- See Note [Scott encoding of datatypes]
                resultType <- safeFreshTyName $ tcName ++ "_matchOut"
                dcs <- getDataCons tc
                index <- case elemIndex dc dcs of
                    Just i  -> pure i
                    Nothing -> throwPlain $ ConversionError "Data constructor not in the type constructor's list of constructors!"
                caseTypes <- mapM (dataConCaseType (PLC.TyVar () resultType)) dcs
                caseArgNames <- mapM (convNameFresh . GHC.getName) dcs
                argTypes <- mapM convType $ GHC.dataConRepArgTys dc
                argNames <- forM [0..(length argTypes -1)] (\i -> safeFreshName $ dcName ++ "_arg" ++ show i)

                isSelfRecursive <- isSelfRecursiveTyCon tc
                maybePf <- if isSelfRecursive
                          then do
                              tc' <- convTyCon tc
                              case splitPatternFunctor tc' of
                                    Just (pf, n) -> pure $ Just (pf, n)
                                    Nothing -> throwPlain $ ConversionError "Could not compute pattern functor for recursive type"
                          else pure Nothing

                let scottBody = mkScottConstructorBody resultType (zip caseArgNames caseTypes) (zip argNames argTypes) index maybePf
                pure scottBody

mkScottConstructorBody
    :: PLC.TyName () -- ^ Name of the result type
    -> [(PLC.Name (), PLCType)] -- ^ Names of the case arguments and their types
    -> [(PLC.Name (), PLCType)] -- ^ Names of the constructor arguments and their types
    -> Int -- ^ Index of this constructor in the list of constructors
    -> Maybe (PLCType, PLC.TyName ()) -- ^ A pattern functor and bound type name if this is constructing a recursive type
    -> PLCTerm
mkScottConstructorBody resultTypeName caseNamesAndTypes argNamesAndTypes index maybePf =
    let
        -- data types are always in kind Type
        resultKind = PLC.Type ()
        thisConstructor = fst $ caseNamesAndTypes !! index
        -- See Note [Iterated abstraction and application]
        -- c_i a_1 .. a_m
        applied = foldl' (\acc a -> PLC.Apply () acc (PLC.Var () a)) (PLC.Var () thisConstructor) (fmap fst argNamesAndTypes)
        -- \c_1 .. c_n . applied
        cfuncs = mkIterLamAbs caseNamesAndTypes applied
        -- no need for a body value check here, we know it's a lambda (see Note [Value restriction])
        -- forall r . cfuncs
        resAbstracted = PLC.TyAbs () resultTypeName resultKind cfuncs
        -- wrap resAbstracted
        fixed = case maybePf of
            Just (pf, n) -> PLC.Wrap () n pf resAbstracted
            Nothing      -> resAbstracted
        -- \a_1 .. a_m . fixed
        afuncs = mkIterLamAbs argNamesAndTypes fixed
    in afuncs

getConstructors :: Converting m => GHC.TyCon -> m [PLCTerm]
getConstructors tc = do
    -- make sure the constructors have been created
    _ <- convTyCon tc
    defs <- gets csTypeDefs
    case Map.lookup (GHC.getName tc) defs of
        Just (tydConstrs -> Just constrs, _) -> pure $ tdTerm <$> constrs
        _                                    -> throwPlain $ ConversionError "Constructors have not been converted"

getConstructorsInstantiated :: Converting m => GHC.Type -> m [PLCTerm]
getConstructorsInstantiated = \case
    (GHC.splitTyConApp_maybe -> Just (tc, args)) -> do
        constrs <- getConstructors tc

        forM constrs $ \c -> do
            args' <- mapM convType args
            pure $ mkIterInst c args'
    -- must be a TC app
    _ -> throwPlain $ ConversionError "Type was not a type constructor application"

mkMatchTy :: Converting m => GHC.TyCon -> [GHC.DataCon] -> m PLCType
mkMatchTy tc dcs =
    let
        tyVars = GHC.tyConTyVars tc
    in
        flip (foldr (\tv acc -> mkTyForall tv acc)) tyVars $ do
            tc' <- convTyCon tc
            args <- mapM (convType . GHC.mkTyVarTy) tyVars
            let applied = mkIterTyApp tc' args

            scottTy <- mkScottTy tc dcs

            pure $ PLC.TyFun () applied scottTy

mkMatch :: Converting m => GHC.TyCon -> m PLCTerm
mkMatch tc =
    let
        tyVars = GHC.tyConTyVars tc
    in
        flip (foldr (\tv acc -> mkTyAbs tv acc)) tyVars $ do
            tc' <- convTyCon tc
            args <- mapM (convType . GHC.mkTyVarTy) tyVars
            let applied = mkIterTyApp tc' args

            x <- safeFreshName "x"
            isSelfRecursive <- isSelfRecursiveTyCon tc
            let body = PLC.Var () x
            let unwrapped = if isSelfRecursive then PLC.Unwrap () body else body

            pure $ PLC.LamAbs () x applied unwrapped

getMatch :: Converting m => GHC.TyCon -> m PLCTerm
getMatch tc = do
    -- ensure the tycon has been converted, which will create the matcher
    _ <- convTyCon tc
    defs <- gets csTypeDefs
    case Map.lookup (GHC.getName tc) defs of
        Just (tydMatch -> Just match, _) -> pure $ tdTerm match
        _                                -> throwPlain $ ConversionError "Match has not been converted"

getMatchInstantiated :: Converting m => GHC.Type -> m PLCTerm
getMatchInstantiated = \case
    (GHC.splitTyConApp_maybe -> Just (tc, args)) -> do
        match <- getMatch tc

        args' <- mapM convType args
        pure $ mkIterInst match args'
    -- must be a TC app
    _ -> throwPlain $ ConversionError "Type was not a type constructor application"

convAlt :: Converting m => Bool -> GHC.DataCon -> GHC.CoreAlt -> m PLCTerm
convAlt mustDelay dc (alt, vars, body) = case alt of
    GHC.LitAlt _  -> throwPlain $ UnsupportedError "Literal case"
    GHC.DEFAULT   -> do
        body' <- convExpr body >>= maybeDelay mustDelay
        -- need to consume the args
        argTypes <- mapM convType $ GHC.dataConRepArgTys dc
        argNames <- forM [0..(length argTypes -1)] (\i -> safeFreshName $ "default_arg" ++ show i)
        pure $ mkIterLamAbs (zip argNames argTypes) body'
    -- We just package it up as a lambda bringing all the
    -- vars into scope whose body is the body of the case alternative.
    -- See Note [Iterated abstraction and application]
    -- See Note [Case expressions and laziness]
    GHC.DataAlt _ -> foldr (\v acc -> mkLambda v acc) (convExpr body >>= maybeDelay mustDelay) vars

-- Literals and primitives

{- Note [Literals]
GHC's literals and primitives are a bit of a pain, since they not only have a Literal
containing the actual data, but are wrapped in special functions (often ending in the magic #).

This is a pain to recognize.
-}

convLiteral :: Converting m => GHC.Literal -> m (PLC.Constant ())
convLiteral l = case l of
    -- TODO: better sizes
    GHC.MachInt64 i    -> pure $ PLC.BuiltinInt () haskellIntSize i
    GHC.MachInt i      -> pure $ PLC.BuiltinInt () haskellIntSize i
    GHC.MachStr bs     -> pure $ PLC.BuiltinBS () haskellBSSize (BSL.fromStrict bs)
    GHC.LitInteger _ _ -> throwPlain $ UnsupportedError "Literal (unbounded) integer"
    GHC.MachWord _     -> throwPlain $ UnsupportedError "Literal word"
    GHC.MachWord64 _   -> throwPlain $ UnsupportedError "Literal word64"
    GHC.MachChar _     -> throwPlain $ UnsupportedError "Literal char"
    GHC.MachFloat _    -> throwPlain $ UnsupportedError "Literal float"
    GHC.MachDouble _   -> throwPlain $ UnsupportedError "Literal double"
    GHC.MachLabel {}   -> throwPlain $ UnsupportedError "Literal label"
    GHC.MachNullAddr   -> throwPlain $ UnsupportedError "Literal null"

isPrimitiveWrapper :: GHC.Id -> Bool
isPrimitiveWrapper i = case GHC.idDetails i of
    GHC.DataConWorkId dc -> isPrimitiveDataCon dc
    GHC.VanillaId        -> GHC.getName i == GHC.unpackCStringName
    _                    -> False

isPrimitiveDataCon :: GHC.DataCon -> Bool
isPrimitiveDataCon dc = dc == GHC.intDataCon

-- These never seem to come up, rather we get the typeclass operations. Not sure if we need them.
convPrimitiveOp :: (Converting m) => GHC.PrimOp -> m PLCTerm
convPrimitiveOp = \case
    GHC.IntAddOp  -> pure $ mkIntFun PLC.AddInteger
    GHC.IntSubOp  -> pure $ mkIntFun PLC.SubtractInteger
    GHC.IntMulOp  -> pure $ mkIntFun PLC.MultiplyInteger
    -- check this one
    GHC.IntQuotOp -> pure $ mkIntFun PLC.DivideInteger
    GHC.IntRemOp  -> pure $ mkIntFun PLC.RemainderInteger
    GHC.IntGtOp   -> pure $ mkIntRel PLC.GreaterThanInteger
    GHC.IntGeOp   -> pure $ mkIntRel PLC.GreaterThanEqInteger
    GHC.IntLtOp   -> pure $ mkIntRel PLC.LessThanInteger
    GHC.IntLeOp   -> pure $ mkIntRel PLC.LessThanEqInteger
    GHC.IntEqOp   -> pure $ mkIntRel PLC.EqInteger
    po            -> throwSd UnsupportedError $ "Primitive operation:" GHC.<+> GHC.ppr po

-- Typeclasses

convEqMethod :: (Converting m) => GHC.Name -> m PLCTerm
convEqMethod name
    | name == GHC.eqName = pure $ mkIntRel PLC.EqInteger
    | otherwise = throwSd UnsupportedError $ "Eq method:" GHC.<+> GHC.ppr name

convOrdMethod :: (Converting m) => GHC.Name -> m PLCTerm
convOrdMethod name
    -- only this one has a name defined in the lib??
    | name == GHC.geName = pure $ mkIntRel PLC.GreaterThanEqInteger
    | GHC.getOccString name == ">" = pure $ mkIntRel PLC.GreaterThanInteger
    | GHC.getOccString name == "<=" = pure $ mkIntRel PLC.LessThanEqInteger
    | GHC.getOccString name == "<" = pure $ mkIntRel PLC.LessThanInteger
    | otherwise = throwSd UnsupportedError $ "Ord method:" GHC.<+> GHC.ppr name

convNumMethod :: (Converting m) => GHC.Name -> m PLCTerm
convNumMethod name
    -- only this one has a name defined in the lib??
    | name == GHC.minusName = pure $ mkIntFun PLC.SubtractInteger
    | GHC.getOccString name == "+" = pure $ mkIntFun PLC.AddInteger
    | GHC.getOccString name == "*" = pure $ mkIntFun PLC.MultiplyInteger
    | otherwise = throwSd UnsupportedError $ "Num method:" GHC.<+> GHC.ppr name

-- Plutus primitives

{- Note [Mapping primitives]
We want the user to be able to call the Plutus primitives as normal Haskell functions.

To do this, we provide a library of such functions, and then make a map from their TH names (which we can
derive from the real function declarations, to be sure they match up), to the implementations. We then
need to do some work in the GHC Core monad to translate those mappings into mappings from Core names.
-}

primitiveTermAssociations :: [(TH.Name, Quote (PLC.Term PLC.TyName PLC.Name ()))]
primitiveTermAssociations = [
    ('Prims.concatenate, pure $ instSize haskellIntSize $ mkConstant PLC.Concatenate)
    , ('Prims.takeByteString, pure $ instSize haskellBSSize $ instSize haskellIntSize $ mkConstant PLC.TakeByteString)
    , ('Prims.dropByteString, pure $ instSize haskellBSSize $ instSize haskellIntSize $ mkConstant PLC.DropByteString)
    , ('Prims.sha2_256, pure $ instSize haskellBSSize $ mkConstant PLC.SHA2)
    , ('Prims.sha3_256, pure $ instSize haskellBSSize $ mkConstant PLC.SHA3)
    , ('Prims.verifySignature, pure $ instSize haskellBSSize $ instSize haskellBSSize $ instSize haskellBSSize $ mkConstant PLC.VerifySignature)
    , ('Prims.equalsByteString, pure $ mkBsRel PLC.EqByteString)
    , ('Prims.txhash, pure $ mkConstant PLC.TxHash)
    , ('Prims.blocknum, pure $ instSize haskellIntSize $ mkConstant PLC.BlockNum)
    -- we're representing error at the haskell level as a polymorphic function, so do the same here
    , ('Prims.error, errorFunc)
    ]

primitiveTypeAssociations :: [(TH.Name, Quote (PLC.Type PLC.TyName ()))]
primitiveTypeAssociations = [
    (''Prims.ByteString, pure $ appSize haskellBSSize $ PLC.TyBuiltin () PLC.TyByteString)
    ]

-- | The function 'error :: forall a . () -> a'.
errorFunc :: Quote (PLC.Term PLC.TyName PLC.Name ())
errorFunc = do
    n <- freshTyName () "e"
    -- see Note [Value restriction]
    mangleTyAbs $ PLC.TyAbs () n (PLC.Type ()) (PLC.Error () (PLC.TyVar () n))

-- | The type 'forall a. () -> a'.
errorTy :: Quote (PLC.Type PLC.TyName ())
errorTy = do
    tyname <- safeFreshTyName "a"
    mangleTyForall $ PLC.TyForall () tyname (PLC.Type ()) (PLC.TyVar () tyname)

-- Value restriction

{- Note [Value restriction]
Plutus Core has the traditional *value restriction* on type abstractions - namely, the
body of a type abstraction must be a value.

This causes problems for us because *Haskell* has no such thing. (There is the monomorphism
restriciton, which is similar, but not as restrictive, so it doesn't help us.)

There are two approaches to solving this problem. Currently we use "passing on the value restriction",
but I include a description of mangling to illustrate why the current solution is preferable.

-- Mangling

We can get around this by delaying the body of all our abstractions, thus making them lambdas, which are values.
This then means that we need to change the *types* of all foralls to include the unit argument,
and all instantiations to force the value.

We need to do this everywhere so that the translation of the users' program remains
well-typed. Consider

runST :: (forall s. ST s a) -> a

myCalc :: Int
myCalc = runST $ pure 1

Converting `pure 1`, we would normally turn it into something of type

(all s (type) [ST s Int])

After mangling, this becomes

(all s (type) (fun unit [ST s Int]))

This means we had better convert `runST` into something that expects things of that type instead of
the original type! And we need to add forces to the instantiations inside `runST` otherwise its
body won't be well-typed too.

Note that it's no good to convert some other abstraction where the body is already a value without the delay -
if we did that, then `runST` would be in an impossible place, since it would need to take
either mangled or non-mangled abstractions. The only way we can get away with this without doing complicated
accounting is to do it uniformly: i.e. absolutely everywhere whether we need it in that
case or not.

We need to do this even for the abstractions in our generated matchers for Scott-encoding,
because constructors are user-visible and so can be passed to functions, which might expect them to be
mangled.

-- Passing on the value restriction

An alternative approach would be to pass on the value restriction to the client Haskell code.
This has the advantage of much simpler codegen. However, it has a few annoying cases:

- We can't provide `error :: forall a. a` any more.
- We can't handle `void# :: forall a. a` well any more.

The first is easy: we just make the primitive be mangled `error :: forall a. () -> a`.

The second is a pain. GHC *does* use the polymorphic void. So we take the ad-hoc
expedient of mangling *just* the 'Void#' type. Since nothing can use this "for real",
there are no uses to go wrong so long as we change the type uniformly. This is a
bit of a hack, though.
-}

-- See Note [Value restriction]
mangleTyForall :: (MonadQuote m) => PLCType -> m PLCType
mangleTyForall = \case
    PLC.TyForall a t k body -> PLC.TyForall a t k <$> delayType body
    x -> pure x

-- See Note [Value restriction]
mangleTyAbs :: (MonadQuote m) => PLCTerm -> m PLCTerm
mangleTyAbs = \case
    PLC.TyAbs a t k body -> PLC.TyAbs a t k <$> delay body
    x -> pure x

-- Binder helpers

-- | Builds a lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkLambda :: Converting m => GHC.Var -> m PLCTerm -> m PLCTerm
mkLambda v body = do
    let ghcName = GHC.getName v
    (t', n') <- convVarFresh v
    body' <- local (\c -> c {ccScopes=pushName ghcName n' (ccScopes c)}) body
    pure $ PLC.LamAbs () n' t' body'

-- | Builds a type abstraction, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyAbs :: Converting m => GHC.Var -> m PLCTerm -> m PLCTerm
mkTyAbs v body = do
    let ghcName = GHC.getName v
    (t', k') <- convTyVarFresh v
    body' <- local (\c -> c {ccScopes=pushTyName ghcName t' (ccScopes c)}) body
    ConvertingContext {ccOpts=opts} <- ask
    -- we sometimes need to turn this off, as checking for term values also checks for normalized types at the moment
    unless (not (coCheckValueRestriction opts) || PLC.isTermValue body') $ throwPlain $ ValueRestrictionError "Type abstraction body is not a value"
    pure $ PLC.TyAbs () t' k' body'

-- | Builds a forall, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyForall :: Converting m => GHC.Var -> m PLCType -> m PLCType
mkTyForall v body = do
    let ghcName = GHC.getName v
    (t', k') <- convTyVarFresh v
    body' <- local (\c -> c {ccScopes=pushTyName ghcName t' (ccScopes c)}) body
    pure $ PLC.TyForall () t' k' body'

-- | Builds a type lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyLam :: Converting m => GHC.Var -> m PLCType -> m PLCType
mkTyLam v body = do
    let ghcName = GHC.getName v
    (t', k') <- convTyVarFresh v
    body' <- local (\c -> c {ccScopes=pushTyName ghcName t' (ccScopes c)}) body
    pure $ PLC.TyLam () t' k' body'

{- Note [Recursive lets]
We need to define these with a fixpoint. We can derive a fixpoint operator for values
already.

However, we also need to work out how to encode recursion over multiple values simultaneously.
The answer is simple - we pass them through as a tuple.

Overall, the translation looks like this. We convert this:

let rec
  f_1 = b_1
  ...
  f_i = b_i
in
  result

into this:

($fixN i$ (\choose f1 ... fi . choose b_1 ... b_i))
(\f1 ... fi . result)
-}

-- Expressions

convExpr :: Converting m => GHC.CoreExpr -> m PLCTerm
convExpr e = withContextM (sdToTxt $ "Converting expr:" GHC.<+> GHC.ppr e) $ do
    -- See Note [Scopes]
    ConvertingContext {ccPrimTerms=prims, ccScopes=stack} <- ask
    let top = NE.head stack
    case e of
        -- See Note [Literals]
        GHC.App (GHC.Var (isPrimitiveWrapper -> True)) arg -> convExpr arg
        -- special typeclass method calls
        GHC.App (GHC.App
                -- eq class method
                (GHC.Var n@(GHC.idDetails -> GHC.ClassOpId ((==) GHC.eqClassName . GHC.getName -> True)))
                -- we only support applying to int
                (GHC.Type (GHC.eqType GHC.intTy -> True)))
            -- last arg is typeclass dictionary
            _ -> convEqMethod (GHC.getName n)
        GHC.App (GHC.App
                -- ord class method
                (GHC.Var n@(GHC.idDetails -> GHC.ClassOpId ((==) GHC.ordClassName . GHC.getName -> True)))
                -- we only support applying to int
                (GHC.Type (GHC.eqType GHC.intTy -> True)))
            -- last arg is typeclass dictionary
            _ -> convOrdMethod (GHC.getName n)
        GHC.App (GHC.App
                -- num class method
                (GHC.Var n@(GHC.idDetails -> GHC.ClassOpId ((==) GHC.numClassName . GHC.getName -> True)))
                -- we only support applying to int
                (GHC.Type (GHC.eqType GHC.intTy -> True)))
            -- last arg is typeclass dictionary
            _ -> convNumMethod (GHC.getName n)
        -- void# - values of type void get represented as error, since they should be unreachable
        GHC.Var n | n == GHC.voidPrimId || n == GHC.voidArgId -> liftQuote errorFunc
        -- locally bound vars
        GHC.Var (lookupName top . GHC.getName -> Just name) -> pure $ PLC.Var () name
        -- Special kinds of id
        GHC.Var (GHC.idDetails -> GHC.PrimOpId po) -> convPrimitiveOp po
        GHC.Var (GHC.idDetails -> GHC.DataConWorkId dc) ->
            let
                tc = GHC.dataConTyCon dc
            in do
                dcs <- getDataCons tc
                constrs <- getConstructors tc

                -- TODO: this is inelegant
                index <- case elemIndex dc dcs of
                    Just i  -> pure i
                    Nothing -> throwPlain $ ConversionError "Data constructor not in the type constructor's list of constructors!"

                pure $ constrs !! index
        GHC.Var (flip Map.lookup prims . GHC.getName -> Just term) -> liftQuote term
        -- the term we get must be closed - we don't resolve most references
        -- TODO: possibly relax this?
        GHC.Var n@(GHC.idDetails -> GHC.VanillaId) -> throwSd FreeVariableError $ "Variable:" GHC.<+> GHC.ppr n GHC.$+$ (GHC.ppr $ GHC.idDetails n)
        GHC.Var n -> throwSd UnsupportedError $ "Variable" GHC.<+> GHC.ppr n GHC.$+$ (GHC.ppr $ GHC.idDetails n)
        GHC.Lit lit -> PLC.Constant () <$> convLiteral lit
        -- arg can be a type here, in which case it's a type instantiation
        GHC.App l (GHC.Type t) -> PLC.TyInst () <$> convExpr l <*> convType t
        -- otherwise it's a normal application
        GHC.App l arg -> PLC.Apply () <$> convExpr l <*> convExpr arg
        -- if we're biding a type variable it's a type abstraction
        GHC.Lam b@(GHC.isTyVar -> True) body -> mkTyAbs b $ convExpr body
        -- othewise it's a normal lambda
        GHC.Lam b body -> mkLambda b $ convExpr body
        GHC.Let (GHC.NonRec b arg) body -> do
            -- convert it as a lambda
            a' <- convExpr arg
            l' <- mkLambda b $ convExpr body
            pure $ PLC.Apply () l' a'
        GHC.Let (GHC.Rec bs) body -> do
            -- See note [Recursive lets]
            -- TODO: we're technically using these twice, which is bad and maybe we need to duplicate
            tys <- mapM convType (fmap (GHC.varType . fst) bs)
            -- The pairs of types we'll need for fixN
            asbs <- forM tys $ \case
                PLC.TyFun () i o -> pure (i, o)
                _ -> throwPlain $ ConversionError "Recursive values must be of function type. You may need to manually add unit arguments."

            -- We need this so we can use the tuple of recursive functions in the end - it
            -- expects an output type.
            outTy <- convType (GHC.exprType body)

            q <- safeFreshTyName "Q"
            choose <- safeFreshName "choose"
            let chooseTy = mkIterTyFun tys (PLC.TyVar () q)

            -- \f1 ... fn -> choose b1 ... bn
            bsLam <- flip (foldr (\b acc -> mkLambda b acc)) (fmap fst bs) $ do
                rhss <- mapM convExpr (fmap snd bs)
                pure $ mkIterApp (PLC.Var() choose) rhss

            -- abstract out Q and choose
            let cLam = PLC.TyAbs () q (PLC.Type ()) $ PLC.LamAbs () choose chooseTy bsLam

            -- fixN {A1 B1 ... An Bn}
            instantiatedFix <- do
                fixN <- liftQuote $ Function.getBuiltinFixN (length bs)
                pure $ mkIterInst fixN $ foldMap (\(a, b) -> [a, b]) asbs

            let fixed = PLC.Apply () instantiatedFix cLam

            -- the consumer of the recursive functions
            bodyLam <- foldr (\b acc -> mkLambda b acc) (convExpr body) (fmap fst bs)
            pure $ PLC.Apply () (PLC.TyInst () fixed outTy) bodyLam
        GHC.Case scrutinee b t alts -> do
            let scrutineeType = GHC.varType b

            -- See Note [Case expressions and laziness]
            isValueAlt <- mapM (\(_, vars, body) -> if null vars then PLC.isTermValue <$> convExpr body else pure True) alts
            let lazyCase = not $ and isValueAlt

            scrutinee' <- convExpr scrutinee

            match <- getMatchInstantiated scrutineeType
            let matched = PLC.Apply () match scrutinee'

            -- See Note [Scott encoding of datatypes]
            -- we're going to delay the body, so the scrutinee needs to be instantiated the delayed type
            instantiated <- PLC.TyInst () matched <$> (convType t >>= maybeDelayType lazyCase)

            tc <- case GHC.splitTyConApp_maybe scrutineeType of
                Just (tc, _) -> pure tc
                Nothing      -> throwPlain $ ConversionError "Scrutinee's type was not a type constructor application"
            dcs <- getDataCons tc

            branches <- forM dcs $ \dc -> case GHC.findAlt (GHC.DataAlt dc) alts of
                Just alt -> convAlt lazyCase dc alt
                Nothing  -> throwPlain $ ConversionError "No case matched and no default case"

            let applied = mkIterApp instantiated branches
            -- See Note [Case expressions and laziness]
            maybeForce lazyCase applied
        -- ignore annotation
        GHC.Tick _ body -> convExpr body
        GHC.Cast body coerce -> do
            body' <- convExpr body
            case splitNewtypeCoercion coerce of
                Just (Unwrap outer inner) -> do
                    match <- getMatchInstantiated outer
                    -- unwrap by doing a "trivial match" - instantiate to the inner type and apply the identity
                    inner' <- convType inner
                    let instantiated = PLC.TyInst () (PLC.Apply () match body') inner'
                    name <- safeFreshName "inner"
                    let identity = PLC.LamAbs () name inner' (PLC.Var () name)
                    pure $ PLC.Apply () instantiated identity
                Just (Wrap _ outer) -> do
                    constr <- head <$> getConstructorsInstantiated outer
                    pure $ PLC.Apply () constr body'
                _ -> throwSd UnsupportedError $ "Coercion" GHC.$+$ GHC.ppr coerce
        GHC.Type _ -> throwPlain $ ConversionError "Cannot convert types directly, only as arguments to applications"
        GHC.Coercion _ -> throwPlain $ ConversionError "Coercions should not be converted"

convExprWithDefs :: Converting m => GHC.CoreExpr -> m PLCTerm
convExprWithDefs e = do
    converted <- convExpr e
    ConvertingState{csTypeDefs=typeDs, csTermDefs=termDs} <- get
    wrapWithDefs typeDs termDs converted
