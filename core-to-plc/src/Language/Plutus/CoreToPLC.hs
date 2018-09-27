{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}

module Language.Plutus.CoreToPLC where

import           Language.Plutus.CoreToPLC.Builtins
import           Language.Plutus.CoreToPLC.Error
import           Language.Plutus.CoreToPLC.Laziness
import qualified Language.Plutus.CoreToPLC.Primitives     as Prims
import           Language.Plutus.CoreToPLC.Types

import qualified GhcPlugins                               as GHC
import qualified Kind                                     as GHC
import qualified MkId                                     as GHC
import qualified Pair                                     as GHC
import qualified PrelNames                                as GHC
import qualified PrimOp                                   as GHC
import qualified TysPrim                                  as GHC

import qualified Language.PlutusCore                      as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Function as Function
import qualified Language.PlutusCore.StdLib.Data.Unit     as Unit

import qualified Language.Haskell.TH.Syntax               as TH

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Bifunctor
import qualified Data.ByteString.Lazy                     as BSL
import           Data.Char
import           Data.Foldable
import qualified Data.List.NonEmpty                       as NE
import qualified Data.Map                                 as Map
import qualified Data.Text                                as T
import qualified Data.Text.Encoding                       as TE

import           Data.List                                (elemIndex)

import           Debug.Trace

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
                []      -> trace ("Bad name: " ++ s) "bad_name"
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

convTyVarFresh :: Converting m => GHC.TyVar -> m (PLC.Kind () , PLC.TyName ())
convTyVarFresh v = do
    k' <- convKind $ GHC.tyVarKind v
    t' <- convTyNameFresh $ GHC.getName v
    pure (k', t')

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
        -- See Note [Iterated abstraction and application]
        pure $ foldl' (\acc t -> PLC.TyApp () acc t) tc' args'

convTyCon :: (Converting m) => GHC.TyCon -> m PLCType
convTyCon tc = handleMaybeRecType (GHC.getName tc) $ do
    ConvertingContext {ccPrimTypes=prims} <- ask
    -- could be a Plutus primitive type
    case Map.lookup (GHC.getName tc) prims of
        Just ty -> liftQuote ty
        Nothing -> do
            -- See note [Spec booleans and Haskell booleans]
            -- we don't have to do anything here because it's symmetrical, but morally we should
            dcs <- getDataCons tc
            convDataCons tc dcs

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

-- | Try to convert a type, using the given action to convert it.
handleMaybeRecType :: (Converting m) => GHC.Name -> m PLCType -> m PLCType
handleMaybeRecType n act = do
    tds <- gets csTypeDefs
    case Map.lookup n tds of
        Just (InProgress tyname) -> pure $ PLC.TyVar () tyname
        -- Either already seen and done or not seen.
        -- Ideally we would store the finished type, but we actually need to
        -- store a version in Quote so we can recreate it safely in multiple
        _ -> do
            tyname <- convTyNameFresh n
            modify $ \cs -> cs { csTypeDefs = Map.insert n (InProgress tyname) (csTypeDefs cs)}
            converted <- act
            modify $ \cs -> cs { csTypeDefs = Map.insert n Done (csTypeDefs cs)}
            pure converted

{- Note [Detecting recursive types in GHC]
This seems to be surprisingly difficult, and as far as I can tell there is nothing built in to
do this.

We can handle the self-recursive case easily enough, since we just look for the very name of
the type constructor we're converting.

For mutually recursive types we'll need to do a SCC analysis on the type dependency graph. We
can do this as we go, but we'll want to cache it. At the moment getting the information to
do this out of GHC seems hard.
-}

isSelfRecursiveTyCon :: (Converting m) => GHC.TyCon -> m Bool
isSelfRecursiveTyCon tc = do
    -- See Note [Detecting recursive types in GHC]
    dcs <- getDataCons tc
    let usedTcs = GHC.unionManyUniqSets $ (\dc -> GHC.unionManyUniqSets $ GHC.tyConsOfType <$> GHC.dataConRepArgTys dc) <$> dcs
    pure $ GHC.elementOfUniqSet tc usedTcs

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
    let withApps = foldl' (\acc arg -> PLC.TyApp () acc arg) noFix tas
    pure (withApps, fixVar)

stripTyApps :: PLC.Type PLC.TyName () -> (PLC.Type PLC.TyName(), [PLC.Type PLC.TyName ()])
stripTyApps = \case
    PLC.TyApp _ ty1 ty2 -> let (ty', tas) = stripTyApps ty1 in (ty', ty2:tas)
    x -> (x, [])

-- Data

{- Note [Scott encoding of datatypes]
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

Consider a datatype T with type parameter t_i, constructors c_j with arguments a_c_j_k of types
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

getDataCons :: (Converting m) =>  GHC.TyCon -> m [GHC.DataCon]
getDataCons tc
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
    abstracted <- flip (foldr (\tv acc -> mkTyLam tv acc)) (GHC.tyConTyVars tc) $ do
        resultType <- safeFreshTyName $ (GHC.getOccString $ GHC.getName tc) ++ "_matchOut"
        cases <- mapM (dataConCaseType (PLC.TyVar () resultType)) dcs
        pure $ mkScottTyBody resultType cases

    tds <- gets csTypeDefs
    isSelfRecursive <- isSelfRecursiveTyCon tc
    if isSelfRecursive
    then case Map.lookup (GHC.getName tc) tds of
        Just (InProgress tyname) -> pure $ PLC.TyFix () tyname abstracted
        _                        -> throwPlain $ ConversionError "Could not find var to fix over"
    else pure abstracted

mkScottTyBody :: PLC.TyName () -> [PLCType] -> PLCType
mkScottTyBody resultTypeName cases =
    let
        -- we can only match into kind Type
        resultKind = PLC.Type ()
        -- See Note [Iterated abstraction and application]
        -- case_1 -> ... -> case_n -> resultType
        funcs = foldr (\t acc -> PLC.TyFun () t acc) (PLC.TyVar () resultTypeName) cases
        -- forall resultType . funcs
        resultAbstracted = PLC.TyForall () resultTypeName resultKind funcs
    in resultAbstracted

dataConCaseType :: Converting m => PLCType -> GHC.DataCon -> m PLCType
dataConCaseType resultType dc = withContextM (sdToTxt $ "Converting data constructor:" GHC.<+> GHC.ppr dc) $
    if not (GHC.isVanillaDataCon dc) then throwSd UnsupportedError $ "Non-vanilla data constructor:" GHC.<+> GHC.ppr dc
    else do
        let argTys = GHC.dataConRepArgTys dc
        args <- mapM convType argTys
        -- See Note [Iterated abstraction and application]
        -- t_1 -> ... -> t_m -> resultType
        pure $ foldr (\t acc -> PLC.TyFun () t acc) resultType args

-- This is the creation of the Scott-encoded constructor value.
convConstructor :: Converting m => GHC.DataCon -> m PLCExpr
convConstructor dc =
    let
        tc = GHC.dataConTyCon dc
        tcTyVars = GHC.tyConTyVars tc
        tcName = GHC.getOccString $ GHC.getName tc
        dcName = GHC.getOccString $ GHC.getName dc
    in
        -- no need for a body value check here, we know it's a lambda (see Note [Value restriction])
        -- /\ tv_1 .. tv_n . body
        flip (foldr (\tv acc -> mkTyAbs tv acc)) tcTyVars $ do
            -- See Note [Scott encoding of datatypes]
            resultType <- safeFreshTyName $ tcName ++ "_matchOut"
            dcs <- getDataCons tc
            -- See Note [Spec booleans and Haskell booleans]
            let maybeSwapped = if tc == GHC.boolTyCon then reverse dcs else dcs
            index <- case elemIndex dc maybeSwapped of
                Just i  -> pure i
                Nothing -> throwPlain $ ConversionError "Data constructor not in the type constructor's list of constructors!"
            caseTypes <- mapM (dataConCaseType (PLC.TyVar () resultType)) maybeSwapped
            caseArgNames <- mapM (convNameFresh . GHC.getName) maybeSwapped
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
    -> PLCExpr
mkScottConstructorBody resultTypeName caseNamesAndTypes argNamesAndTypes index maybePf =
    let
        -- data types are always in kind Type
        resultKind = PLC.Type ()
        thisConstructor = fst $ caseNamesAndTypes !! index
        -- See Note [Iterated abstraction and application]
        -- c_i a_1 .. a_m
        applied = foldl' (\acc a -> PLC.Apply () acc (PLC.Var () a)) (PLC.Var () thisConstructor) (fmap fst argNamesAndTypes)
        -- \c_1 .. c_n . applied
        cfuncs = foldr (\(name, t) acc -> PLC.LamAbs () name t acc) applied caseNamesAndTypes
        -- no need for a body value check here, we know it's a lambda (see Note [Value restriction])
        -- forall r . cfuncs
        resAbstracted = PLC.TyAbs () resultTypeName resultKind cfuncs
        -- wrap resAbstracted
        fixed = case maybePf of
            Just (pf, n) -> PLC.Wrap () n pf resAbstracted
            Nothing      -> resAbstracted
        -- \a_1 .. a_m . fixed
        afuncs = foldr (\(name, t) acc -> PLC.LamAbs () name t acc) fixed argNamesAndTypes
    in afuncs

convAlt :: Converting m => Bool -> GHC.DataCon -> GHC.CoreAlt -> m PLCExpr
convAlt mustDelay dc (alt, vars, body) = case alt of
    GHC.LitAlt _  -> throwPlain $ UnsupportedError "Literal case"
    GHC.DEFAULT   -> do
        body' <- convExpr body >>= maybeDelay mustDelay
        -- need to consume the args
        argTypes <- mapM convType $ GHC.dataConRepArgTys dc
        argNames <- forM [0..(length argTypes -1)] (\i -> safeFreshName $ "default_arg" ++ show i)
        -- See Note [Iterated abstraction and application]
        pure $ foldr (\(n', t') acc -> PLC.LamAbs () n' t' acc) body' (zip argNames argTypes)
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
convPrimitiveOp :: (Converting m) => GHC.PrimOp -> m PLCExpr
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

convEqMethod :: (Converting m) => GHC.Name -> m PLCExpr
convEqMethod name
    | name == GHC.eqName = pure $ mkIntRel PLC.EqInteger
    | otherwise = throwSd UnsupportedError $ "Eq method:" GHC.<+> GHC.ppr name

convOrdMethod :: (Converting m) => GHC.Name -> m PLCExpr
convOrdMethod name
    -- only this one has a name defined in the lib??
    | name == GHC.geName = pure $ mkIntRel PLC.GreaterThanEqInteger
    | GHC.getOccString name == ">" = pure $ mkIntRel PLC.GreaterThanInteger
    | GHC.getOccString name == "<=" = pure $ mkIntRel PLC.LessThanEqInteger
    | GHC.getOccString name == "<" = pure $ mkIntRel PLC.LessThanInteger
    | otherwise = throwSd UnsupportedError $ "Ord method:" GHC.<+> GHC.ppr name

convNumMethod :: (Converting m) => GHC.Name -> m PLCExpr
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
mangleTyAbs :: (MonadQuote m) => PLCExpr -> m PLCExpr
mangleTyAbs = \case
    PLC.TyAbs a t k body -> PLC.TyAbs a t k <$> delay body
    x -> pure x

-- Binder helpers

-- | Builds a lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkLambda :: Converting m => GHC.Var -> m PLCExpr -> m PLCExpr
mkLambda v body = do
    let ghcName = GHC.getName v
    (t', n') <- convVarFresh v
    body' <- local (\c -> c {ccScopes=pushName ghcName n' (ccScopes c)}) body
    pure $ PLC.LamAbs () n' t' body'

-- | Builds a type abstraction, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyAbs :: Converting m => GHC.Var -> m PLCExpr -> m PLCExpr
mkTyAbs v body = do
    let ghcName = GHC.getName v
    (k', t') <- convTyVarFresh v
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
    (k', t') <- convTyVarFresh v
    body' <- local (\c -> c {ccScopes=pushTyName ghcName t' (ccScopes c)}) body
    pure $ PLC.TyForall () t' k' body'

-- | Builds a type lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyLam :: Converting m => GHC.Var -> m PLCType -> m PLCType
mkTyLam v body = do
    let ghcName = GHC.getName v
    (k', t') <- convTyVarFresh v
    body' <- local (\c -> c {ccScopes=pushTyName ghcName t' (ccScopes c)}) body
    pure $ PLC.TyLam () t' k' body'


-- See Note [Recursion with Z]
delayFunction :: MonadQuote m => PLCType -> PLCExpr -> m PLCExpr
delayFunction ty f = do
    n <- safeFreshName "arg"
    forcedUse <- force $ PLC.Var () n
    dType <- delayType ty
    pure $ PLC.LamAbs () n dType $ PLC.Apply () f forcedUse

-- Tuples

mkTupleType :: MonadQuote m => [PLCType] -> m PLCType
mkTupleType tys = do
    resultType <- safeFreshTyName "tuple_matchOut"
    let cases = [foldr (\v acc -> PLC.TyFun () v acc) (PLC.TyVar () resultType) tys]
    pure $ mkScottTyBody resultType cases

mkTupleConstructor :: MonadQuote m => [PLCType] -> m PLCExpr
mkTupleConstructor argTys = do
    resultType <- safeFreshTyName "tuple_matchOut"
    caseName <- safeFreshName "c"
    let caseNamesAndTypes = [(caseName, foldr (\v acc -> PLC.TyFun () v acc) (PLC.TyVar () resultType) argTys)]
    argNames <- forM [0..(length argTys -1)] (\i -> safeFreshName $ "tuple_arg" ++ show i)
    pure $ mkScottConstructorBody resultType caseNamesAndTypes (zip argNames argTys) 0 Nothing

-- Functions

{- Note [Recursion with Z]
XXX: THIS IS VERY WRONG, REVISIT LATER

How do we handle fixpoints of functions `a -> a` when we only have the Z combinator?

We translate the value as a function `() -> a` instead, and force it immediately in the
body. This way the semantics are still strict.

Translating `f :: a -> a` to a function `(() -> a) -> () -> a)` is easy, you just do
`delay . f . force`.
-}

-- | A fixpoint combinator on functions of type @a -> a@.
fixY :: MonadQuote m => PLCType -> PLCExpr -> m PLCExpr
fixY ty f = do
    unitTy <- liftQuote Unit.getBuiltinUnit
    z <- liftQuote Function.getBuiltinFix
    let instantiated = PLC.TyInst () (PLC.TyInst () z unitTy) ty
    -- See Note [Recursion with Z]
    zFunction <- delayFunction ty f
    pure $ PLC.Apply () instantiated zFunction


{- Note [Recursive lets]
We need to define these with a fixpoint. We can derive a fixpoint operator for values
already (see Note [Recursion with Z]).

However, we also need to work out how to encode recursion over multiple values simultaneously.
The answer is simple - we pass them through as a tuple.

Overall, the translation looks like this. We convert this:

let rec
  a_1 = b_1
  ..
  a_i = b_i
in
  result

into this (with a lot of noise due to our let-bindings becoming lambdas):

(\tuple ->
  tuple
  (\a_1 ->
    ..
    result
  )
)
(fixY
  (\tuple ->
    tuple
    (\a_1 ->
      ..
      tuple_i b_1 .. b_i
    )
  )
)
-}

{- Note [Spec booleans and Haskell booleans]
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
-}


-- The main function

convExpr :: Converting m => GHC.CoreExpr -> m PLCExpr
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
        GHC.Var (GHC.idDetails -> GHC.DataConWorkId dc) -> convConstructor dc
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
            tys <- mapM convType (fmap (GHC.varType . fst) bs)
            forM_ tys $ \case
                PLC.TyFun {} -> pure ()
                _ -> throwPlain $ ConversionError "Recursive values must be of function type. You may need to manually add unit arguments."
            tupleTy <- mkTupleType tys

            bsLam <- flip (foldr (\b acc -> mkLambda b acc)) (fmap fst bs) $ do
                rhss <- mapM convExpr (fmap snd bs)
                tupleConstructor <- mkTupleConstructor tys
                let tuple = foldl' (\acc rhs -> PLC.Apply () acc rhs) tupleConstructor rhss
                pure tuple

            tupleArg <- safeFreshName "tuple"
            let tupleFun = PLC.LamAbs () tupleArg tupleTy $ PLC.Apply () (PLC.Var () tupleArg) bsLam
            fixed <- fixY tupleTy tupleFun

            bodyLam <- foldr (\b acc -> mkLambda b acc) (convExpr body) (fmap fst bs)
            pure $ PLC.Apply () bodyLam fixed
        GHC.Case scrutinee b t alts -> do
            let scrutineeType = GHC.varType b
            -- must be a TC app
            tc <- case GHC.splitTyConApp_maybe scrutineeType of
                Just (tc, _) -> pure tc
                Nothing      -> throwPlain $ ConversionError "Scrutinee's type was not a type constructor application"

            -- See Note [Case expressions and laziness]
            isValueAlt <- mapM (\(_, vars, body) -> if null vars then PLC.isTermValue <$> convExpr body else pure True) alts
            let lazyCase = not $ and isValueAlt

            scrutinee' <- convExpr scrutinee
            -- unwrap the fixpoint if necessary
            isSelfRecursive <- isSelfRecursiveType scrutineeType
            let unwrapped = if isSelfRecursive then PLC.Unwrap () scrutinee' else scrutinee'
            -- See Note [Scott encoding of datatypes]
            -- we're going to delay the body, so the scrutinee needs to be instantiated the delayed type
            instantiated <- PLC.TyInst () unwrapped <$> (convType t >>= maybeDelayType lazyCase)

            dcs <- getDataCons tc
            -- See Note [Spec booleans and Haskell booleans]
            let maybeSwapped = if tc == GHC.boolTyCon then reverse dcs else dcs

            branches <- forM maybeSwapped $ \dc -> case GHC.findAlt (GHC.DataAlt dc) alts of
                Just alt -> convAlt lazyCase dc alt
                Nothing  -> throwPlain $ ConversionError "No case matched and no default case"

            -- See Note [Iterated abstraction and application]
            let applied = foldl' (\acc alt -> PLC.Apply () acc alt) instantiated branches
            -- See Note [Case expressions and laziness]
            maybeForce lazyCase applied
        -- ignore annotation
        GHC.Tick _ body -> convExpr body
        GHC.Cast body coerce -> do
            body' <- convExpr body
            case splitNewtypeCoercion coerce of
                Just (Unwrap _ inner) -> do
                    -- unwrap by doing a "trivial match" - instantiate to the inner type and apply the identity
                    inner' <- convType inner
                    let instantiated = PLC.TyInst () body' inner'
                    name <- safeFreshName "inner"
                    let identity = PLC.LamAbs () name inner' (PLC.Var () name)
                    pure $ PLC.Apply () instantiated identity
                Just (Wrap inner _) -> do
                    -- wrap by creating a matcher
                    -- could treat this like a unary tuple, but I think it's clearer to do it on its own
                    inner' <- convType inner
                    tyName <- safeFreshTyName "match_out"
                    name <- safeFreshName "c"
                    -- no need for a body value check here, we know it's a lambda (see Note [Value restriction])
                    pure $ PLC.TyAbs () tyName (PLC.Type ()) $ PLC.LamAbs () name (PLC.TyFun () inner' (PLC.TyVar () tyName)) $ PLC.Apply () (PLC.Var () name) body'
                _ -> throwSd UnsupportedError $ "Coercion" GHC.$+$ GHC.ppr coerce
        GHC.Type _ -> throwPlain $ ConversionError "Cannot convert types directly, only as arguments to applications"
        GHC.Coercion _ -> throwPlain $ ConversionError "Coercions should not be converted"
