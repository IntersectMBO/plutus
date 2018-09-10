{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

module Language.Plutus.CoreToPLC where

import           Language.Plutus.CoreToPLC.Error

import qualified Class                                    as GHC
import qualified GhcPlugins                               as GHC
import qualified Kind                                     as GHC
import qualified PrelNames                                as GHC
import qualified PrimOp                                   as GHC

import           GHC.Natural

import qualified Language.PlutusCore                      as PC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Function as Function
import qualified Language.PlutusCore.StdLib.Data.Unit     as Unit

import           Control.Monad.Except
import           Control.Monad.Reader

import           Data.Bifunctor
import qualified Data.ByteString.Lazy                     as BSL
import           Data.Char
import           Data.Foldable
import qualified Data.List.NonEmpty                       as NE
import qualified Data.Map                                 as Map
import qualified Data.Text                                as T
import qualified Data.Text.Encoding                       as TE

import           Data.List                                (elemIndex)

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

-- Useful synonyms and functions

type PCExpr = PC.Term PC.TyName PC.Name ()
type PCType = PC.Type PC.TyName ()
-- See Note [Scopes]
type Converting m = (Monad m, MonadError (Error ()) m, MonadQuote m, MonadReader (ScopeStack, GHC.DynFlags) m)

strToBs :: String -> BSL.ByteString
strToBs = BSL.fromStrict . TE.encodeUtf8 . T.pack

bsToStr :: BSL.ByteString -> String
bsToStr = T.unpack . TE.decodeUtf8 . BSL.toStrict

sdToTxt :: (MonadReader (ScopeStack, GHC.DynFlags) m) => GHC.SDoc -> m T.Text
sdToTxt sd = do
  (_, flags) <- ask
  pure $ T.pack $ GHC.showSDoc flags sd

conversionFail :: (MonadError (Error ()) m, MonadReader (ScopeStack, GHC.DynFlags) m) => GHC.SDoc -> m a
conversionFail = (throwError . ConversionError) <=< sdToTxt

unsupported :: (MonadError (Error ()) m, MonadReader (ScopeStack, GHC.DynFlags) m) => GHC.SDoc -> m a
unsupported = (throwError . UnsupportedError) <=< sdToTxt

freeVariable :: (MonadError (Error ()) m, MonadReader (ScopeStack, GHC.DynFlags) m) => GHC.SDoc -> m a
freeVariable = (throwError . FreeVariableError) <=< sdToTxt

-- Names and scopes

{- Note [Scopes]
We need a notion of scope, because we have to make sure that if we convert a GHC
Var into a variable, then we always convert it into the same variable, while also making
sure that if we encounter multiple things with the same name we produce fresh variables
appropriately.

So we have the usual mechanism of carrying around a stack of scopes.
-}

data Scope = Scope (Map.Map GHC.Name (PC.Name ())) (Map.Map GHC.Name (PC.TyName ()))
type ScopeStack = NE.NonEmpty Scope

initialScopeStack :: ScopeStack
initialScopeStack = pure $ Scope Map.empty Map.empty

lookupName :: Scope -> GHC.Name -> Maybe (PC.Name ())
lookupName (Scope ns _) n = Map.lookup n ns

{- Note [PLC names]
We convert names from Haskell names quite frequently here, but PLC admits a much
smaller set of valid identifiers. We compromise by mangling the identifier, but
in the long run it would be nice to have a more principled encoding so we can
support unicode identifiers as well.
-}

safeFreshName :: MonadQuote m => String -> m (PC.Name ())
safeFreshName s = let
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
              (c:cs)  -> toLower c : cs
      in liftQuote $ freshName () $ strToBs fixed

convNameFresh :: MonadQuote m => GHC.Name -> m (PC.Name ())
convNameFresh n = safeFreshName $ GHC.getOccString n

convVarFresh :: Converting m => GHC.Var -> m (PCType, PC.Name ())
convVarFresh v = do
    t' <- convType $ GHC.varType v
    n' <- convNameFresh $ GHC.varName v
    pure (t', n')

lookupTyName :: Scope -> GHC.Name -> Maybe (PC.TyName ())
lookupTyName (Scope _ tyns) n = Map.lookup n tyns

safeFreshTyName :: MonadQuote m => String -> m (PC.TyName ())
safeFreshTyName s = PC.TyName <$> safeFreshName s

convTyNameFresh :: MonadQuote m => GHC.Name -> m (PC.TyName ())
convTyNameFresh n = PC.TyName <$> convNameFresh n

convTyVarFresh :: Converting m => GHC.TyVar -> m (PC.Kind () , PC.TyName ())
convTyVarFresh v = do
    k' <- convKind $ GHC.tyVarKind v
    t' <- convTyNameFresh $ GHC.varName v
    pure (k', t')

pushName :: GHC.Name -> PC.Name () -> ScopeStack -> ScopeStack
pushName ghcName n stack = let Scope ns tyns = NE.head stack in Scope (Map.insert ghcName n ns) tyns NE.<| stack

pushTyName :: GHC.Name -> PC.TyName () -> ScopeStack -> ScopeStack
pushTyName ghcName n stack = let Scope ns tyns = NE.head stack in Scope ns (Map.insert ghcName n tyns) NE.<| stack

-- Types and kinds

haskellIntSize :: Natural
haskellIntSize = 64

haskellBSSize :: Natural
haskellBSSize = 64

convKind :: Converting m => GHC.Kind -> m (PC.Kind ())
convKind k = case k of
    -- this is a bit weird because GHC uses 'Type' to represent kinds, so '* -> *' is a 'TyFun'
    (GHC.isStarKind -> True)              -> pure $ PC.Type ()
    (GHC.splitFunTy_maybe -> Just (i, o)) -> PC.KindArrow () <$> convKind i <*> convKind o
    _                                     -> unsupported $ "Kind:" GHC.<+> GHC.ppr k

convType :: Converting m => GHC.Type -> m PCType
convType t = do
    -- See Note [Scopes]
    (stack, _) <- ask
    let top = NE.head stack
    case t of
        (GHC.getTyVar_maybe -> Just (lookupTyName top . GHC.varName -> Just name)) -> pure $ PC.TyVar () name
        (GHC.getTyVar_maybe -> Just v) -> freeVariable $ "Type variable:" GHC.<+> GHC.ppr v
        (GHC.splitFunTy_maybe -> Just (i, o)) -> PC.TyFun () <$> convType i <*> convType o
        (GHC.splitTyConApp_maybe -> Just (tc, ts)) -> convTyConApp tc ts
        (GHC.splitForAllTy_maybe -> Just (tv, tpe)) -> mkTyForall tv (convType tpe)
        -- I think it's safe to ignore the coercion here
        (GHC.splitCastTy_maybe -> Just (tpe, _)) -> convType tpe
        _ -> unsupported $ "Type" GHC.<+> GHC.ppr t

convTyConApp :: (Converting m) => GHC.TyCon -> [GHC.Type] -> m PCType
convTyConApp tc ts
    -- this is Int
    | tc == GHC.intTyCon = pure $ PC.TyApp () (PC.TyBuiltin () PC.TyInteger) (PC.TyInt () haskellIntSize)
    -- this is Int#, can we do this nicer?
    | (GHC.getOccString $ GHC.tyConName tc) == "Int#" = pure $ PC.TyApp () (PC.TyBuiltin () PC.TyInteger) (PC.TyInt () haskellIntSize)
    | otherwise = do
        tc' <- convTyCon tc
        args' <- mapM convType ts
        -- See Note [Iterated abstraction and application]
        pure $ foldl' (\acc t -> PC.TyApp () acc t) tc' args'

convTyCon :: (Converting m) => GHC.TyCon -> m PCType
convTyCon tc = do
    dcs <- getDataCons tc
    convDataCons tc dcs

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

More generally, we compile case expressions (of which an if expression is one) lazily, i.e. we add
a unit argument and apply it at the end.
-}

getDataCons :: (Converting m) =>  GHC.TyCon -> m [GHC.DataCon]
getDataCons tc
    | GHC.isAlgTyCon tc || GHC.isTupleTyCon tc = case GHC.algTyConRhs tc of
        GHC.AbstractTyCon                -> unsupported $ "Abstract type:" GHC.<+> GHC.ppr tc
        GHC.DataTyCon{GHC.data_cons=dcs} -> pure dcs
        GHC.TupleTyCon{GHC.data_con=dc}  -> pure [dc]
        GHC.SumTyCon{}                   -> unsupported $ "Sum type:" GHC.<+> GHC.ppr tc
        GHC.NewTyCon{}                   -> unsupported $ "Newtype:" GHC.<+> GHC.ppr tc
    | otherwise = unsupported $ "Type constructor:" GHC.<+> GHC.ppr tc

-- This is the creation of the Scott-encoded datatype type. See Note [Scott encoding of datatypes]
convDataCons :: forall m. Converting m => GHC.TyCon -> [GHC.DataCon] -> m PCType
convDataCons tc dcs =
    -- \tv_1 .. tv_k . body
    flip (foldr (\tv acc -> mkTyLam tv acc)) (GHC.tyConTyVars tc) $ do
        resultType <- safeFreshTyName $ (GHC.getOccString $ GHC.tyConName tc) ++ "_matchOut"
        cases <- mapM (dataConCaseType (PC.TyVar () resultType)) dcs
        pure $ mkScottTyBody resultType cases

mkScottTyBody :: PC.TyName () -> [PCType] -> PCType
mkScottTyBody resultTypeName cases = let
        -- we can only match into kind Type
        resultKind = PC.Type ()
        -- See Note [Iterated abstraction and application]
        -- case_1 -> ... -> case_n -> resultType
        funcs = foldr (\t acc -> PC.TyFun () t acc) (PC.TyVar () resultTypeName) cases
        -- forall resultType . funcs
        resultAbstracted = PC.TyForall () resultTypeName resultKind funcs
    in
        resultAbstracted

dataConCaseType :: Converting m => PCType -> GHC.DataCon -> m PCType
dataConCaseType resultType dc = if not (GHC.isVanillaDataCon dc) then unsupported $ "Non-vanilla data constructor:" GHC.<+> GHC.ppr dc else
    do
        let argTys = GHC.dataConRepArgTys dc
        args <- mapM convType argTys
        -- See Note [Iterated abstraction and application]
        -- t_1 -> ... -> t_m -> resultType
        pure $ foldr (\t acc -> PC.TyFun () t acc) resultType args

-- This is the creation of the Scott-encoded constructor value.
convConstructor :: Converting m => GHC.DataCon -> m PCExpr
convConstructor dc = let
        tc = GHC.dataConTyCon dc
        tcName = GHC.getOccString $ GHC.tyConName tc
        dcName = GHC.getOccString $ GHC.dataConName dc
    in
        -- /\ tv_1 .. tv_n . body
        flip (foldr (\tv acc -> mkTyAbs tv acc)) (GHC.tyConTyVars tc) $ do
            -- See Note [Scott encoding of datatypes]
            resultType <- safeFreshTyName $ tcName ++ "_matchOut"
            dcs <- getDataCons tc
            index <- case elemIndex dc dcs of
                Just i  -> pure i
                Nothing -> conversionFail "Data constructor not in the type constructor's list of constructors!"
            caseTypes <- mapM (dataConCaseType (PC.TyVar () resultType)) dcs
            caseArgNames <- mapM (convNameFresh . GHC.dataConName) dcs
            argTypes <- mapM convType $ GHC.dataConRepArgTys dc
            argNames <- forM [0..(length argTypes -1)] (\i -> safeFreshName $ dcName ++ "_arg" ++ show i)
            pure $ mkScottConstructorBody resultType (zip caseArgNames caseTypes) (zip argNames argTypes) index

mkScottConstructorBody :: PC.TyName () -> [(PC.Name (), PCType)] -> [(PC.Name (), PCType)] -> Int -> PCExpr
mkScottConstructorBody resultTypeName caseNamesAndTypes argNamesAndTypes index = let
        -- data types are always in kind Type
        resultKind = PC.Type ()
        thisConstructor = fst $ caseNamesAndTypes !! index
        -- See Note [Iterated abstraction and application]
        -- c_i a_1 .. a_m
        applied = foldl' (\acc a -> PC.Apply () acc (PC.Var () a)) (PC.Var () thisConstructor) (fmap fst argNamesAndTypes)
        -- \c_1 .. c_n . applied
        cfuncs = foldr (\(name, t) acc -> PC.LamAbs () name t acc) applied caseNamesAndTypes
        -- forall r . cfuncs
        resAbstracted = PC.TyAbs () resultTypeName resultKind cfuncs
        -- \a_1 .. a_m . abstracted
        afuncs = foldr (\(name, t) acc -> PC.LamAbs () name t acc) resAbstracted argNamesAndTypes
    in
        afuncs

convAlt :: Converting m => GHC.CoreAlt -> m PCExpr
convAlt (alt, vars, body) = case alt of
    GHC.LitAlt _  -> unsupported "Literal case"
    GHC.DEFAULT   -> do
        caseBody <- convExpr body
        delay caseBody
    -- We just package it up as a lambda bringing all the
    -- vars into scope whose body is the body of the case alternative.
    -- See Note [Iterated abstraction and application]
    -- See Note [Case expressions and laziness]
    GHC.DataAlt _ -> foldr (\v acc -> mkLambda v acc) (convExpr body >>= delay) vars

-- Literals and primitives

{- Note [Literals]
GHC's literals and primitives are a bit of a pain, since they not only have a Literal
containing the actual data, but are wrapped in special functions (often ending in the magic #).

This is a pain to recognize.
-}

convLiteral :: Converting m => GHC.Literal -> m (PC.Constant ())
convLiteral l = case l of
    -- TODO: better sizes
    GHC.MachInt64 i    -> pure $ PC.BuiltinInt () haskellIntSize i
    GHC.MachInt i      -> pure $ PC.BuiltinInt () haskellIntSize i
    GHC.MachStr bs     -> pure $ PC.BuiltinBS () haskellBSSize (BSL.fromStrict bs)
    GHC.LitInteger _ _ -> unsupported "Literal (unbounded) integer"
    GHC.MachWord _     -> unsupported "Literal word"
    GHC.MachWord64 _   -> unsupported "Literal word64"
    GHC.MachChar _     -> unsupported "Literal char"
    GHC.MachFloat _    -> unsupported "Literal float"
    GHC.MachDouble _   -> unsupported "Literal double"
    GHC.MachLabel {}   -> unsupported "Literal label"
    GHC.MachNullAddr   -> unsupported "Literal null"

isPrimitiveWrapper :: GHC.Id -> Bool
isPrimitiveWrapper i = case GHC.idDetails i of
    GHC.DataConWorkId dc -> isPrimitiveDataCon dc
    GHC.VanillaId        -> GHC.varName i == GHC.unpackCStringName
    _                    -> False

isPrimitiveDataCon :: GHC.DataCon -> Bool
isPrimitiveDataCon dc = dc == GHC.intDataCon

-- These never seem to come up, rather we get the typeclass operations. Not sure if we need them.
convPrimitiveOp :: (Converting m) => GHC.PrimOp -> m PCExpr
convPrimitiveOp po = do
    name <- case po of
        GHC.IntAddOp  -> pure PC.AddInteger
        GHC.IntSubOp  -> pure PC.SubtractInteger
        GHC.IntMulOp  -> pure PC.MultiplyInteger
        -- check this one
        GHC.IntQuotOp -> pure PC.DivideInteger
        GHC.IntRemOp  -> pure PC.RemainderInteger
        GHC.IntGtOp   -> pure PC.GreaterThanInteger
        GHC.IntGeOp   -> pure PC.GreaterThanEqInteger
        GHC.IntLtOp   -> pure PC.LessThanInteger
        GHC.IntLeOp   -> pure PC.LessThanEqInteger
        GHC.IntEqOp   -> pure PC.EqInteger
        _             -> unsupported $ "Primitive operation:" GHC.<+> GHC.ppr po
    pure $ PC.TyInst () (PC.Constant () $ PC.BuiltinName () name) (PC.TyInt () haskellIntSize)

-- Typeclasses

convEqMethod :: (Converting m) => GHC.Name -> m PCExpr
convEqMethod name = do
    m <- method name
    pure $ PC.TyInst () m (PC.TyInt () haskellIntSize)
        where
            method n
              | n == GHC.eqName = pure $ PC.Constant () $ PC.BuiltinName () PC.EqInteger
              | otherwise = unsupported $ "Eq method:" GHC.<+> GHC.ppr n

convOrdMethod :: (Converting m) => GHC.Name -> m PCExpr
convOrdMethod name = do
    m <- method name
    pure $ PC.TyInst () m (PC.TyInt () haskellIntSize)
        where
            method n
                -- only this one has a name defined in the lib??
                | n == GHC.geName = pure $ PC.Constant () $ PC.BuiltinName () PC.GreaterThanEqInteger
                | GHC.getOccString n == ">" = pure $ PC.Constant () $ PC.BuiltinName () PC.GreaterThanInteger
                | GHC.getOccString n == "<=" = pure $ PC.Constant () $ PC.BuiltinName () PC.LessThanEqInteger
                | GHC.getOccString n == "<" = pure $ PC.Constant () $ PC.BuiltinName () PC.LessThanInteger
                | otherwise = unsupported $ "Ord method:" GHC.<+> GHC.ppr n

convNumMethod :: (Converting m) => GHC.Name -> m PCExpr
convNumMethod name = do
    m <- method name
    pure $ PC.TyInst () m (PC.TyInt () haskellIntSize)
        where
            method n
                -- only this one has a name defined in the lib??
                | n == GHC.minusName = pure $ PC.Constant () $ PC.BuiltinName () PC.SubtractInteger
                | GHC.getOccString n == "+" = pure $ PC.Constant () $ PC.BuiltinName () PC.AddInteger
                | GHC.getOccString n == "*" = pure $ PC.Constant () $ PC.BuiltinName () PC.MultiplyInteger
                | otherwise = unsupported $ "Num method:" GHC.<+> GHC.ppr n

-- Binder helpers

-- | Builds a lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkLambda :: Converting m => GHC.Var -> m PCExpr -> m PCExpr
mkLambda v body = do
    let ghcName = GHC.varName v
    (t', n') <- convVarFresh v
    body' <- local (first $ pushName ghcName n') body
    pure $ PC.LamAbs () n' t' body'

-- | Builds a type abstraction, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyAbs :: Converting m => GHC.Var -> m PCExpr -> m PCExpr
mkTyAbs v body = do
    let ghcName = GHC.tyVarName v
    (k', t') <- convTyVarFresh v
    body' <- local (first $ pushTyName ghcName t') body
    pure $ PC.TyAbs () t' k' body'

-- | Builds a forall, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyForall :: Converting m => GHC.Var -> m PCType -> m PCType
mkTyForall v body = do
    let ghcName = GHC.tyVarName v
    (k', t') <- convTyVarFresh v
    body' <- local (first $ pushTyName ghcName t') body
    pure $ PC.TyForall () t' k' body'

-- | Builds a type lambda, binding the given variable to a name that
-- will be in scope when running the second argument.
mkTyLam :: Converting m => GHC.Var -> m PCType -> m PCType
mkTyLam v body = do
    let ghcName = GHC.tyVarName v
    (k', t') <- convTyVarFresh v
    body' <- local (first $ pushTyName ghcName t') body
    pure $ PC.TyLam () t' k' body'

-- Simulating laziness
-- TODO: These could all be actual language values rather than metalanguage things, perhaps that would be neater?
-- the downside would be that without simplification it would make the generated terms more complex

delay :: MonadQuote m => PCExpr -> m PCExpr
delay body = PC.LamAbs () <$> safeFreshName "thunk" <*> liftQuote Unit.getBuiltinUnit <*> pure body

delayType :: MonadQuote m => PCType -> m PCType
delayType orig = PC.TyFun () <$> liftQuote Unit.getBuiltinUnit <*> pure orig

force :: MonadQuote m => PCExpr -> m PCExpr
force thunk = PC.Apply () thunk <$> liftQuote Unit.getBuiltinUnitval

-- See Note [Recursion with Z]
delayFunction :: MonadQuote m => PCType -> PCExpr -> m PCExpr
delayFunction ty f = do
    n <- safeFreshName "arg"
    forcedUse <- force $ PC.Var () n
    dType <- delayType ty
    pure $ PC.LamAbs () n dType $ PC.Apply () f forcedUse

-- Tuples

mkTupleType :: MonadQuote m => [PCType] -> m PCType
mkTupleType tys = do
    resultType <- safeFreshTyName "tuple_matchOut"
    let cases = [foldr (\v acc -> PC.TyFun () v acc) (PC.TyVar () resultType) tys]
    pure $ mkScottTyBody resultType cases

mkTupleConstructor :: MonadQuote m => [PCType] -> m PCExpr
mkTupleConstructor argTys = do
    resultType <- safeFreshTyName "tuple_matchOut"
    caseName <- safeFreshName "c"
    let caseNamesAndTypes = [(caseName, foldr (\v acc -> PC.TyFun () v acc) (PC.TyVar () resultType) argTys)]
    argNames <- forM [0..(length argTys -1)] (\i -> safeFreshName $ "tuple_arg" ++ show i)
    pure $ mkScottConstructorBody resultType caseNamesAndTypes (zip argNames argTys) 0

-- Functions

{- Note [Recursion with Z]
How do we handle fixpoints of functions `a -> a` when we only have the Z combinator?

We translate the value as a function `() -> a` instead, and force it immediately in the
body. This way the semantics are still strict.

Translating `f :: a -> a` to a function `(() -> a) -> () -> a)` is easy, you just do
`delay . f . force`.
-}

-- | A fixpoint combinator on functions of type @a -> a@.
fixY :: MonadQuote m => PCType -> PCExpr -> m PCExpr
fixY ty f = do
    unitTy <- liftQuote Unit.getBuiltinUnit
    z <- liftQuote Function.getBuiltinFix
    let instantiated = PC.TyInst () (PC.TyInst () z unitTy) ty
    -- See Note [Recursion with Z]
    zFunction <- delayFunction ty f
    pure $ PC.Apply () instantiated zFunction


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

-- The main function

convExpr :: Converting m => GHC.CoreExpr -> m PCExpr
convExpr e = do
    -- See Note [Scopes]
    (stack, _) <- ask
    let top = NE.head stack
    case e of
        -- See Note [Literals]
        GHC.App (GHC.Var (isPrimitiveWrapper -> True)) arg -> convExpr arg
        -- special typeclass method calls
        GHC.App (GHC.App
                 -- eq class method
                 (GHC.Var n@(GHC.idDetails -> GHC.ClassOpId ((==) GHC.eqClassName . GHC.className -> True)))
                 -- we only support applying to int
                 (GHC.Type (GHC.eqType GHC.intTy -> True)))
            -- last arg is typeclass dictionary
            _ -> convEqMethod (GHC.varName n)
        GHC.App (GHC.App
                 -- ord class method
                 (GHC.Var n@(GHC.idDetails -> GHC.ClassOpId ((==) GHC.ordClassName . GHC.className -> True)))
                 -- we only support applying to int
                 (GHC.Type (GHC.eqType GHC.intTy -> True)))
            -- last arg is typeclass dictionary
            _ -> convOrdMethod (GHC.varName n)
        GHC.App (GHC.App
                 -- num class method
                 (GHC.Var n@(GHC.idDetails -> GHC.ClassOpId ((==) GHC.numClassName . GHC.className -> True)))
                 -- we only support applying to int
                 (GHC.Type (GHC.eqType GHC.intTy -> True)))
            -- last arg is typeclass dictionary
            _ -> convNumMethod (GHC.varName n)
        -- locally bound vars
        GHC.Var (lookupName top . GHC.varName -> Just name) -> pure $ PC.Var () name
        -- Special kinds of id
        GHC.Var (GHC.idDetails -> GHC.PrimOpId po) -> convPrimitiveOp po
        GHC.Var (GHC.idDetails -> GHC.DataConWorkId dc) -> convConstructor dc
        -- the term we get must be closed - we don't resolve most references
        -- TODO: possibly relax this?
        GHC.Var n@(GHC.idDetails -> GHC.VanillaId) -> freeVariable $ "Variable:" GHC.<+> GHC.ppr n GHC.$+$ (GHC.ppr $ GHC.idDetails n)
        GHC.Var n -> unsupported $ "Variable" GHC.<+> GHC.ppr n GHC.$+$ (GHC.ppr $ GHC.idDetails n)
        GHC.Lit lit -> PC.Constant () <$> convLiteral lit
        -- arg can be a type here, in which case it's a type instantiation
        GHC.App l (GHC.Type t) -> PC.TyInst () <$> convExpr l <*> convType t
        -- otherwise it's a normal application
        GHC.App l arg -> PC.Apply () <$> convExpr l <*> convExpr arg
        -- if we're biding a type variable it's a type abstraction
        GHC.Lam b@(GHC.isTyVar -> True) body -> mkTyAbs b $ convExpr body
        -- othewise it's a normal lambda
        GHC.Lam b body -> mkLambda b $ convExpr body
        GHC.Let (GHC.NonRec b arg) body -> do
            -- convert it as a lambda
            a' <- convExpr arg
            l' <- mkLambda b $ convExpr body
            pure $ PC.Apply () l' a'
        GHC.Let (GHC.Rec bs) body -> do
            tys <- mapM convType (fmap (GHC.varType . fst) bs)
            tupleTy <- mkTupleType tys

            bsLam <- flip (foldr (\b acc -> mkLambda b acc)) (fmap fst bs) $ do
                rhss <- mapM convExpr (fmap snd bs)
                tupleConstructor <- mkTupleConstructor tys
                let tuple = foldl' (\acc rhs -> PC.Apply () acc rhs) tupleConstructor rhss
                pure tuple

            tupleArg <- safeFreshName "tuple"
            let tupleFun = PC.LamAbs () tupleArg tupleTy $ PC.Apply () (PC.Var () tupleArg) bsLam
            fixed <- fixY tupleTy tupleFun

            bodyLam <- foldr (\b acc -> mkLambda b acc) (convExpr body) (fmap fst bs)
            pure $ PC.Apply () bodyLam fixed
        GHC.Case scrutinee b t alts -> do
            let scrutineeType = GHC.varType b
            -- must be a TC app
            tc <- case GHC.splitTyConApp_maybe scrutineeType of
                Just (tc, _) -> pure tc
                Nothing      -> conversionFail "Scrutinee's type was not a type constructor application"
            dcs <- getDataCons tc
            -- See Note [Scott encoding of datatypes]
            -- we're going to delay the body, so the scrutinee needs to be instantiated the delayed type
            instantiated <- PC.TyInst () <$> convExpr scrutinee <*> (delayType =<< convType t)
            branches <- forM dcs $ \dc -> case GHC.findAlt (GHC.DataAlt dc) alts of
                Just alt -> do
                    alt' <- convAlt alt
                    if GHC.isDefaultAlt alt then do
                        -- need to consume the args
                        argTypes <- mapM convType $ GHC.dataConRepArgTys dc
                        argNames <- forM [0..(length argTypes -1)] (\i -> safeFreshName $ "default_arg" ++ show i)
                        -- See Note [Iterated abstraction and application]
                        pure $ foldr (\(n', t') acc -> PC.LamAbs () n' t' acc) alt' (zip argNames argTypes)
                    else
                        pure alt'
                Nothing -> conversionFail "No case matched and no default case"
            -- See Note [Iterated abstraction and application]
            -- See Note [Case expressions and laziness]
            force $ foldl' (\acc alt -> PC.Apply () acc alt) instantiated branches
        -- ignore annotation
        GHC.Tick _ body -> convExpr body
        -- just go straight to the body, we don't care about the nominal types
        GHC.Cast body _ -> convExpr body
        GHC.Type _ -> conversionFail "Cannot convert types directly, only as arguments to applications"
        GHC.Coercion _ -> conversionFail "Coercions should not be converted"
