-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

module PlutusTx.IsData.TH
  ( unsafeFromDataClause
  , unstableMakeIsData
  , makeIsDataIndexed
  , makeIsDataAsList
  , mkConstrCreateExpr
  , mkUnsafeConstrMatchPattern
  , mkConstrPartsMatchPattern
  , mkUnsafeConstrPartsMatchPattern
  , AsDataProdType (..)
  , fromDataClause
  ) where

import Data.Foldable as Foldable (foldl')
import Data.Functor ((<&>))
import Data.List qualified as Li
import Data.Traversable (for)

import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH

import PlutusTx.AsData.Internal (wrapUnsafeDataAsConstr, wrapUnsafeUncons)
import PlutusTx.Builtins as Builtins
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Eq qualified as PlutusTx
import PlutusTx.ErrorCodes (reconstructCaseError)
import PlutusTx.IsData.Class (FromData (..), ToData (..), UnsafeFromData (..))
import PlutusTx.Trace (traceError)

import Prelude

mkListCreateExpr :: [TH.Name] -> TH.ExpQ
mkListCreateExpr createFieldNames =
  foldr
    (\v e -> [|BI.mkCons (toBuiltinData $(TH.varE v)) $e|])
    [|BI.mkNilData BI.unitval|]
    createFieldNames

mkConstrCreateExpr :: Integer -> [TH.Name] -> TH.ExpQ
mkConstrCreateExpr conIx createFieldNames =
  [|BI.mkConstr (conIx :: Integer) $(mkListCreateExpr createFieldNames)|]

mkConstrPartsMatchPattern :: Integer -> [TH.Name] -> TH.PatQ
mkConstrPartsMatchPattern conIx extractFieldNames =
  let
    -- Do not change this to raw integer pattern matching.
    -- GHC may inline `integerEq` and do integer equality by matching
    -- them structurally, which the plugin does not know how to handle.
    -- (==) i -> True
    ixMatchPat = [p|((PlutusTx.==) (conIx :: Integer) -> True)|]
    -- [unsafeFromBuiltinData -> arg1, ...]
    extractArgPats =
      extractFieldNames <&> \n ->
        [p|(fromBuiltinData -> Just $(TH.varP n))|]
    extractArgsPat = go extractArgPats
      where
        go [] = [p|_|]
        go [x] = [p|(Builtins.headMaybe -> Just $x)|]
        go (x : xs) = [p|(Builtins.uncons -> Just ($x, $(go xs)))|]
    pat = [p|($ixMatchPat, $extractArgsPat)|]
   in
    pat

mkListPartsMatchPattern :: [TH.Name] -> TH.PatQ
mkListPartsMatchPattern extractFieldNames =
  let
    -- [unsafeFromBuiltinData -> arg1, ...]
    extractArgPats =
      extractFieldNames <&> \n ->
        [p|(fromBuiltinData -> Just $(TH.varP n))|]
    go [] = [p|_|]
    go [x] = [p|(Builtins.headMaybe -> Just $x)|]
    go (x : xs) = [p|(Builtins.uncons -> Just ($x, $(go xs)))|]
   in
    [p|$(go extractArgPats)|]

{-| If generating pattern synonyms for a product type declared with 'asData',
we can avoid the index match, as we know that the type only has one constructor. -}
data AsDataProdType
  = IsAsDataProdType
  | IsNotAsDataProdType

-- TODO: safe match for the whole thing? not needed atm

mkUnsafeConstrMatchPattern
  :: AsDataProdType
  -> Integer
  -> [TH.Name]
  -> TH.PatQ
mkUnsafeConstrMatchPattern isProduct conIx extractFieldNames =
  case isProduct of
    IsAsDataProdType ->
      [p|
        ( wrapUnsafeDataAsConstr ->
            ( BI.snd ->
                $(mkUnsafeConstrPartsMatchPattern isProduct conIx extractFieldNames)
              )
          )
        |]
    IsNotAsDataProdType ->
      [p|
        ( wrapUnsafeDataAsConstr ->
            ( Builtins.pairToPair ->
                $(mkUnsafeConstrPartsMatchPattern isProduct conIx extractFieldNames)
              )
          )
        |]

mkUnsafeConstrPartsMatchPattern
  :: AsDataProdType
  -> Integer
  -> [TH.Name]
  -> TH.PatQ
mkUnsafeConstrPartsMatchPattern isProduct conIx extractFieldNames =
  let
    -- (==) i -> True
    ixMatchPat = [p|((PlutusTx.==) (conIx :: Integer) -> True)|]
    -- [unsafeFromBuiltinData -> arg1, ...]
    extractArgPats =
      extractFieldNames <&> \n ->
        [p|(unsafeFromBuiltinData -> $(TH.varP n))|]
    extractArgsPat = go extractArgPats
      where
        go [] = [p|_|]
        go [x] = [p|(BI.head -> $x)|]
        go (x : xs) = [p|(wrapUnsafeUncons -> ($x, $(go xs)))|]
    pat =
      -- We can safely omit the index match if we know that the type is a product type
      case isProduct of
        IsAsDataProdType -> [p|$extractArgsPat|]
        IsNotAsDataProdType -> [p|($ixMatchPat, $extractArgsPat)|]
   in
    pat

toDataClause :: (TH.ConstructorInfo, Int) -> TH.Q TH.Clause
toDataClause (TH.ConstructorInfo {TH.constructorName = name, TH.constructorFields = argTys}, index) = do
  argNames <- for argTys $ \_ -> TH.newName "arg"
  let create = mkConstrCreateExpr (fromIntegral index) argNames
  TH.clause [TH.conP name (fmap TH.varP argNames)] (TH.normalB create) []

toDataListClause :: TH.ConstructorInfo -> TH.Q TH.Clause
toDataListClause TH.ConstructorInfo {TH.constructorName = name, TH.constructorFields = argTys} = do
  argNames <- for argTys $ \_ -> TH.newName "arg"
  let create = [|BI.mkList $(mkListCreateExpr argNames)|]
  TH.clause [TH.conP name (fmap TH.varP argNames)] (TH.normalB create) []

toDataClauses :: [(TH.ConstructorInfo, Int)] -> [TH.Q TH.Clause]
toDataClauses indexedCons = toDataClause <$> indexedCons

reconstructCase :: (TH.ConstructorInfo, Int) -> TH.MatchQ
reconstructCase (TH.ConstructorInfo {TH.constructorName = name, TH.constructorFields = argTys}, index) = do
  argNames <- for argTys $ \_ -> TH.newName "arg"

  -- Build the constructor application, assuming that all the arguments are in scope
  let app = Foldable.foldl' (\h v -> [|$h $(TH.varE v)|]) (TH.conE name) argNames

  TH.match (mkConstrPartsMatchPattern (fromIntegral index) argNames) (TH.normalB [|Just $app|]) []

fromDataClause :: [(TH.ConstructorInfo, Int)] -> TH.Q TH.Clause
fromDataClause indexedCons = do
  dName <- TH.newName "d"
  indexName <- TH.newName "index"
  argsName <- TH.newName "args"
  -- Call the clause for each constructor, falling through to the next one, until we get to the end in which case we call 'error'
  let
    conCases :: [TH.MatchQ]
    conCases = (fmap (\ixCon -> reconstructCase ixCon) indexedCons)
    finalCase :: TH.MatchQ
    finalCase = TH.match TH.wildP (TH.normalB [|Nothing|]) []
    cases = conCases ++ [finalCase]
    kase :: TH.ExpQ
    kase = TH.caseE [|($(TH.varE indexName), $(TH.varE argsName))|] cases
  let body =
        [|
          -- See Note [Bang patterns in TH quotes]
          let constrFun $(TH.bangP $ TH.varP indexName) $(TH.bangP $ TH.varP argsName) = $kase
           in matchData'
                $(TH.varE dName)
                constrFun
                (const Nothing)
                (const Nothing)
                (const Nothing)
                (const Nothing)
                (const Nothing)
          |]
  TH.clause [TH.varP dName] (TH.normalB body) []

fromDataListClause :: TH.ConstructorInfo -> TH.Q TH.Clause
fromDataListClause TH.ConstructorInfo {TH.constructorName = consName, TH.constructorFields = argTys} = do
  dName <- TH.newName "d"
  argsName <- TH.newName "args"
  -- Call the clause for each constructor, falling through to the next one, until we get to the end in which case we call 'error'
  let
    singleCase :: TH.MatchQ
    singleCase = do
      constructorArgs <- for argTys $ \_ -> TH.newName "consArg"
      let app = Foldable.foldl' (\h v -> [|$h $(TH.varE v)|]) (TH.conE consName) constructorArgs
      TH.match (mkListPartsMatchPattern constructorArgs) (TH.normalB [|Just $app|]) []
    finalCase :: TH.MatchQ
    finalCase = TH.match TH.wildP (TH.normalB [|Nothing|]) []
    cases = [singleCase, finalCase]
    kase :: TH.ExpQ
    kase = TH.caseE [|$(TH.varE argsName)|] cases
  let body =
        [|
          -- See Note [Bang patterns in TH quotes]
          let constrFun $(TH.bangP $ TH.varP argsName) = $kase
           in matchData'
                $(TH.varE dName)
                (const $ const Nothing)
                (const Nothing)
                constrFun
                (const Nothing)
                (const Nothing)
                (const Nothing)
          |]
  TH.clause [TH.varP dName] (TH.normalB body) []

unsafeReconstructCase :: (TH.ConstructorInfo, Int) -> TH.MatchQ
unsafeReconstructCase (TH.ConstructorInfo {TH.constructorName = name, TH.constructorFields = argTys}, index) = do
  argNames <- for argTys $ \_ -> TH.newName "arg"

  -- Build the constructor application, assuming that all the arguments are in scope
  let app = foldl' (\h v -> [|$h $(TH.varE v)|]) (TH.conE name) argNames

  TH.match
    (mkUnsafeConstrPartsMatchPattern IsNotAsDataProdType (fromIntegral index) argNames)
    (TH.normalB app)
    []

unsafeReconstructListCase :: TH.ConstructorInfo -> TH.MatchQ
unsafeReconstructListCase TH.ConstructorInfo {TH.constructorName = name, TH.constructorFields = argTys} = do
  argNames <- for argTys $ \_ -> TH.newName "arg"

  -- Build the constructor application, assuming that all the arguments are in scope
  let app = foldl' (\h v -> [|$h $(TH.varE v)|]) (TH.conE name) argNames

  TH.match
    (mkUnsafeConstrPartsMatchPattern IsAsDataProdType (-1) argNames)
    (TH.normalB app)
    []

unsafeFromDataClause :: [(TH.ConstructorInfo, Int)] -> TH.Q TH.Clause
unsafeFromDataClause indexedCons = do
  dName <- TH.newName "d"
  tupName <- TH.newName "tup"
  indexName <- TH.newName "index"
  argsName <- TH.newName "args"
  -- Call the clause for each constructor, falling through to the next one, until we get to the end in which case we call 'error'
  let
    finalCase :: TH.MatchQ
    finalCase = TH.match TH.wildP (TH.normalB [|traceError reconstructCaseError|]) []

    indexedConsSorted =
      Li.sortBy (\(_, x) (_, y) -> compare x y) indexedCons

    intCasingEligible =
      let idxs = snd <$> indexedConsSorted
       in [0 .. (length idxs - 1)] == idxs

  if intCasingEligible
    then do
      let
        kases =
          TH.listE $
            (\(conInfo, _) -> TH.lamCaseE [unsafeReconstructListCase conInfo, finalCase])
              <$> indexedConsSorted
        body =
          [|
            BI.casePair (BI.unsafeDataAsConstr $(TH.varE dName)) $
              \($(TH.varP indexName)) ($(TH.varP argsName)) ->
                (caseInteger $(TH.varE indexName) $kases) $(TH.varE argsName)
            |]

      TH.clause [TH.varP dName] (TH.normalB body) []
    else do
      let
        conCases :: [TH.MatchQ]
        conCases = (fmap (\ixCon -> unsafeReconstructCase ixCon) indexedCons)
        cases = conCases ++ [finalCase]
        kase :: TH.ExpQ
        kase = TH.caseE [|($(TH.varE indexName), $(TH.varE argsName))|] cases
      let body =
            [|
              -- See Note [Bang patterns in TH quotes]
              let $(TH.bangP $ TH.varP tupName) = BI.unsafeDataAsConstr $(TH.varE dName)
                  $(TH.bangP $ TH.varP indexName) = BI.fst $(TH.varE tupName)
                  $(TH.bangP $ TH.varP argsName) = BI.snd $(TH.varE tupName)
               in $kase
              |]
      TH.clause [TH.varP dName] (TH.normalB body) []

unsafeFromDataListClause :: TH.ConstructorInfo -> TH.Q TH.Clause
unsafeFromDataListClause cons = do
  dName <- TH.newName "d"
  argsName <- TH.newName "args"
  -- Call the clause for each constructor, falling through to the next one, until we get to the end in which case we call 'error'
  let
    finalCase :: TH.MatchQ
    finalCase = TH.match TH.wildP (TH.normalB [|traceError reconstructCaseError|]) []
    cases = [unsafeReconstructListCase cons, finalCase]
    kase :: TH.ExpQ
    kase = TH.caseE [|$(TH.varE argsName)|] cases
  let body =
        [|
          -- See Note [Bang patterns in TH quotes]
          let $(TH.bangP $ TH.varP argsName) = BI.unsafeDataAsList $(TH.varE dName)
           in $kase
          |]
  TH.clause [TH.varP dName] (TH.normalB body) []

defaultIndex :: TH.Name -> TH.Q [(TH.Name, Int)]
defaultIndex name = do
  info <- TH.reifyDatatype name
  pure $ zip (TH.constructorName <$> TH.datatypeCons info) [0 ..]

{-| Generate a 'FromData' and a 'ToData' instance for a type.
This may not be stable in the face of constructor additions,
renamings, etc. Use 'makeIsDataIndexed' if you need stability. -}
unstableMakeIsData :: TH.Name -> TH.Q [TH.Dec]
unstableMakeIsData name = makeIsDataIndexed name =<< defaultIndex name

{-| Generate a 'ToData', 'FromData and a 'UnsafeFromData' instances for a type,
using an explicit mapping of constructor names to indices.
Use this for types where you need to keep the representation stable. -}
makeIsDataIndexed :: TH.Name -> [(TH.Name, Int)] -> TH.Q [TH.Dec]
makeIsDataIndexed dataTypeName indices = do
  dataTypeInfo <- TH.reifyDatatype dataTypeName
  let appliedType = TH.datatypeType dataTypeInfo
  let nonOverlapInstance = TH.InstanceD Nothing

  indexedCons <- for (TH.datatypeCons dataTypeInfo) $ \ctorInfo ->
    case lookup (TH.constructorName ctorInfo) indices of
      Just i -> pure (ctorInfo, i)
      Nothing -> fail $ "No index given for constructor" ++ show (TH.constructorName ctorInfo)

  toDataInst <- do
    let constraints =
          TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
            TH.classPred ''ToData [TH.VarT (tyvarbndrName tyVarBinder)]
    toDataDecl <- TH.funD 'toBuiltinData (toDataClauses indexedCons)
    toDataPrag <- TH.pragInlD 'toBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
    pure $
      nonOverlapInstance
        constraints
        (TH.classPred ''ToData [appliedType])
        [toDataPrag, toDataDecl]

  fromDataInst <- do
    let constraints =
          TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
            TH.classPred ''FromData [TH.VarT (tyvarbndrName tyVarBinder)]
    fromDataDecl <- TH.funD 'fromBuiltinData [fromDataClause indexedCons]
    fromDataPrag <- TH.pragInlD 'fromBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
    pure $
      nonOverlapInstance
        constraints
        (TH.classPred ''FromData [appliedType])
        [fromDataPrag, fromDataDecl]

  unsafeFromDataInst <- do
    let constraints =
          TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
            TH.classPred ''UnsafeFromData [TH.VarT (tyvarbndrName tyVarBinder)]
    unsafeFromDataDecl <- TH.funD 'unsafeFromBuiltinData [unsafeFromDataClause indexedCons]
    unsafeFromDataPrag <- TH.pragInlD 'unsafeFromBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
    pure $
      nonOverlapInstance
        constraints
        (TH.classPred ''UnsafeFromData [appliedType])
        [unsafeFromDataPrag, unsafeFromDataDecl]

  pure [toDataInst, fromDataInst, unsafeFromDataInst]
  where
#if MIN_VERSION_template_haskell(2,17,0)
      tyvarbndrName (TH.PlainTV n _)    = n
      tyvarbndrName (TH.KindedTV n _ _) = n
#else
      tyvarbndrName (TH.PlainTV n)      = n
      tyvarbndrName (TH.KindedTV n _)   = n
#endif

{-| Generates `FromData` and `ToData` instances for a type.
Requires the type to have exactly one constructor,
since instances created by `deriveIsDataAsList` use a list encoding
instead of `Constr` and thus cannot represent constructor indices. -}
makeIsDataAsList :: TH.Name -> TH.Q [TH.Dec]
makeIsDataAsList dataTypeName = do
  dataTypeInfo <- TH.reifyDatatype dataTypeName
  let appliedType = TH.datatypeType dataTypeInfo
  let nonOverlapInstance = TH.InstanceD Nothing

  cons <-
    case TH.datatypeCons dataTypeInfo of
      [cons] -> pure cons
      _ -> fail "Only data types with single constructor are eligible for 'makeIsDataAsList'"

  toDataInst <- do
    let constraints =
          TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
            TH.classPred ''ToData [TH.VarT (tyvarbndrName tyVarBinder)]
    toDataDecl <- TH.funD 'toBuiltinData [toDataListClause cons]
    toDataPrag <- TH.pragInlD 'toBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
    pure $
      nonOverlapInstance
        constraints
        (TH.classPred ''ToData [appliedType])
        [toDataPrag, toDataDecl]

  fromDataInst <- do
    let constraints =
          TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
            TH.classPred ''FromData [TH.VarT (tyvarbndrName tyVarBinder)]
    fromDataDecl <- TH.funD 'fromBuiltinData [fromDataListClause cons]
    fromDataPrag <- TH.pragInlD 'fromBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
    pure $
      nonOverlapInstance
        constraints
        (TH.classPred ''FromData [appliedType])
        [fromDataPrag, fromDataDecl]

  unsafeFromDataInst <- do
    let constraints =
          TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
            TH.classPred ''UnsafeFromData [TH.VarT (tyvarbndrName tyVarBinder)]
    unsafeFromDataDecl <- TH.funD 'unsafeFromBuiltinData [unsafeFromDataListClause cons]
    unsafeFromDataPrag <- TH.pragInlD 'unsafeFromBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
    pure $
      nonOverlapInstance
        constraints
        (TH.classPred ''UnsafeFromData [appliedType])
        [unsafeFromDataPrag, unsafeFromDataDecl]

  pure [toDataInst, fromDataInst, unsafeFromDataInst]
  where
#if MIN_VERSION_template_haskell(2,17,0)
      tyvarbndrName (TH.PlainTV n _)    = n
      tyvarbndrName (TH.KindedTV n _ _) = n
#else
      tyvarbndrName (TH.PlainTV n)      = n
      tyvarbndrName (TH.KindedTV n _)   = n
#endif

{- Note [indexMatchCase and fallthrough]
`indexMatchCase` and `fallthrough` need to be non-strict, because (1) at most one of them
needs to be evaluated; (2) evaluating `indexMatchCase` when it shouldn't be evaluated
can lead to `BI.head []` (e.g., in the `UnsafeFromData (Maybe a)` instance); (3) evaluating
`fallthrough` when it shouldn't be evaluated can lead to PT1 (reconstructCaseError).
-}

{- Note [Bang patterns in TH quotes]
Bang patterns in TH quotes do not work before GHC 9.8.1. See
https://gitlab.haskell.org/ghc/ghc/-/issues/23036.

For the time being, we need to use `TH.bangP`.
-}
