-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
module PlutusTx.IsData.TH (
  unstableMakeIsData,
  makeIsDataIndexed,
  mkConstrCreateExpr,
  mkUnsafeConstrMatchPattern,
  mkDecodingFunction,
  mkConstrPartsMatchPattern,
  mkUnsafeConstrPartsMatchPattern,
) where

import Data.Foldable as Foldable (foldl')
import Data.Functor ((<&>))
import Data.Traversable (for)

import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH

import PlutusTx.Builtins as Builtins
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Eq qualified as PlutusTx
import PlutusTx.ErrorCodes (reconstructCaseError)
import PlutusTx.IsData.Class (FromData (..), ToData (..), UnsafeFromData (..))
import PlutusTx.Trace (traceError)

import Prelude

mkConstrCreateExpr :: Integer -> [TH.Name] -> TH.ExpQ
mkConstrCreateExpr conIx createFieldNames =
  let
    createArgsExpr :: TH.ExpQ
    createArgsExpr = foldr
      (\v e -> [| BI.mkCons (toBuiltinData $(TH.varE v)) $e |])
      [| BI.mkNilData BI.unitval |]
      createFieldNames
    createExpr = [| BI.mkConstr (conIx :: Integer) $createArgsExpr |]
  in createExpr

mkConstrPartsMatchPattern :: Integer -> [TH.Name] -> TH.PatQ
mkConstrPartsMatchPattern conIx extractFieldNames =
  let
    -- (==) i -> True
    ixMatchPat = [p| ((PlutusTx.==) (conIx :: Integer) -> True) |]
    -- [unsafeFromBuiltinData -> arg1, ...]
    extractArgPats = extractFieldNames <&> \n ->
      [p| (fromBuiltinData -> Just $(TH.varP n)) |]
    extractArgsPat = go extractArgPats
      where
        go []     = [p| _ |]
        go [x]    = [p| (Builtins.headMaybe -> Just $x) |]
        go (x:xs) = [p| (Builtins.uncons -> Just ($x, $(go xs))) |]
    pat = [p| ($ixMatchPat, $extractArgsPat) |]
  in pat

-- TODO: safe match for the whole thing? not needed atm

mkUnsafeConstrMatchPattern :: Integer -> [TH.Name] -> TH.PatQ
mkUnsafeConstrMatchPattern conIx extractFieldNames =
  [p| (BI.unsafeDataAsConstr -> (Builtins.pairToPair -> $(mkUnsafeConstrPartsMatchPattern conIx extractFieldNames))) |]

-- | Function which generates a function which takes a runtime BuiltinData argument
-- and decodes it into a tuple of arguments
mkDecodingFunction
  :: TH.Name
  -- ^ Name of the type
  -> [TH.Name]
  -- ^ Type variables of the type
  -> [TH.Type]
  -- ^ Types of the fields
  -> TH.Name
  -- ^ Name of the constructor
  -> TH.Name
  -- ^ Name of the generated constructor
  -> Integer
  -- ^ Index of the constructor
  -> Integer
  -- ^ Number of fields in the constructor
  -> TH.Q [TH.Dec]
mkDecodingFunction name typeVars _ cn dTypeName dTypeConstrIx 0 = do
  let funcName = TH.mkName $ "matchOn" <> TH.nameBase cn
      builtinData = TH.mkName "builtinData"
      argPat = TH.ConP dTypeName [] [TH.VarP builtinData]
      decs =
        [ TH.ValD
            (TH.VarP $ TH.mkName "asConstr")
            (TH.NormalB $ TH.AppE (TH.VarE 'BI.unsafeDataAsConstr) (TH.VarE builtinData))
            []
        , TH.ValD
            (TH.VarP $ TH.mkName "constrIx")
            (TH.NormalB $ TH.AppE (TH.VarE 'BI.fst) (TH.VarE $ TH.mkName "asConstr"))
            []
        , TH.ValD
            (TH.VarP $ TH.mkName "constrArgs")
            (TH.NormalB $ TH.AppE (TH.VarE 'BI.snd) (TH.VarE $ TH.mkName "asConstr"))
            []
        ]
      ifExpr =
          TH.CondE
            (TH.AppE (TH.AppE (TH.VarE '(PlutusTx.==)) (TH.VarE $ TH.mkName "constrIx")) (TH.LitE . TH.IntegerL $ dTypeConstrIx))
            (TH.AppE (TH.ConE 'Just) (TH.TupE []))
            (TH.ConE 'Nothing) -- (TH.AppE (TH.VarE 'traceError) (TH.LitE (TH.StringL "testing1")))
      body = TH.NormalB $ TH.LetE decs ifExpr
      clause = TH.Clause [argPat] body []
      functionDef = TH.FunD funcName [clause]
      tType = foldl TH.AppT (TH.ConT name) $ TH.VarT <$> typeVars
      functionType = TH.SigD funcName $ TH.AppT (TH.AppT TH.ArrowT tType) (TH.AppT (TH.ConT ''Maybe) (TH.TupleT 0))
  return [functionType, functionDef]
mkDecodingFunction name typeVars fieldTypes cn dTypeName dTypeConstrIx numFields = do
  let funcName = TH.mkName $ "matchOn" <> TH.nameBase cn
      builtinData = TH.mkName "builtinData"
      argPat = TH.ConP dTypeName [] [TH.VarP builtinData]
      decs =
        [ TH.ValD
            (TH.VarP $ TH.mkName "asConstr")
            (TH.NormalB $ TH.AppE (TH.VarE 'BI.unsafeDataAsConstr) (TH.VarE builtinData))
            []
        , TH.ValD
            (TH.VarP $ TH.mkName "constrIx")
            (TH.NormalB $ TH.AppE (TH.VarE 'BI.fst) (TH.VarE $ TH.mkName "asConstr"))
            []
        , TH.ValD
            (TH.VarP $ TH.mkName "constrArgs")
            (TH.NormalB $ TH.AppE (TH.VarE 'BI.snd) (TH.VarE $ TH.mkName "asConstr"))
            []
        -- , TH.SigD (TH.mkName "field0") (Prelude.head fieldTypes)
        , TH.ValD
            (TH.VarP $ TH.mkName "field0")
            (TH.NormalB $ TH.AppE (TH.VarE 'unsafeFromBuiltinData) (TH.AppE (TH.VarE 'BI.head) (TH.VarE $ TH.mkName "constrArgs")))
            []
        ]
        <> foldMap (\i ->
            [ -- TH.SigD (TH.mkName $ "field" <> show i) (fieldTypes !! fromIntegral i)
            TH.ValD
                (TH.VarP $ TH.mkName $ "field" <> show i)
                (TH.NormalB $ TH.AppE (TH.VarE 'unsafeFromBuiltinData) (TH.AppE (TH.VarE 'BI.head) (TH.VarE $ TH.mkName $ "rest" <> show (i - 1))))
                []
            ]
            )
            [1 .. numFields - 1]
        <> fmap (\i ->
            TH.ValD
                (TH.VarP $ TH.mkName $ "rest" <> show i)
                (TH.NormalB $ TH.AppE (TH.VarE 'BI.tail) (if i == 0 then TH.VarE $ TH.mkName "constrArgs" else TH.VarE $ TH.mkName $ "rest" <> show (i - 1)))
                []
            )
            [0 .. numFields - 2]
      ifExpr =
          TH.CondE
            (TH.AppE (TH.AppE (TH.VarE '(PlutusTx.==)) (TH.VarE $ TH.mkName "constrIx")) (TH.LitE . TH.IntegerL $ dTypeConstrIx))
            (TH.AppE (TH.ConE 'Just) (TH.TupE $ fmap (Just . TH.VarE . TH.mkName . ("field" <>) . show) [0 .. numFields - 1])) -- (TH.TupE $ fmap (Just . TH.VarE . TH.mkName . ("field" <>) . show) [0 .. numFields - 1])
            (TH.ConE 'Nothing) -- (TH.AppE (TH.VarE 'traceError) (TH.LitE (TH.StringL "testing2")))
      body = TH.NormalB $ TH.LetE decs ifExpr
      clause = TH.Clause [argPat] body []
      functionDef = TH.FunD funcName [clause]
      tupleType = foldl TH.AppT (TH.TupleT (fromIntegral numFields)) fieldTypes
      tType = foldl TH.AppT (TH.ConT name) $ TH.VarT <$> typeVars
      constraints = fmap (\ty -> TH.AppT (TH.ConT ''UnsafeFromData) (TH.VarT ty)) typeVars
      typeBody =  TH.AppT (TH.AppT TH.ArrowT tType) (TH.AppT (TH.ConT ''Maybe) tupleType)
      typeBodyWithQuantification = TH.ForallT [] constraints typeBody
      functionType = TH.SigD funcName typeBodyWithQuantification
  return [functionType, functionDef]

mkUnsafeConstrPartsMatchPattern :: Integer -> [TH.Name] -> TH.PatQ
mkUnsafeConstrPartsMatchPattern conIx extractFieldNames =
  let
    -- (==) i -> True
    ixMatchPat = [p| ((PlutusTx.==) (conIx :: Integer) -> True) |]
    -- [unsafeFromBuiltinData -> arg1, ...]
    extractArgPats = extractFieldNames <&> \n ->
      [p| (unsafeFromBuiltinData -> $(TH.varP n)) |]
    extractArgsPat = go extractArgPats
      where
        go []     = [p| _ |]
        go [x]    = [p| (BI.head -> $x) |]
        go (x:xs) = [p| (Builtins.unsafeUncons -> ($x, $(go xs))) |]
    pat = [p| ($ixMatchPat, $extractArgsPat) |]
  in pat

toDataClause :: (TH.ConstructorInfo, Int) -> TH.Q TH.Clause
toDataClause (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) = do
    argNames <- for argTys $ \_ -> TH.newName "arg"
    let create = mkConstrCreateExpr (fromIntegral index) argNames
    TH.clause [TH.conP name (fmap TH.varP argNames)] (TH.normalB create) []

toDataClauses :: [(TH.ConstructorInfo, Int)] -> [TH.Q TH.Clause]
toDataClauses indexedCons = toDataClause <$> indexedCons

reconstructCase :: (TH.ConstructorInfo, Int) -> TH.MatchQ
reconstructCase (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) = do
    argNames <- for argTys $ \_ -> TH.newName "arg"

    -- Build the constructor application, assuming that all the arguments are in scope
    let app = Foldable.foldl' (\h v -> [| $h $(TH.varE v) |]) (TH.conE name) argNames

    TH.match (mkConstrPartsMatchPattern (fromIntegral index) argNames) (TH.normalB [| Just $app |]) []

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
      finalCase = TH.match TH.wildP (TH.normalB [| Nothing |]) []
      cases = conCases ++ [finalCase]
      kase :: TH.ExpQ
      kase = TH.caseE [| ($(TH.varE indexName), $(TH.varE argsName))|] cases
    let body =
          [|
            -- See Note [Bang patterns in TH quotes]
            let constrFun $(TH.bangP $ TH.varP indexName) $(TH.bangP $ TH.varP argsName) = $kase
            in matchData' $(TH.varE dName) constrFun (const Nothing) (const Nothing) (const Nothing) (const Nothing)
          |]
    TH.clause [TH.varP dName] (TH.normalB body) []

unsafeReconstructCase :: (TH.ConstructorInfo, Int) -> TH.MatchQ
unsafeReconstructCase (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) = do
    argNames <- for argTys $ \_ -> TH.newName "arg"

    -- Build the constructor application, assuming that all the arguments are in scope
    let app = foldl' (\h v -> [| $h $(TH.varE v) |]) (TH.conE name) argNames

    TH.match (mkUnsafeConstrPartsMatchPattern (fromIntegral index) argNames) (TH.normalB app) []

unsafeFromDataClause :: [(TH.ConstructorInfo, Int)] -> TH.Q TH.Clause
unsafeFromDataClause indexedCons = do
    dName <- TH.newName "d"
    tupName <- TH.newName "tup"
    indexName <- TH.newName "index"
    argsName <- TH.newName "args"
    -- Call the clause for each constructor, falling through to the next one, until we get to the end in which case we call 'error'
    let
      conCases :: [TH.MatchQ]
      conCases = (fmap (\ixCon -> unsafeReconstructCase ixCon) indexedCons)
      finalCase :: TH.MatchQ
      finalCase = TH.match TH.wildP (TH.normalB [| traceError reconstructCaseError |]) []
      cases = conCases ++ [finalCase]
      kase :: TH.ExpQ
      kase = TH.caseE [| ($(TH.varE indexName), $(TH.varE argsName))|] cases
    let body =
          [|
            -- See Note [Bang patterns in TH quotes]
            let $(TH.bangP $ TH.varP tupName) = BI.unsafeDataAsConstr $(TH.varE dName)
                $(TH.bangP $ TH.varP indexName) = BI.fst $(TH.varE tupName)
                $(TH.bangP $ TH.varP argsName) = BI.snd $(TH.varE tupName)
            in $kase
          |]
    TH.clause [TH.varP dName] (TH.normalB body) []

defaultIndex :: TH.Name -> TH.Q [(TH.Name, Int)]
defaultIndex name = do
    info <- TH.reifyDatatype name
    pure $ zip (TH.constructorName <$> TH.datatypeCons info) [0..]

-- | Generate a 'FromData' and a 'ToData' instance for a type.
-- This may not be stable in the face of constructor additions,
-- renamings, etc. Use 'makeIsDataIndexed' if you need stability.
unstableMakeIsData :: TH.Name -> TH.Q [TH.Dec]
unstableMakeIsData name = makeIsDataIndexed name =<< defaultIndex name

-- | Generate a 'ToData', 'FromData and a 'UnsafeFromData' instances for a type,
-- using an explicit mapping of constructor names to indices.
-- Use this for types where you need to keep the representation stable.
makeIsDataIndexed :: TH.Name -> [(TH.Name, Int)] -> TH.Q [TH.Dec]
makeIsDataIndexed dataTypeName indices = do
  dataTypeInfo <- TH.reifyDatatype dataTypeName
  let appliedType = TH.datatypeType dataTypeInfo
  let nonOverlapInstance = TH.InstanceD Nothing

  indexedCons <- for (TH.datatypeCons dataTypeInfo) $ \ctorInfo ->
    case lookup (TH.constructorName ctorInfo) indices of
      Just i  -> pure (ctorInfo, i)
      Nothing -> fail $ "No index given for constructor" ++ show (TH.constructorName ctorInfo)

  toDataInst <- do
    let constraints = TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
          TH.classPred ''ToData [TH.VarT (tyvarbndrName tyVarBinder)]
    toDataDecl <- TH.funD 'toBuiltinData (toDataClauses indexedCons)
    toDataPrag <- TH.pragInlD 'toBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
    pure $ nonOverlapInstance
      constraints
      (TH.classPred ''ToData [appliedType])
      [toDataPrag, toDataDecl]

  fromDataInst <- do
    let constraints = TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
          TH.classPred ''FromData [TH.VarT (tyvarbndrName tyVarBinder)]
    fromDataDecl <- TH.funD 'fromBuiltinData [fromDataClause indexedCons]
    fromDataPrag <- TH.pragInlD 'fromBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
    pure $ nonOverlapInstance
      constraints
      (TH.classPred ''FromData [appliedType])
      [fromDataPrag, fromDataDecl]

  unsafeFromDataInst <- do
    let constraints = TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
          TH.classPred ''UnsafeFromData [TH.VarT (tyvarbndrName tyVarBinder)]
    unsafeFromDataDecl <- TH.funD 'unsafeFromBuiltinData [unsafeFromDataClause indexedCons]
    unsafeFromDataPrag <- TH.pragInlD 'unsafeFromBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
    pure $ nonOverlapInstance
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
