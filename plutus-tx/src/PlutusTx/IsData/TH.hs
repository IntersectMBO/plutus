-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}
module PlutusTx.IsData.TH (unstableMakeIsData, makeIsDataIndexed) where

import Data.Foldable
import Data.Traversable

import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH
import PlutusTx.ErrorCodes

import PlutusTx.Applicative qualified as PlutusTx

import PlutusTx.Builtins as Builtins
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData.Class
import PlutusTx.Trace (traceError)

-- We do not use qualified import because the whole module contains off-chain code
import Prelude

toDataClause :: (TH.ConstructorInfo, Int) -> TH.Q TH.Clause
toDataClause (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) = do
    argNames <- for argTys $ \_ -> TH.newName "arg"
    let argsList = foldr (\v e -> [| BI.mkCons (toBuiltinData $(TH.varE v)) $e |]) [| BI.mkNilData BI.unitval |] argNames
    let app = [| BI.mkConstr index $argsList |]
    TH.clause [TH.conP name (fmap TH.varP argNames)] (TH.normalB app) []

toDataClauses :: [(TH.ConstructorInfo, Int)] -> [TH.Q TH.Clause]
toDataClauses indexedCons = toDataClause <$> indexedCons

reconstructCase :: (TH.ConstructorInfo, Int) -> TH.Q TH.Exp -> TH.Q TH.Exp -> TH.Q TH.Exp -> TH.Q TH.Exp
reconstructCase (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) ixExpr argsExpr kont = do
    argNames <- for argTys $ \_ -> TH.newName "arg"

    -- Applicatively build the constructor application, assuming that all the arguments are in scope
    let app = foldl' (\h v -> [| $h PlutusTx.<*> fromBuiltinData $(TH.varE v) |]) [| PlutusTx.pure $(TH.conE name) |] argNames

    -- Takes a list of argument names, and safely takes one element off the list for each, binding it to the name.
    -- Finally, invokes 'app'.
    let handleList :: [TH.Name] -> TH.Q TH.Exp -> TH.Q TH.Exp
        handleList [] lExp = [| matchList $lExp $app (\_ _ -> Nothing) |]
        handleList (argName:rest) lExp = do
            tailName <- TH.newName "t"
            [|
             let !consCase = \ $(TH.varP argName) $(TH.varP tailName) -> $(handleList rest (TH.varE tailName))
             in matchList $lExp Nothing consCase
             |]
    -- Check that the index matches the expected one, otherwise fallthrough to 'kont'
    let body =
            [|
                let !indexMatchCase = $(handleList argNames argsExpr)
                    !fallthrough = $kont
                in BI.ifThenElse ($ixExpr `BI.equalsInteger` (index :: Integer)) (const indexMatchCase) (const fallthrough) BI.unitval
            |]
    body

fromDataClause :: [(TH.ConstructorInfo, Int)] -> TH.Q TH.Clause
fromDataClause indexedCons = do
    dName <- TH.newName "d"
    indexName <- TH.newName "index"
    argsName <- TH.newName "args0"
    -- Call the clause for each constructor, falling through to the next one, until we get to the end in which case we return 'Nothing'
    let cases =
            foldl'
            (\kont ixCon -> reconstructCase ixCon (TH.varE indexName) (TH.varE argsName) kont)
            [| Nothing |]
            indexedCons
    let body =
          [|
            let !constrMatchCase = \ $(TH.varP indexName) $(TH.varP argsName) -> $cases
            in matchData' $(TH.varE dName) constrMatchCase (const Nothing) (const Nothing) (const Nothing) (const Nothing)
          |]
    TH.clause [TH.varP dName] (TH.normalB body) []

unsafeReconstructCase :: (TH.ConstructorInfo, Int) -> TH.Q TH.Exp -> TH.Q TH.Exp -> TH.Q TH.Exp -> TH.Q TH.Exp
unsafeReconstructCase (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) ixExpr argsExpr kont = do
    argNames <- for argTys $ \_ -> TH.newName "arg"

    -- Build the constructor application, assuming that all the arguments are in scope
    let app = foldl' (\h v -> [| $h (unsafeFromBuiltinData $(TH.varE v)) |]) (TH.conE name) argNames

    -- Takes a list of argument names, and takes one element off the list for each, binding it to the name.
    -- Finally, invokes 'app'.
    let handleList :: [TH.Name] -> TH.Q TH.Exp -> TH.Q TH.Exp
        handleList [] _ = [| $app |]
        handleList (argName:rest) lExp = do
            [|
             let
                 !t = $lExp
                 $(TH.bangP $ TH.varP argName) = BI.head t
             in $(handleList rest [| BI.tail t |])
             |]
    -- Check that the index matches the expected one, otherwise fallthrough to 'kont'
    let body =
            [|
                let !indexMatchCase = $(handleList argNames argsExpr)
                    !fallthrough = $kont
                in BI.ifThenElse ($ixExpr `BI.equalsInteger` (index :: Integer)) (const indexMatchCase) (const fallthrough) BI.unitval
            |]
    body

unsafeFromDataClause :: [(TH.ConstructorInfo, Int)] -> TH.Q TH.Clause
unsafeFromDataClause indexedCons = do
    dName <- TH.newName "d"
    indexName <- TH.newName "index"
    tupName <- TH.newName "tup"
    -- Call the clause for each constructor, falling through to the next one, until we get to the end in which case we call 'error'
    let cases =
            foldl'
            (\kont ixCon -> unsafeReconstructCase ixCon (TH.varE indexName) [| BI.snd $(TH.varE tupName) |] kont)
            [| traceError reconstructCaseError |]
            indexedCons
    let body =
          [|
            let $(TH.bangP $ TH.varP tupName) = BI.unsafeDataAsConstr $(TH.varE dName)
                $(TH.bangP $ TH.varP indexName) = BI.fst $(TH.varE tupName)
            in $cases
          |]
    TH.clause [TH.varP dName] (TH.normalB body) []

defaultIndex :: TH.Name -> TH.Q [(TH.Name, Int)]
defaultIndex name = do
    info <- TH.reifyDatatype name
    pure $ zip (TH.constructorName <$> TH.datatypeCons info) [0..]

-- | Generate a 'FromData' and a 'ToData' instance for a type. This may not be stable in the face of constructor additions,
-- renamings, etc. Use 'makeIsDataIndexed' if you need stability.
unstableMakeIsData :: TH.Name -> TH.Q [TH.Dec]
unstableMakeIsData name = makeIsDataIndexed name =<< defaultIndex name

-- | Generate a 'FromData' and a 'ToData' instance for a type, using an explicit mapping of constructor names to indices. Use
-- this for types where you need to keep the representation stable.
makeIsDataIndexed :: TH.Name -> [(TH.Name, Int)] -> TH.Q [TH.Dec]
makeIsDataIndexed name indices = do

    -- TODO: arguably this should fail on newtypes and get the user to derive the instances.
    -- Probably too late now as existing instances are relied upon.
    info <- TH.reifyDatatype name
    let appliedType = TH.datatypeType info

    indexedCons <- for (TH.datatypeCons info) $ \c -> case lookup (TH.constructorName c) indices of
            Just i  -> pure (c, i)
            Nothing -> fail $ "No index given for constructor" ++ show (TH.constructorName c)

    toDataInst <- do
        let constraints = fmap (\t -> TH.classPred ''ToData [TH.VarT (tyvarbndrName t)]) (TH.datatypeVars info)
        toDataDecl <- TH.funD 'toBuiltinData (toDataClauses indexedCons)
        toDataPrag <- TH.pragInlD 'toBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
        pure $ TH.InstanceD Nothing constraints (TH.classPred ''ToData [appliedType]) [toDataPrag, toDataDecl]

    fromDataInst <- do
        let constraints = fmap (\t -> TH.classPred ''FromData [TH.VarT (tyvarbndrName t)]) (TH.datatypeVars info)
        fromDataDecl <- TH.funD 'fromBuiltinData [fromDataClause indexedCons]
        fromDataPrag <- TH.pragInlD 'fromBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
        pure $ TH.InstanceD Nothing constraints (TH.classPred ''FromData [appliedType]) [fromDataPrag, fromDataDecl]

    unsafeFromDataInst <- do
        let constraints = fmap (\t -> TH.classPred ''UnsafeFromData [TH.VarT (tyvarbndrName t)]) (TH.datatypeVars info)
        unsafeFromDataDecl <- TH.funD 'unsafeFromBuiltinData [unsafeFromDataClause indexedCons]
        unsafeFromDataPrag <- TH.pragInlD 'unsafeFromBuiltinData TH.Inlinable TH.FunLike TH.AllPhases
        pure $ TH.InstanceD Nothing constraints (TH.classPred ''UnsafeFromData [appliedType]) [unsafeFromDataPrag, unsafeFromDataDecl]

    pure [toDataInst, fromDataInst, unsafeFromDataInst]
    where
#if MIN_VERSION_template_haskell(2,17,0)
        tyvarbndrName (TH.PlainTV n _)    = n
        tyvarbndrName (TH.KindedTV n _ _) = n
#else
        tyvarbndrName (TH.PlainTV n)      = n
        tyvarbndrName (TH.KindedTV n _)   = n
#endif
