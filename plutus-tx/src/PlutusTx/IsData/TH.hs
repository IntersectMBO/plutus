{-# LANGUAGE TemplateHaskell #-}
module PlutusTx.IsData.TH (unstableMakeIsData, makeIsDataIndexed) where

import           Data.Foldable
import           Data.Traversable

import qualified Language.Haskell.TH          as TH
import qualified Language.Haskell.TH.Datatype as TH

import qualified PlutusTx.Applicative         as PlutusTx
import           PlutusTx.Data
import qualified PlutusTx.Eq                  as PlutusTx

import           PlutusTx.IsData.Class

toDataClause :: (TH.ConstructorInfo, Int) -> TH.Q TH.Clause
toDataClause (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) = do
    argNames <- for argTys $ \_ -> TH.newName "arg"
    let pat = TH.conP name (fmap TH.varP argNames)
    let argsToData = fmap (\v -> [| toData $(TH.varE v) |]) argNames
    let app = [| Constr index $(TH.listE argsToData) |]
    TH.clause [pat] (TH.normalB app) []

toDataClauses :: [(TH.ConstructorInfo, Int)] -> [TH.Q TH.Clause]
toDataClauses indexedCons = toDataClause <$> indexedCons

fromDataClause :: (TH.ConstructorInfo, Int) -> TH.Q TH.Clause
fromDataClause (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) = do
    argNames <- for argTys $ \_ -> TH.newName "arg"
    indexName <- TH.newName "i"
    let pat = TH.conP 'Constr [TH.varP indexName , TH.listP (fmap TH.varP argNames)]
    let argsFromData = fmap (\v -> [| fromData $(TH.varE v) |]) argNames
    let app = foldl' (\h e -> [| $h PlutusTx.<*> $e |]) [| PlutusTx.pure $(TH.conE name) |] argsFromData
    let guard = [| $(TH.varE indexName) PlutusTx.== index |]
    TH.clause [pat] (TH.guardedB [TH.normalGE guard app]) []

fromDataClauses :: [(TH.ConstructorInfo, Int)] -> [TH.Q TH.Clause]
fromDataClauses indexedCons =
    let mainClauses = fromDataClause <$> indexedCons
        catchallClause = TH.clause [TH.wildP] (TH.normalB [| Nothing |]) []
    in mainClauses ++ [ catchallClause ]

defaultIndex :: TH.Name -> TH.Q [(TH.Name, Int)]
defaultIndex name = do
    info <- TH.reifyDatatype name
    pure $ zip (TH.constructorName <$> TH.datatypeCons info) [0..]

-- | Generate an 'IsData' instance for a type. This may not be stable in the face of constructor additions, renamings,
-- etc. Use 'makeIsDataIndexed' if you need stability.
unstableMakeIsData :: TH.Name -> TH.Q [TH.Dec]
unstableMakeIsData name = makeIsDataIndexed name =<< defaultIndex name

-- | Generate an 'IsData' instance for a type, using an explicit mapping of constructor names to indices. Use
-- this for types where you need to keep the representation stable.
makeIsDataIndexed :: TH.Name -> [(TH.Name, Int)] -> TH.Q [TH.Dec]
makeIsDataIndexed name indices = do

    info <- TH.reifyDatatype name
    let appliedType = TH.datatypeType info
        constraints = fmap (\t -> TH.classPred ''IsData [TH.VarT (tyvarbndrName t)]) (TH.datatypeVars info)

    indexedCons <- for (TH.datatypeCons info) $ \c -> case lookup (TH.constructorName c) indices of
            Just i  -> pure (c, i)
            Nothing -> fail $ "No index given for constructor" ++ show (TH.constructorName c)

    toDataDecl <- TH.funD 'toData (toDataClauses indexedCons)
    toDataPrag <- TH.pragInlD 'toData TH.Inlinable TH.FunLike TH.AllPhases

    fromDataDecl <- TH.funD 'fromData (fromDataClauses indexedCons)
    fromDataPrag <- TH.pragInlD 'fromData TH.Inlinable TH.FunLike TH.AllPhases

    pure [TH.InstanceD Nothing constraints (TH.classPred ''IsData [appliedType]) [toDataPrag, toDataDecl, fromDataPrag, fromDataDecl]]
    where
        tyvarbndrName (TH.PlainTV n)    = n
        tyvarbndrName (TH.KindedTV n _) = n
