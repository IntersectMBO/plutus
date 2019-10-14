{-# LANGUAGE TemplateHaskell #-}
module Language.PlutusTx.IsData.TH (makeIsData) where

import           Data.Foldable
import           Data.Traversable

import qualified Language.Haskell.TH            as TH
import qualified Language.Haskell.TH.Datatype   as TH

import qualified Language.PlutusTx.Applicative  as PlutusTx
import           Language.PlutusTx.Data
import qualified Language.PlutusTx.Eq           as PlutusTx

import           Language.PlutusTx.IsData.Class

toDataClause :: Int -> TH.ConstructorInfo -> TH.Q TH.Clause
toDataClause index TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys} = do
    argNames <- for argTys $ \_ -> TH.newName "arg"
    let pat = TH.conP name (fmap TH.varP argNames)
    let argsToData = fmap (\v -> [| toData $(TH.varE v) |]) argNames
    let app = [| Constr index $(TH.listE argsToData) |]
    TH.clause [pat] (TH.normalB app) []

toDataClauses :: TH.DatatypeInfo -> [TH.Q TH.Clause]
toDataClauses dt = zipWith toDataClause [0..] (TH.datatypeCons dt)

fromDataClause :: Int -> TH.ConstructorInfo -> TH.Q TH.Clause
fromDataClause index TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys} = do
    argNames <- for argTys $ \_ -> TH.newName "arg"
    indexName <- TH.newName "i"
    let pat = TH.conP 'Constr [TH.varP indexName , TH.listP (fmap TH.varP argNames)]
    let argsFromData = fmap (\v -> [| fromData $(TH.varE v) |]) argNames
    let app = foldl' (\h e -> [| $h PlutusTx.<*> $e |]) [| PlutusTx.pure $(TH.conE name) |] argsFromData
    let guard = [| $(TH.varE indexName) PlutusTx.== index |]
    TH.clause [pat] (TH.guardedB [TH.normalGE guard app]) []

fromDataClauses :: TH.DatatypeInfo -> [TH.Q TH.Clause]
fromDataClauses dt =
    let mainClauses = zipWith fromDataClause [0..] (TH.datatypeCons dt)
        catchallClause = TH.clause [TH.wildP] (TH.normalB [| Nothing |]) []
    in mainClauses ++ [ catchallClause ]

makeIsData :: TH.Name -> TH.Q [TH.Dec]
makeIsData name = do

    info <- TH.reifyDatatype name
    let appliedType = TH.datatypeType info
        constraints = fmap (\t -> TH.classPred ''IsData [stripSig t]) (TH.datatypeVars info)

    toDataDecl <- TH.funD 'toData (toDataClauses info)
    toDataPrag <- TH.pragInlD 'toData TH.Inlinable TH.FunLike TH.AllPhases

    fromDataDecl <- TH.funD 'fromData (fromDataClauses info)
    fromDataPrag <- TH.pragInlD 'fromData TH.Inlinable TH.FunLike TH.AllPhases

    pure [TH.InstanceD Nothing constraints (TH.classPred ''IsData [appliedType]) [toDataPrag, toDataDecl, fromDataPrag, fromDataDecl]]
    where
        stripSig (TH.SigT ty _) = ty
        stripSig x              = x
