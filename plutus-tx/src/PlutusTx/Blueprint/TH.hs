{-# LANGUAGE CPP              #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns     #-}

module PlutusTx.Blueprint.TH where

import Prelude

import Data.Functor ((<&>))
import Data.List.NonEmpty qualified as NE
import Data.Traversable (for)
import GHC.Natural (Natural, naturalToInteger)
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH
import PlutusTx.Blueprint.Class (HasDataSchema (..))
import PlutusTx.Blueprint.Schema (DataSchema (..))
import PlutusTx.IsData.TH (makeIsDataIndexed)

{- | Generate a 'ToData', 'FromData', 'UnsafeFromData', 'HasDataSchema' instances for a type,
using an explicit mapping of constructor names to indices.
Use this for types where you need to keep the representation stable.
-}
makeIsDataSchemaIndexed :: TH.Name -> [(TH.Name, Natural)] -> TH.Q [TH.Dec]
makeIsDataSchemaIndexed dataTypeName indices = do
  dataInstances <- makeIsDataIndexed dataTypeName (map (fmap fromIntegral) indices)
  dataTypeInfo <- TH.reifyDatatype dataTypeName
  let appliedType = TH.datatypeType dataTypeInfo
  let nonOverlapInstance = TH.InstanceD Nothing

  indexedCons <- for (TH.datatypeCons dataTypeInfo) $ \ctorInfo ->
    case lookup (TH.constructorName ctorInfo) indices of
      Just index -> pure (ctorInfo, index)
      Nothing    -> fail $ "No index given for constructor " ++ show (TH.constructorName ctorInfo)

  hasDataSchemaInst <- do
    let constraints =
          TH.datatypeVars dataTypeInfo <&> \tyVarBinder ->
            TH.classPred ''HasDataSchema [TH.VarT (tyvarbndrName tyVarBinder)]
    hasDataSchemaPrag <- TH.funD 'dataSchema [toDataClause indexedCons]
    hasDataSchemaDecl <- TH.pragInlD 'dataSchema TH.Inlinable TH.FunLike TH.AllPhases
    pure
      $ nonOverlapInstance
        constraints
        (TH.classPred ''HasDataSchema [appliedType])
        [hasDataSchemaPrag, hasDataSchemaDecl]

  pure $ hasDataSchemaInst : dataInstances
 where
#if MIN_VERSION_template_haskell(2,17,0)
  tyvarbndrName (TH.PlainTV n _)    = n
  tyvarbndrName (TH.KindedTV n _ _) = n
#else
  tyvarbndrName (TH.PlainTV n)      = n
  tyvarbndrName (TH.KindedTV n _)   = n
#endif

toDataClause :: [(TH.ConstructorInfo, Natural)] -> TH.ClauseQ
toDataClause ctorIndexes =
  case ctorIndexes of
    []          -> fail "At least one constructor index must be specified."
    [ctorIndex] -> mkBody (mkCtor ctorIndex)
    _           -> mkBody [|DSOneOf (NE.fromList $(TH.listE (fmap mkCtor ctorIndexes)))|]
 where
  mkBody :: TH.ExpQ -> TH.ClauseQ
  mkBody body = do
    let patterns = []
    let whereDecls = []
    TH.clause patterns (TH.normalB body) whereDecls

  mkCtor :: (TH.ConstructorInfo, Natural) -> TH.ExpQ
  mkCtor (TH.ConstructorInfo{..}, naturalToInteger -> ctorIndex) = do
    fields <- for constructorFields $ \ty -> [|dataSchema @($(pure ty))|]
    let name = TH.nameBase constructorName
    [|DSConstructor Nothing Nothing (Just name) ctorIndex $(pure (TH.ListE fields))|]
