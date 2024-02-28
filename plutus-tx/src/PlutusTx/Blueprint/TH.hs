{-# LANGUAGE CPP              #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns     #-}

module PlutusTx.Blueprint.TH where

import Prelude

import Data.List (nub)
import Data.List.NonEmpty qualified as NE
import Data.Traversable (for)
import Data.Typeable (Typeable)
import GHC.Natural (Natural, naturalToInteger)
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH
import PlutusTx.Blueprint.Class (HasDataSchema (..))
import PlutusTx.Blueprint.Definition (HasSchemaDefinition)
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.IsData.TH (makeIsDataIndexed)

{- | Generate a 'ToData', 'FromData', 'UnsafeFromData', 'HasDataSchema' instances for a type,
using an explicit mapping of constructor names to indices.
Use this for types where you need to keep the representation stable.
-}
makeIsDataSchemaIndexed :: TH.Name -> [(TH.Name, Natural)] -> TH.Q [TH.InstanceDec]
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
    let tsType = TH.VarT (TH.mkName "ts")
    let constraints = nub $
          [ constraint
          | tyVarBinder <- TH.datatypeVars dataTypeInfo
          , let tType = TH.VarT (tyvarbndrName tyVarBinder)
          , constraint <-
              [ TH.classPred ''Typeable [tType]
              , TH.classPred ''HasSchemaDefinition [tType, tsType]
              ]
          ]
            ++ [ TH.classPred ''HasSchemaDefinition [fieldType, tsType]
               | (TH.ConstructorInfo{constructorFields}, _index) <- indexedCons
               , fieldType <- constructorFields
               ]
    hasDataSchemaPrag <- TH.funD 'dataSchema [toClause tsType indexedCons]
    hasDataSchemaDecl <- TH.pragInlD 'dataSchema TH.Inlinable TH.FunLike TH.AllPhases
    pure
      $ nonOverlapInstance
        constraints
        (TH.classPred ''HasDataSchema [appliedType, tsType])
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

toClause :: TH.Type -> [(TH.ConstructorInfo, Natural)] -> TH.ClauseQ
toClause ts ctorIndexes =
  case ctorIndexes of
    []          -> fail "At least one constructor index must be specified."
    [ctorIndex] -> mkBody (mkCtor ctorIndex)
    _           -> mkBody [|SchemaOneOf (NE.fromList $(TH.listE (fmap mkCtor ctorIndexes)))|]
 where
  mkBody :: TH.ExpQ -> TH.ClauseQ
  mkBody body = do
    let patterns = []
    let whereDecls = []
    TH.clause patterns (TH.normalB body) whereDecls

  mkCtor :: (TH.ConstructorInfo, Natural) -> TH.ExpQ
  mkCtor (TH.ConstructorInfo{..}, naturalToInteger -> ctorIndex) = do
    fields <- for constructorFields $ \t -> [|definitionRef @($(pure t)) @($(pure ts))|]
    let name = TH.nameBase constructorName
    [|SchemaConstructor Nothing Nothing (Just name) ctorIndex $(pure (TH.ListE fields))|]
