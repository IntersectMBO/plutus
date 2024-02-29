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
import GHC.Natural (Natural, naturalToInteger)
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH
import PlutusTx.Blueprint.Class (HasSchema (..))
import PlutusTx.Blueprint.Definition (HasSchemaDefinition)
import PlutusTx.Blueprint.Schema (ConstructorSchema (..), Schema (..), SchemaInfo (..))
import PlutusTx.IsData.TH (makeIsDataIndexed)

{- |
  Generate a 'ToData', 'FromData', 'UnsafeFromData', 'HasSchema' instances for a type,
  using an explicit mapping of constructor names to indices.
  Use this for types where you need to keep the representation stable.
-}
makeIsDataSchemaIndexed :: TH.Name -> [(TH.Name, Natural)] -> TH.Q [TH.InstanceDec]
makeIsDataSchemaIndexed dataTypeName indices = do
  dataInstances <- makeIsDataIndexed dataTypeName (fmap fromIntegral <$> indices)
  hasSchemaInstance <- makeHasSchemaInstance dataTypeName indices
  pure $ hasSchemaInstance : dataInstances

makeHasSchemaInstance :: TH.Name -> [(TH.Name, Natural)] -> TH.Q TH.InstanceDec
makeHasSchemaInstance dataTypeName indices = do
  dataTypeInfo <- TH.reifyDatatype dataTypeName
  let appliedType = TH.datatypeType dataTypeInfo
  let nonOverlapInstance = TH.InstanceD Nothing

  -- Lookup indices for all constructors of a data type.
  indexedCons <- for (TH.datatypeCons dataTypeInfo) $ \ctorInfo ->
    case lookup (TH.constructorName ctorInfo) indices of
      Just index -> pure (ctorInfo, index)
      Nothing    -> fail $ "No index given for constructor " ++ show (TH.constructorName ctorInfo)

  let tsType = TH.VarT (TH.mkName "referencedTypes")

  -- Generate constraints for the instance.
  let constraints =
        nub
          -- Every type in the constructor fields must have a schema definition.
          [ TH.classPred ''HasSchemaDefinition [fieldType, tsType]
          | (TH.ConstructorInfo{constructorFields}, _index) <- indexedCons
          , fieldType <- constructorFields
          ]
  -- Generate a 'schema' function for the instance with one clause.
  schemaPrag <- TH.funD 'schema [mkSchemaClause tsType indexedCons]
  -- Generate a pragma for the 'schema' function, making it inlinable.
  schemaDecl <- TH.pragInlD 'schema TH.Inlinable TH.FunLike TH.AllPhases
  pure
    -- Generate an instance declaration, e.g.:
    -- instance (constraints) => HasSchema T referencedTypes where
    --   {-# INLINE schema #-}
    --   schema = ...
    $ nonOverlapInstance
      constraints
      (TH.classPred ''HasSchema [appliedType, tsType])
      [schemaPrag, schemaDecl]

-- | Make a clause for the 'schema' function.
mkSchemaClause :: TH.Type -> [(TH.ConstructorInfo, Natural)] -> TH.ClauseQ
mkSchemaClause ts ctorIndexes =
  case ctorIndexes of
    [] -> fail "At least one constructor index must be specified."
    [ctorIndex] -> mkBody (mkSchemaConstructor ctorIndex)
    _ -> mkBody [|SchemaOneOf (NE.fromList $(TH.listE (fmap mkSchemaConstructor ctorIndexes)))|]
 where
  mkBody :: TH.ExpQ -> TH.ClauseQ
  mkBody body = do
    let patterns = []
    let whereDecls = []
    TH.clause patterns (TH.normalB body) whereDecls

  mkSchemaConstructor :: (TH.ConstructorInfo, Natural) -> TH.ExpQ
  mkSchemaConstructor (TH.ConstructorInfo{..}, naturalToInteger -> ctorIndex) = do
    fields <- for constructorFields $ \t -> [|definitionRef @($(pure t)) @($(pure ts))|]
    let name = TH.nameBase constructorName
    [|
      SchemaConstructor
        (MkSchemaInfo Nothing Nothing (Just name))
        (MkConstructorSchema ctorIndex $(pure (TH.ListE fields)))
      |]
