{-# LANGUAGE CPP              #-}
{-# LANGUAGE EmptyCase        #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns     #-}

module PlutusTx.Blueprint.TH where

import Prelude

import Data.Data (Data)
import Data.List (nub)
import Data.List.NonEmpty qualified as NE
import Data.Set (Set)
import Data.Text qualified as Text
import GHC.Natural (naturalToInteger)
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH
import Numeric.Natural (Natural)
import PlutusPrelude (for, (<&>), (<<$>>))
import PlutusTx.Blueprint.Argument (ArgumentBlueprint (..))
import PlutusTx.Blueprint.Class (HasSchema (..))
import PlutusTx.Blueprint.Definition (HasSchemaDefinition)
import PlutusTx.Blueprint.Parameter (ParameterBlueprint (..))
import PlutusTx.Blueprint.Purpose (Purpose)
import PlutusTx.Blueprint.Schema (ConstructorSchema (..), Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (SchemaAnn (..), SchemaComment, SchemaDescription,
                                             SchemaInfo (..), SchemaTitle, annotationsToSchemaInfo,
                                             schemaDescriptionToString, schemaTitleToString)
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
  indexedCons :: [(TH.ConstructorInfo, SchemaInfo, Natural)] <- do
    for (TH.datatypeCons dataTypeInfo) $ \ctorInfo -> do
      let ctorName = TH.constructorName ctorInfo
      case lookup ctorName indices of
        Nothing -> fail $ "No index given for constructor " ++ show (TH.constructorName ctorInfo)
        Just index -> do
          ctorSchemaAnns <- lookupSchemaAnns ctorName
          schemaInfo <- schemaInfoFromAnns ctorSchemaAnns
          pure (ctorInfo, schemaInfo, index)

  let tsType = TH.VarT (TH.mkName "referencedTypes")

  -- Generate constraints for the instance.
  let constraints =
        nub
          -- Every type in the constructor fields must have a schema definition.
          [ TH.classPred ''HasSchemaDefinition [fieldType, tsType]
          | (TH.ConstructorInfo{constructorFields}, _info, _index) <- indexedCons
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
 where
  -- Lookup all annotations (SchemaTitle, SchemdDescription, SchemaComment) attached to a name.
  lookupSchemaAnns :: TH.Name -> TH.Q [SchemaAnn]
  lookupSchemaAnns name = do
    title <- MkSchemaAnnTitle <<$>> lookupAnn @SchemaTitle name
    description <- MkSchemaAnnDescription <<$>> lookupAnn @SchemaDescription name
    comment <- MkSchemaAnnComment <<$>> lookupAnn @SchemaComment name
    pure $ title ++ description ++ comment

  -- | Make SchemaInfo from a list of schema annotations, failing in case of ambiguity.
  schemaInfoFromAnns :: [SchemaAnn] -> TH.Q SchemaInfo
  schemaInfoFromAnns = either fail pure . annotationsToSchemaInfo

-- | Make a clause for the 'schema' function.
mkSchemaClause ::
  -- | The type for the 'HasSchema' instance.
  TH.Type ->
  -- | The constructors of the type with their schema infos and indices.
  [(TH.ConstructorInfo, SchemaInfo, Natural)] ->
  -- | The clause for the 'schema' function.
  TH.ClauseQ
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

  mkSchemaConstructor :: (TH.ConstructorInfo, SchemaInfo, Natural) -> TH.ExpQ
  mkSchemaConstructor (TH.ConstructorInfo{..}, info, naturalToInteger -> ctorIndex) = do
    fields <- for constructorFields $ \t -> [|definitionRef @($(pure t)) @($(pure ts))|]
    [|SchemaConstructor info (MkConstructorSchema ctorIndex $(pure (TH.ListE fields)))|]

deriveParameterBlueprint :: TH.Name -> Set Purpose -> TH.ExpQ
deriveParameterBlueprint tyName purpose = do
  title <- Text.pack . schemaTitleToString <<$>> lookupSchemaTitle tyName
  description <- Text.pack . schemaDescriptionToString <<$>> lookupSchemaDescription tyName
  [| MkParameterBlueprint
      { parameterTitle = title
      , parameterDescription = description
      , parameterPurpose = purpose
      , parameterSchema = definitionRef @($(TH.conT tyName))
      }
    |]

deriveArgumentBlueprint :: TH.Name -> Set Purpose -> TH.ExpQ
deriveArgumentBlueprint tyName purpose = do
  title <- Text.pack . schemaTitleToString <<$>> lookupSchemaTitle tyName
  description <- Text.pack . schemaDescriptionToString <<$>> lookupSchemaDescription tyName
  [| MkArgumentBlueprint
      { argumentTitle = title
      , argumentDescription = description
      , argumentPurpose = purpose
      , argumentSchema = definitionRef @($(TH.conT tyName))
      }
    |]

----------------------------------------------------------------------------------------------------
-- TH Utilities ------------------------------------------------------------------------------------

lookupAnn :: (Data a) => TH.Name -> TH.Q [a]
lookupAnn = TH.reifyAnnotations . TH.AnnLookupName

lookupSchemaTitle :: TH.Name -> TH.Q (Maybe SchemaTitle)
lookupSchemaTitle tyName = lookupAnn @SchemaTitle tyName <&> \case
    [x] -> Just x
    [] -> Nothing
    _ -> fail $ "Multiple SchemTitle annotations found for " <> show tyName

lookupSchemaDescription :: TH.Name -> TH.Q (Maybe SchemaDescription)
lookupSchemaDescription tyName = lookupAnn @SchemaDescription tyName <&> \case
    [x] -> Just x
    [] -> Nothing
    _ -> fail $ "Multiple SchemaDescription annotations found for " <> show tyName
