{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoStrict #-}

module PlutusTx.Blueprint.Schema.Annotation
  ( SchemaInfo (..)
  , emptySchemaInfo
  , annotationsToSchemaInfo
  , SchemaAnn (..)
  , SchemaTitle (..)
  , SchemaDescription (..)
  , SchemaComment (..)
  ) where

import Control.Monad.State (execStateT, get, lift, put)
import Data.Aeson (ToJSON (..))
import Data.Data (Data)
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax (Lift)
import Prelude hiding (max, maximum, min, minimum)

-- | Additional information optionally attached to any datatype schema definition.
data SchemaInfo = MkSchemaInfo
  { title :: Maybe String
  , description :: Maybe String
  , comment :: Maybe String
  }
  deriving stock (Eq, Ord, Show, Generic, Data, Lift)

emptySchemaInfo :: SchemaInfo
emptySchemaInfo = MkSchemaInfo Nothing Nothing Nothing

type SchemaInfoError = String

annotationsToSchemaInfo :: [SchemaAnn] -> Either SchemaInfoError SchemaInfo
annotationsToSchemaInfo =
  (`execStateT` emptySchemaInfo) . traverse \case
    MkSchemaAnnTitle (SchemaTitle t) ->
      get >>= \info -> case title info of
        Nothing -> put $ info {title = Just t}
        Just t' -> failOverride "SchemaTitle" t' t
    MkSchemaAnnDescription (SchemaDescription d) ->
      get >>= \info -> case description info of
        Nothing -> put $ info {description = Just d}
        Just d' -> failOverride "SchemaDescription" d' d
    MkSchemaAnnComment (SchemaComment c) ->
      get >>= \info -> case comment info of
        Nothing -> put $ info {comment = Just c}
        Just c' -> failOverride "SchemaComment" c' c
  where
    failOverride label old new =
      lift . Left $ concat [label, " annotation error: ", show old, " is overridden with ", show new]

-- | Annotation that can be attached to a schema definition.
data SchemaAnn
  = MkSchemaAnnTitle SchemaTitle
  | MkSchemaAnnDescription SchemaDescription
  | MkSchemaAnnComment SchemaComment
  deriving stock (Eq, Ord, Show, Generic, Data, Lift)

{-| An annotation for the "title" schema attribute.

This annotation could be attached to a type or constructor:
@
{\-# ANN type MyFoo (SchemaTitle "My Foo Title") #-\}
{\-# ANN MkMyFoo (SchemaTitle "Title") #-\}
newtype MyFoo = MkMyFoo Int
@ -}
newtype SchemaTitle = SchemaTitle {schemaTitleToString :: String}
  deriving newtype (Eq, Ord, Show, ToJSON)
  deriving stock (Data, Lift)

{-| An annotation for the "description" schema attribute.

This annotation could be attached to a type or constructor:
@
{\-# ANN type MyFoo (SchemaDescription "My Foo Description") #-\}
{\-# ANN MkMyFoo (SchemaDescription "Description") #-\}
newtype MyFoo = MkMyFoo Int
@ -}
newtype SchemaDescription = SchemaDescription {schemaDescriptionToString :: String}
  deriving newtype (Eq, Ord, Show, ToJSON)
  deriving stock (Data, Lift)

{-| An annotation for the "$comment" schema attribute.

This annotation could be attached to a type or constructor:
@
{\-# ANN type MyFoo (SchemaComment "My Foo Comment") #-\}
{\-# ANN MkMyFoo (SchemaComment "Comment") #-\}
newtype MyFoo = MkMyFoo Int
@ -}
newtype SchemaComment = SchemaComment {schemaCommentToString :: String}
  deriving newtype (Eq, Ord, Show, ToJSON)
  deriving stock (Data, Lift)
