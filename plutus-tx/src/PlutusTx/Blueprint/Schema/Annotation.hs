{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoStrict           #-}

module PlutusTx.Blueprint.Schema.Annotation where

import Data.Aeson (ToJSON (..))
import Data.Data (Data, Typeable)
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax (Lift)
import Prelude hiding (max, maximum, min, minimum)

-- | Additional information about a schema definition is a set of annotations.
type SchemaInfo = Set SchemaAnn

emptySchemaInfo :: SchemaInfo
emptySchemaInfo = Set.empty

-- | Annotation that can be attached to a schema definition.
data SchemaAnn
  = MkSchemaAnnTitle SchemaTitle
  | MkSchemaAnnDescription SchemaDescription
  | MkSchemaAnnComment SchemaComment
  deriving stock (Eq, Ord, Show, Generic, Typeable, Data, Lift)

{- | An annotation for the "title" schema attribute.

This annotation could be attached to a type or constructor:
@
{\-# ANN type MyFoo (SchemaTitle "My Foo Title") #-\}
{\-# ANN MkMyFoo (SchemaTitle "Title") #-\}
newtype MyFoo = MkMyFoo Int
@
-}
newtype SchemaTitle = SchemaTitle String
  deriving newtype (Eq, Ord, Show, Typeable, ToJSON)
  deriving stock (Data, Lift)

{- | An annotation for the "description" schema attribute.

This annotation could be attached to a type or constructor:
@
{\-# ANN type MyFoo (SchemaDescription "My Foo Description") #-\}
{\-# ANN MkMyFoo (SchemaDescription "Description") #-\}
newtype MyFoo = MkMyFoo Int
@
-}
newtype SchemaDescription = SchemaDescription String
  deriving newtype (Eq, Ord, Show, Typeable, ToJSON)
  deriving stock (Data, Lift)

{- | An annotation for the "$comment" schema attribute.

This annotation could be attached to a type or constructor:
@
{\-# ANN type MyFoo (SchemaComment "My Foo Comment") #-\}
{\-# ANN MkMyFoo (SchemaComment "Comment") #-\}
newtype MyFoo = MkMyFoo Int
@
-}
newtype SchemaComment = SchemaComment String
  deriving newtype (Eq, Ord, Show, Typeable, ToJSON)
  deriving stock (Data, Lift)
