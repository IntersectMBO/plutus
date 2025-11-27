{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

-- | This module provides a functionality to derive and reference schema definitions.
module PlutusTx.Blueprint.Definition.Internal where

import Prelude

import Data.Kind (Constraint, Type)
import Data.Map (Map)
import Data.Map qualified as Map
import GHC.TypeLits qualified as GHC
import PlutusTx.Blueprint.Definition.Id (DefinitionId)
import PlutusTx.Blueprint.Schema (Schema (..))

-- | A schema definition of a type @t@ with a list of referenced types @ts@.
data Definition t ts = MkDefinition DefinitionId (Schema ts)
  deriving stock (Show)

-- | A registry of schema definitions.
data Definitions ts where
  NoDefinitions :: Definitions ts
  AddDefinition :: Definition t ts -> Definitions ts -> Definitions ts

deriving stock instance Show (Definitions ts)

-- | Add a schema definition to a registry.
addDefinition :: Definitions ts -> Definition t ts -> Definitions ts
addDefinition NoDefinitions d = AddDefinition d NoDefinitions
addDefinition (AddDefinition t s) d = AddDefinition d (AddDefinition t s)

definitionsToMap :: Definitions ts -> (forall xs. Schema xs -> v) -> Map DefinitionId v
definitionsToMap NoDefinitions _k = Map.empty
definitionsToMap (AddDefinition (MkDefinition defId v) s) k =
  Map.insert defId (k v) (definitionsToMap s k)

{-|
  A constraint that checks if a schema definition is present in a list of schema definitions.
  Gives a user-friendly error message if the schema definition is not found. -}
type HasSchemaDefinition t ts = HasSchemaDefinition' t ts ts

type HasSchemaDefinition' :: Type -> [Type] -> [Type] -> Constraint
type family HasSchemaDefinition' n xs xs0 where
  HasSchemaDefinition' x (x ': xs) _ = ()
  HasSchemaDefinition' x (_ ': xs) xs0 = HasSchemaDefinition' x xs xs0
  HasSchemaDefinition' n xs xs0 =
    GHC.TypeError
      ( GHC.ShowType n
          GHC.:<>: GHC.Text " type was not found in the list of types having schema definitions: "
          GHC.:<>: GHC.ShowType xs0
      )
