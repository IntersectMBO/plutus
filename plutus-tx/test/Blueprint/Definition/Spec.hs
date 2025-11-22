{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Blueprint.Definition.Spec where

import Prelude

import Blueprint.Definition.Fixture qualified as Fixture
import Control.Lens.Plated (universe)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (isSubsetOf)
import Data.Set qualified as Set
import PlutusTx.Blueprint.Definition (DefinitionId, definitionsToMap, deriveDefinitions)
import PlutusTx.Blueprint.Schema (Schema (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, testCase, (@?), (@?=))

tests :: TestTree
tests =
  testGroup
    "PlutusTx.Blueprint.Definition"
    [ testCase
        "Derived definitions are empty when no types are provided."
        (definitionsToMap (deriveDefinitions @'[]) (const ()) @?= mempty)
    , testCase
        "There are not less schema definitions than listed domain types."
        atLeastAsManyDefinitionsAsTypes
    , testCase
        "All referenced schema definitions are defined."
        allReferencedDefinitionsAreDefined
    ]

atLeastAsManyDefinitionsAsTypes :: Assertion
atLeastAsManyDefinitionsAsTypes =
  (length (Map.keys definitions) >= 3)
    @? "Not enough schema definitions: < 3"
  where
    definitions = definitionsToMap (deriveDefinitions @[Fixture.T1, Fixture.T2, Integer]) (const ())

allReferencedDefinitionsAreDefined :: Assertion
allReferencedDefinitionsAreDefined =
  (referencedIds `isSubsetOf` definedIds)
    @? "Not all referenced schema definitions are defined"
  where
    referencedIds =
      Set.fromList
        [ ref
        | schemas <- universe (Map.elems definitions)
        , SomeSchema (SchemaDefinitionRef ref) <- schemas
        ]
    definedIds = Set.fromList (Map.keys definitions)

    definitions :: Map DefinitionId SomeSchema
    definitions =
      -- Here T2 depends on T1 (and not vice-versa) but we intentionally provide them out of order
      -- to prove that any order is valid.
      definitionsToMap (deriveDefinitions @[Fixture.T1, Fixture.T2, Integer]) SomeSchema

data SomeSchema where
  SomeSchema :: Schema xs -> SomeSchema
