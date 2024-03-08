{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Blueprint.Definition.Spec where

import Prelude

import Blueprint.Definition.Fixture qualified as Fixture
import Control.Lens.Plated (universe)
import Data.Map qualified as Map
import Data.Set (isSubsetOf)
import Data.Set qualified as Set
import PlutusTx.Blueprint.Definition (deriveSchemaDefinitions)
import PlutusTx.Blueprint.Schema (Schema (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, testCase, (@?), (@?=))

tests :: TestTree
tests =
  testGroup
    "PlutusTx.Blueprint.Definition"
    [ testCase
        "Derived definitions are empty when no types are provided."
        (deriveSchemaDefinitions @'[] @?= Map.empty)
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
  definitions =
    deriveSchemaDefinitions @[Fixture.T1, Fixture.T2, Integer]

allReferencedDefinitionsAreDefined :: Assertion
allReferencedDefinitionsAreDefined =
  (referencedIds `isSubsetOf` definedIds)
    @? "Not all referenced schema definitions are defined"
 where
  referencedIds =
    Set.fromList
      [ ref
      | schemas <- universe (Map.elems definitions)
      , SchemaDefinitionRef ref <- schemas
      ]
  definedIds =
    Set.fromList (Map.keys definitions)
  definitions =
    -- Here T2 depends on T1 (and not vice-versa) but we intentionally provide them out of order
    -- to prove that any order is valid.
    deriveSchemaDefinitions @[Fixture.T1, Fixture.T2, Integer]
