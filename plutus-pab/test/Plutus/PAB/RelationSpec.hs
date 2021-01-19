{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Plutus.PAB.RelationSpec
    ( tests
    ) where

import           Control.Applicative            (empty, optional)
import           Plutus.PAB.Relation            (Table, fromList, intersection, keys, lookup)
import           Prelude                        hiding (lookup)
import           Test.QuickCheck                (Arbitrary, arbitrary)
import           Test.QuickCheck.Instances.UUID ()
import           Test.Tasty                     (TestTree, testGroup)
import           Test.Tasty.QuickCheck          (testProperty, (===))

tests :: TestTree
tests = testGroup "Plutus.PAB.Relation" [innerJoinTests, outerJoinTests]

innerJoinTests :: TestTree
innerJoinTests =
    testGroup
        "innerJoin"
        [ testProperty "Inner join is the intersection of keys" $ \(t1 :: Table Int String) (t2 :: Table Int String) ->
              keys ((,) <$> t1 <*> t2) === intersection (keys t1) (keys t2)
        , testProperty "Inner join preserves lookup" $ \k (t1 :: Table Int String) (t2 :: Table Int String) ->
              ((,) <$> lookup t1 k <*> lookup t2 k) ===
              lookup ((,) <$> t1 <*> t2) k
        ]

outerJoinTests :: TestTree
outerJoinTests =
    testGroup
        "outerJoin"
        [ testProperty "Optional join preserves mandatory keys" $ \(t1 :: Table Int String) (t2 :: Table Int String) ->
              keys ((,) <$> t1 <*> optional t2) === keys t1
        , testProperty "Outer join preserves lookup" $ \k (t1 :: Table Int String) ->
              (const <$> lookup t1 k <*> optional empty) === lookup t1 k
        ]

instance (Ord k, Arbitrary k, Arbitrary v) => Arbitrary (Table k v) where
    arbitrary = fromList <$> arbitrary
