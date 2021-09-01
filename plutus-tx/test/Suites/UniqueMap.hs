
{-# LANGUAGE TypeApplications #-}

module Suites.UniqueMap (tests) where

import           PlutusTx.Arbitrary    ()
import qualified PlutusTx.Prelude      as P
import           PlutusTx.UniqueMap    (UniqueMap)
import qualified PlutusTx.UniqueMap    as UniqueMap
import           Prelude
import           Test.QuickCheck       (Property, arbitrary, forAllShrink, shrink, (===))
import           Test.Tasty            (TestTree, localOption)
import           Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

tests :: [TestTree]
tests =
  [ localOption go . testProperty "Put-get" $ putGetProp
  , localOption go . testProperty "Put-put" $ putPutProp
  , localOption go . testProperty "Get from empty" $ getEmptyProp
  , localOption (go `quot` 8) . testProperty "Semigroup laws" $ semigroupLawsProp
  ]
  where
    go :: QuickCheckTests
    go = 100000

-- If we insert a key-value pair into a map, we should be able to retrieve the
-- value.
putGetProp :: Property
putGetProp = forAllShrink arbitrary shrink go
  where
    go ::
      (P.Integer, P.Integer, UniqueMap P.Integer P.Integer) ->
      Property
    go (key, val, um) =
      UniqueMap.lookup key (UniqueMap.insert key val um)
        === Just val

-- If we insert a pair, then insert again under the same key, the second insert
-- wins.
putPutProp :: Property
putPutProp = forAllShrink arbitrary shrink go
  where
    go ::
      (P.Integer, P.Integer, P.Integer, UniqueMap P.Integer P.Integer) ->
      Property
    go (key, val1, val2, um) =
      UniqueMap.insert key val2 (UniqueMap.insert key val1 um)
        === UniqueMap.insert key val2 um

-- We cannot retrieve anything from an empty map.
getEmptyProp :: Property
getEmptyProp = forAllShrink arbitrary shrink go
  where
    go :: P.Integer -> Property
    go key = UniqueMap.lookup key UniqueMap.empty === Nothing @P.Integer

-- Map semigroup operator is associative.
semigroupLawsProp :: Property
semigroupLawsProp = forAllShrink arbitrary shrink $
  \(um1 :: UniqueMap P.Integer [P.Integer], um2, um3) ->
    (um1 P.<> um2) P.<> um3 === um1 P.<> (um2 P.<> um3)
