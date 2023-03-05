{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.BLS12_381
    (test_BLS12_381)
where

import Evaluation.Builtins.BLS12_381.Haskell.G1 as Haskell.G1
import Evaluation.Builtins.BLS12_381.Haskell.G2 as Haskell.G2
import Evaluation.Builtins.BLS12_381.Haskell.Pairing as Haskell.Pairing

import Evaluation.Builtins.BLS12_381.Plutus.G1 as Plutus.G1
import Evaluation.Builtins.BLS12_381.Plutus.G2 as Plutus.G2
import Evaluation.Builtins.BLS12_381.Plutus.Pairing as Plutus.Pairing

import Test.Tasty

{-

import Text.Show.Pretty (ppShow)
  import Data.Kind (Type)
  import Test.Tasty
  import Test.Tasty.Hedgehog
  import Test.Tasty.HUnit
  import PlutusPrelude
-}


{- TODO:
    * Check the first three bits of compressed points
    * Unit tests for known values.
-}

---------------- Test groups ----------------

test_haskell :: TestTree
test_haskell =
    testGroup "BLS12-381 (Haskell)"
    [ Haskell.G1.tests
    , Haskell.G2.tests
    , Haskell.Pairing.tests
    ]

test_plutus :: TestTree
test_plutus =
    testGroup "BLS12-381 (Plutus)"
    [ Plutus.G1.tests
    , Plutus.G2.tests
    , Plutus.Pairing.tests
    ]

test_BLS12_381 :: TestTree
test_BLS12_381 =
    testGroup "BLS12-381"
    [ test_haskell
    , test_plutus
    ]
