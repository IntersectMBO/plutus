{-# LANGUAGE OverloadedStrings #-}

module Ual.Error.Spec (tests) where

import Prelude

import PlutusTx.Ual.Error (UalError (..), renderUalError)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

{-| Every case interpolates its arguments, and several take two or three of the
same type, so a swapped pair would be invisible without pinning the wording.
The arguments below are chosen to be distinguishable from each other. -}
tests :: TestTree
tests =
  testGroup
    "Error"
    [ testCase "UnterminatedBlock" $
        renderUalError (UnterminatedBlock 7)
          @?= "line 7: unterminated '{-@' block: no '@-}' found"
    , testCase "UnknownBlockKind" $
        renderUalError (UnknownBlockKind 3 "NOPE")
          @?= "line 3: unknown UAL block kind 'NOPE'; expected one of "
            <> "ONCHAIN, PREDICATE, PROPERTY, UPLC_DATA"
    , testCase "ArityMismatch keeps declared before actual" $
        renderUalError (ArityMismatch "spend" 3 2)
          @?= "ONCHAIN 'spend': signature declares 3 argument(s) "
            <> "but the Haskell type has 2"
    , testCase "VersionMismatch keeps declared before preamble" $
        renderUalError (VersionMismatch "spend" "v3" "v2")
          @?= "ONCHAIN 'spend': declares version v3 but the blueprint preamble says v2"
    , testCase "UnknownFragment keeps property before fragment" $
        renderUalError (UnknownFragment "no-double-spend" "utxoValid")
          @?= "property 'no-double-spend' uses unknown fragment 'utxoValid'"
    , testCase "FragmentCycle joins the cycle in order" $
        renderUalError (FragmentCycle ["a", "b", "a"])
          @?= "cycle in fragment imports: a -> b -> a"
    ]
