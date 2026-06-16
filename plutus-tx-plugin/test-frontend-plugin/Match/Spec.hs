{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

{-| Activation test for the @Match@ generator (the CPS destructor).

Compiled with the Plinth plugin, @deriving (AsData, Match) via Plinth@ must
produce the @Circle@/@Rectangle@ pattern synonyms /and/ a destructor

> matchShape :: Shape -> (Integer -> r) -> (Integer -> Integer -> r) -> r

'firstField' constructs values via the AsData synonyms and destructures them
via @matchShape@, exercising both continuations and the (now head/tail-free)
field decoding. If the plugin does not fire, @matchShape@ is undefined and this
module fails to compile.
-}
module Match.Spec (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

data Shape
  = Circle Integer
  | Rectangle Integer Integer
  deriving (AsData, Match) via Plinth

firstField :: Shape -> Integer
firstField s = matchShape s (\r -> r) (\w _ -> w)

tests :: TestTree
tests =
  testGroup
    "Match via Plinth"
    [ testCase "matchShape dispatches on the tag and decodes fields" $ do
        firstField (Circle 7) @?= 7
        firstField (Rectangle 3 5) @?= 3
    ]
