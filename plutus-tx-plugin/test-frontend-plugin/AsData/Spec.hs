{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

{-| Activation test for the Plinth @deriving via@ pass.

This module is compiled with the Plinth plugin (@-fplugin Plinth.Plugin@), into
which the deriving pass is wired. The plugin must rewrite the
@deriving AsData via Plinth@ clause below into a @BuiltinData@-backed newtype
plus bidirectional pattern synonyms @Circle@/@Rectangle@ (and inject the
@PlutusTx.*@ imports the generated code uses).

If the deriving pass does /not/ fire, the clause survives to the renamer —
where @AsData@ is not a real class and the @Circle@ synonym does not exist — so
this module fails to compile. Thus successful compilation /is/ the test.
-}
module AsData.Spec (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

data Shape
  = Circle Integer
  | Rectangle Integer Integer
  deriving AsData via Plinth

-- | These reference both plugin-generated pattern synonyms (so neither is
-- flagged unused under @-Werror@). The trailing wildcard makes each match
-- total and non-overlapping regardless of the generated @COMPLETE@ pragma,
-- so they do not trip @-Werror@ on incomplete/overlapping patterns either.
isCircle :: Shape -> Bool
isCircle (Circle _) = True
isCircle _          = False

isRectangle :: Shape -> Bool
isRectangle (Rectangle _ _) = True
isRectangle _               = False

tests :: TestTree
tests =
  testGroup
    "AsData via Plinth"
    [ testCase "plugin fires; generated synonyms construct and match" $ do
        isCircle (Circle 1) @?= True
        isRectangle (Circle 1) @?= False
        isRectangle (Rectangle 2 3) @?= True
    ]
