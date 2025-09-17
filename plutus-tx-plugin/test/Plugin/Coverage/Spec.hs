-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin -fplugin-opt PlutusTx.Plugin:coverage-all #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module Plugin.Coverage.Spec (coverage) where

import Control.Lens

import Data.Map qualified as Map
import Data.Proxy
import Data.Set (Set)
import Data.Set qualified as Set
import PlutusTx.Code
import PlutusTx.Coverage
import PlutusTx.Plugin
import PlutusTx.Prelude qualified as P
import PlutusTx.Test
import Prelude as Haskell

import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.HUnit

noBool :: CompiledCode (() -> ())
noBool = plc (Proxy @"noBool") (\() -> ())

boolTrueFalse :: CompiledCode (() -> Bool)
boolTrueFalse = plc (Proxy @"boolTrueFalse") (\() -> True && False)

boolOtherFunction :: CompiledCode (Maybe Integer -> Maybe Bool)
boolOtherFunction = plc (Proxy @"boolOtherFunction") fun

fun :: Maybe Integer -> Maybe Bool
fun x = case x of
  Just y | otherFun y -> Just False
  _                   -> Nothing
{-# INLINEABLE fun #-}

otherFun :: Integer -> Bool
otherFun x = (x P.== 5) && True

boolQualifiedDisappears :: CompiledCode (() -> Bool)
boolQualifiedDisappears = plc (Proxy @"boolQualifiedDisappears") (\() -> Haskell.True)

coverage :: TestNested
coverage =
  testNested "Coverage" . pure $
    testNestedGhc
      [ embed $
          testGroup
            "Application heads and line coverage"
            [ mkTests "noBool" noBool Set.empty [31]
            , mkTests "boolTrueFalse" boolTrueFalse (Set.singleton "&&") [34]
            , mkTests "boolOtherFunction" boolOtherFunction (Set.fromList ["&&", "=="]) [37, 40, 41, 46]
            , mkTests "boolQualifiedDisappears" boolQualifiedDisappears Set.empty [49]
            ]
      , goldenPirReadable "coverageCode" boolOtherFunction
      ]

mkTests :: String -> CompiledCode t -> Set String -> [Int] -> TestTree
mkTests nm cc heads ls = testGroup nm [applicationHeadsCorrect cc heads, linesInCoverageIndex cc ls]

applicationHeadsCorrect :: CompiledCode t -> Set String -> TestTree
applicationHeadsCorrect cc heads = testCase "correct application heads" (assertEqual "" heads headSymbols)
 where
  headSymbols :: Set String
  headSymbols =
    -- TODO: This should really use a prism instead of going to and from lists I guess
    Set.fromList $
      [ s
      | covMeta <- cc ^. to getCovIdx . coverageMetadata . to Map.elems
      , ApplicationHeadSymbol s <- Set.toList $ covMeta ^. metadataSet
      ]

linesInCoverageIndex :: CompiledCode t -> [Int] -> TestTree
linesInCoverageIndex cc ls =
  testCase
    "correct line coverage"
    (assertBool ("Lines " ++ show ls ++ " are not covered by " ++ show covLineSpans) covered)
 where
  covered = all (\l -> any (\(s, e) -> s <= l && l <= e) covLineSpans) ls
  covLineSpans =
    [ (covLoc ^. covLocStartLine, covLoc ^. covLocEndLine)
    | CoverLocation covLoc <- cc ^. to getCovIdx . coverageMetadata . to Map.keys
    ]
