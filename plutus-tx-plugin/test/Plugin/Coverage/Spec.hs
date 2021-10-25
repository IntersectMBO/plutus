{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin -fplugin-opt PlutusTx.Plugin:coverage-all #-}
{-# OPTIONS_GHC -g #-}

module Plugin.Coverage.Spec (coverage) where

import           Control.Lens

import qualified Data.Map          as Map
import           Data.Proxy
import           Data.Set          (Set)
import qualified Data.Set          as Set
import           PlutusTx.Code
import           PlutusTx.Coverage
import           PlutusTx.Plugin
import qualified PlutusTx.Prelude  as P
import           Prelude           as Haskell

import           Test.Tasty
import           Test.Tasty.HUnit

coverage :: TestTree
coverage = testGroup "Coverage" [ applicationHeads ]

applicationHeads :: TestTree
applicationHeads = testGroup "Correct application heads"
  [ applicationHeadsCorrect "noBool" noBool Set.empty
  , applicationHeadsCorrect "boolTrueFalse" boolTrueFalse (Set.singleton "&&")
  , applicationHeadsCorrect "boolOtherFunction" boolOtherFunction (Set.fromList ["&&", "==", "otherFun"])
  , applicationHeadsCorrect "boolOtherFunctionSimplifiesAway" boolOtherFunctionSimplifiesAway (Set.fromList ["&&", "=="])
  , applicationHeadsCorrect "boolQualifiedDisappears" boolQualifiedDisappears Set.empty
  ]

applicationHeadsCorrect :: String -> CompiledCode t -> Set String -> TestTree
applicationHeadsCorrect nm cc heads = testCase nm (assertEqual "" heads headSymbols)
  where
    headSymbols :: Set String
    headSymbols =
      -- TODO: This should really use a prism instead of going to and from lists I guess
      Set.fromList $ [ s
                     | covMeta <- cc ^. to getCovIdx . coverageMetadata . to Map.elems
                     , ApplicationHeadSymbol s <- Set.toList $ covMeta ^. metadataSet ]

noBool :: CompiledCode (() -> ())
noBool = plc (Proxy @"noBool") (\() -> ())

boolTrueFalse :: CompiledCode (() -> Bool)
boolTrueFalse = plc (Proxy @"boolTrueFalse") (\() -> True && False)

boolOtherFunction :: CompiledCode (Maybe Integer -> Maybe Bool)
boolOtherFunction = plc (Proxy @"boolOtherFunction") fun

{-# INLINEABLE fun #-}
fun :: Maybe Integer -> Maybe Bool
fun x = case x of
  Just y | otherFun y -> Just False
  _                   -> Nothing

otherFun :: Integer -> Bool
otherFun x = (x P.== 5) && True

boolOtherFunctionSimplifiesAway :: CompiledCode (Integer -> Bool)
boolOtherFunctionSimplifiesAway = plc (Proxy @"boolOtherFunctionSimplfiesAway") (\x -> otherFun x)

boolQualifiedDisappears :: CompiledCode (() -> Bool)
boolQualifiedDisappears = plc (Proxy @"boolQualifiedDisappears") (\ () -> Haskell.True)
