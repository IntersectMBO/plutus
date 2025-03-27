-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}

module Budget.Spec where

import Test.Tasty.Extras

import Budget.WithGHCOptimisations qualified as WithGHCOptTest
import Budget.WithoutGHCOptimisations qualified as WithoutGHCOptTest
import Data.Set qualified as Set
import PlutusTx.AsData qualified as AsData
import PlutusTx.Builtins qualified as PlutusTx hiding (null)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Code
import PlutusTx.Data.List (List)
import PlutusTx.Data.List qualified as DL
import PlutusTx.Data.List.TH (destructList)
import PlutusTx.Foldable qualified as F
import PlutusTx.IsData qualified as IsData
import PlutusTx.Lift (liftCodeDef, makeLift)
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

AsData.asData [d|
  data MaybeD a = JustD a | NothingD
  |]
makeLift ''MaybeD

tests :: TestNested
tests = testNested "Budget" . pure $ testNestedGhc
  [ goldenUPlcReadable "sum" compiledSum
  , goldenPirReadable "sum" compiledSum
  , goldenSize "sum" compiledSum
  , goldenEvalCekCatch "sum" [compiledSum `unsafeApplyCode` inp]
  , goldenBudget "sum" (compiledSum `unsafeApplyCode` inp)
  , goldenUPlcReadable "sum2" compiledSum2
  , goldenPirReadable "sum2" compiledSum2
  , goldenEvalCekCatch "sum2" [compiledSum2 `unsafeApplyCode` inp]
  , goldenBudget "sum2" (compiledSum2 `unsafeApplyCode` inp)
  , goldenSize "sum2" compiledSum2
  ]

compiledSum :: CompiledCode (PlutusTx.BuiltinData ->  Integer)
compiledSum = $$(compile [|| \d ->
      DL.length @Integer (PlutusTx.unsafeFromBuiltinData d) ||])


compiledSum2 :: CompiledCode (PlutusTx.BuiltinData ->  Integer)
compiledSum2 = $$(compile [|| \d ->
      DL.length2 @Integer (PlutusTx.unsafeFromBuiltinData d) ||])



inp :: CompiledCode PlutusTx.BuiltinData
inp = liftCodeDef (PlutusTx.toBuiltinData (DL.fromSOP ([1..10] :: [Integer])))
