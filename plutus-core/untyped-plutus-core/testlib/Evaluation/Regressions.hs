-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Evaluation.Regressions
  ( schnorrVerifyRegressions
  ) where

import Data.Bits (zeroBits)
import Data.ByteString (ByteString)
import Data.List.Split (chunksOf)
import Evaluation.Builtins.Common (typecheckEvaluateCek)
import GHC.Exts (fromListN)
import PlutusCore
  ( DefaultFun (VerifySchnorrSecp256k1Signature)
  , EvaluationResult (EvaluationFailure)
  )
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModelForTesting)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusPrelude
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Text.Read (readMaybe)

schnorrVerifyRegressions :: TestTree
schnorrVerifyRegressions =
  testGroup
    "Schnorr signature verification regressions"
    [ testCase "malformed verkey should fail" $ do
        let badVerKey = "m"
        let message = "\213"
        let comp =
              mkIterAppNoAnn
                (builtin () VerifySchnorrSecp256k1Signature)
                [ mkConstant @ByteString () badVerKey
                , mkConstant @ByteString () message
                , mkConstant @ByteString () signature
                ]
        let result = typecheckEvaluateCek def defaultBuiltinCostModelForTesting comp
        case result of
          Left _ -> assertFailure "Failed to type check unexpectedly"
          Right (res, _) -> assertEqual "" EvaluationFailure res
    ]

-- The original reproducing case is a hex string
-- Unfortunately, ByteString literals are a weird pseudo-ASCII thing
-- Thus, this manual reconstruction
signature :: ByteString
signature = fromListN 64 . fmap go . chunksOf 2 $ "4d83cfb975c5f8b9ba656edb205466bf2c5548f01fc3277427d4ff555df4a996383e171127e82e56fd9bfd0e22df12a004fdac73c67793d97199cc5b223dbe84"
  where
    go :: [Char] -> Word8
    go = fromMaybe zeroBits . readMaybe
