-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

-- | Golden tests pinning the user-visible text of `PlutusTx.Options.ParseError`s.
module Options.Spec where

import PlutusTx.Options (parsePluginOptions, posDumpTimings, posPlcTargetVersion)

import Control.Lens (view)
import Data.Either.Validation (Validation (..))
import Data.Text qualified as Text
import PlutusCore.Version (plcVersion120)
import Test.Tasty.Extras (TestNested, embed, nestedGoldenVsTextM, testNested)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestNested
tests =
  testNested
    "Options"
    [ embed $
        testCase "default target is 1.2.0" $
          case parsePluginOptions [] of
            Success opts -> view posPlcTargetVersion opts @?= plcVersion120
            Failure errs -> error $ show errs
    , testParseErrorGolden "plcParserOptionMalformed" ["target-version=notaversion"]
    , testParseErrorGolden "readOptionMalformed" ["context-level=abc"]
    , testParseErrorGolden "fromReadOptionMalformed" ["verbosity=abc"]
    , testTimingOption "timings disabled by default" [] False
    , testTimingOption "enable timing output" ["dump-timings"] True
    , testTimingOption "disable timing output explicitly" ["dump-timings", "no-dump-timings"] False
    ]

testTimingOption :: String -> [String] -> Bool -> TestNested
testTimingOption name options expected = embed $
  testCase name $
    case parsePluginOptions options of
      Success parsed -> view posDumpTimings parsed @?= expected
      Failure errors -> error (show errors)

testParseErrorGolden :: String -> [String] -> TestNested
testParseErrorGolden name opts =
  nestedGoldenVsTextM name "" $
    case parsePluginOptions opts of
      Success _ -> error "Expected parse failure, but parsing succeeded"
      Failure errs -> pure $ Text.pack (show errs)
