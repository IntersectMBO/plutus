-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

-- | Golden tests pinning the user-visible text of `PlutusTx.Options.ParseError`s.
module Options.Spec where

import PlutusTx.Options (parsePluginOptions)

import Data.Either.Validation (Validation (..))
import Data.Text qualified as Text
import Test.Tasty.Extras (TestNested, nestedGoldenVsTextM, testNested)

tests :: TestNested
tests =
  testNested
    "Options"
    [ testParseErrorGolden "plcParserOptionMalformed" ["target-version=notaversion"]
    , testParseErrorGolden "readOptionMalformed" ["context-level=abc"]
    , testParseErrorGolden "fromReadOptionMalformed" ["verbosity=abc"]
    ]

testParseErrorGolden :: String -> [String] -> TestNested
testParseErrorGolden name opts =
  nestedGoldenVsTextM name "" $
    case parsePluginOptions opts of
      Success _ -> error "Expected parse failure, but parsing succeeded"
      Failure errs -> pure $ Text.pack (show errs)
