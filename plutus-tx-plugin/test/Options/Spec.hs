-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

{- | Golden tests for the rendered text of `PlutusTx.Options.ParseError`s.

These tests pin down the user-visible error messages that appear in GHC
output when a plugin option value fails to parse. They cover all three
constructors of `CannotParseValue` (one per parser helper):

* `plcParserOption` — via `target-version`, where the value is parsed by
  the PLC parser. The detail should include the underlying Megaparsec
  error (source position + reason).
* `readOption`      — via `context-level`, which uses `readMaybe`.
* `fromReadOption`  — via `verbosity`, which first reads an `Int`.

If the error text changes, the goldens fail and the change is explicit.
-}
module Options.Spec where

import PlutusTx.Options (parsePluginOptions)

import Data.ByteString.Lazy qualified as BSL
import Data.Either.Validation (Validation (..))
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)

tests :: TestTree
tests =
  testGroup
    "Options"
    [ testOptionsParseErrorGolden
        "plcParserOptionMalformed"
        "test/Options/Golden/plcParserOptionMalformed.golden"
        ["target-version=notaversion"]
    , testOptionsParseErrorGolden
        "readOptionMalformed"
        "test/Options/Golden/readOptionMalformed.golden"
        ["context-level=abc"]
    , testOptionsParseErrorGolden
        "fromReadOptionMalformed"
        "test/Options/Golden/fromReadOptionMalformed.golden"
        ["verbosity=abc"]
    ]

-- | Run `parsePluginOptions` on a single malformed option and compare the
-- rendered `ParseErrors` against a golden file.
testOptionsParseErrorGolden :: String -> FilePath -> [String] -> TestTree
testOptionsParseErrorGolden testName goldenPath opts =
  goldenVsString testName goldenPath $
    case parsePluginOptions opts of
      Success _ -> error "Expected parse failure, but parsing succeeded"
      Failure errs ->
        pure . BSL.fromStrict . Text.encodeUtf8 . Text.pack $ show errs
