{-# LANGUAGE OverloadedStrings #-}

module Transform.Simplify.Lib where

import Control.Lens ((&), (.~))
import Data.ByteString.Lazy qualified as BSL
import Data.Text.Encoding (encodeUtf8)
import PlutusCore qualified as PLC
import PlutusCore.Builtin (BuiltinSemanticsVariant)
import PlutusCore.Pretty (PrettyPlc, Render (render), prettyPlcReadableSimple)
import PlutusPrelude (Default (def))
import Test.Tasty (TestTree)
import Test.Tasty.Golden (goldenVsString)
import UntypedPlutusCore (Name, SimplifierTrace, Term, defaultSimplifyOpts, runSimplifierT,
                          soInlineCallsiteGrowth, soMaxCseIterations, soMaxSimplifierIterations,
                          soPreserveLogging, termSimplifier)

-- TODO Fix duplication with other golden tests, quite annoying
goldenVsPretty :: (PrettyPlc a) => String -> String -> a -> TestTree
goldenVsPretty extn name value =
  goldenVsString name ("untyped-plutus-core/test/Transform/" ++ name ++ extn) $
    pure . BSL.fromStrict . encodeUtf8 . render $
      prettyPlcReadableSimple value

goldenVsSimplified :: String -> Term Name PLC.DefaultUni PLC.DefaultFun () -> TestTree
goldenVsSimplified name =
  goldenVsPretty ".golden.uplc" name
    . PLC.runQuote
    . fmap fst
    . testSimplify

testSimplify
  :: Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> PLC.Quote
      ( Term Name PLC.DefaultUni PLC.DefaultFun ()
      , SimplifierTrace Name PLC.DefaultUni PLC.DefaultFun ()
      )
testSimplify =
    runSimplifierT
    . termSimplifier
      ( defaultSimplifyOpts
          -- Just run one iteration, to see what that does
          & soMaxSimplifierIterations .~ 1
          & soMaxCseIterations .~ 0
          & soInlineCallsiteGrowth .~ 0
          & soPreserveLogging .~ False
      )
      (def :: BuiltinSemanticsVariant PLC.DefaultFun)

goldenVsCse :: String -> Term Name PLC.DefaultUni PLC.DefaultFun () -> TestTree
goldenVsCse name =
  goldenVsPretty ".golden.uplc" name
    . PLC.runQuote
    . fmap fst
    . testCse

testCse
  :: Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> PLC.Quote
      ( Term Name PLC.DefaultUni PLC.DefaultFun ()
      , SimplifierTrace Name PLC.DefaultUni PLC.DefaultFun ()
      )
testCse =
    runSimplifierT
    . termSimplifier
      ( defaultSimplifyOpts
          -- Just run one iteration, to see what that does
          & soMaxSimplifierIterations .~ 0
          & soMaxCseIterations .~ 1
          & soInlineCallsiteGrowth .~ 0
          & soPreserveLogging .~ False
      )
      (def :: BuiltinSemanticsVariant PLC.DefaultFun)
