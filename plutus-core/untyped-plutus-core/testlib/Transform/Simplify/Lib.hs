{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Transform.Simplify.Lib where

import Control.Lens ((&), (.~))
import Data.ByteString.Lazy qualified as BSL
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.Tuple.Extra ((&&&))
import PlutusCore qualified as PLC
import PlutusCore.Builtin (BuiltinSemanticsVariant)
import PlutusCore.Pretty (PrettyPlc, Render (render), prettyPlcReadableSimple)
import PlutusPrelude (Default (def))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import UntypedPlutusCore
  ( CseWhichSubterms
  , Name
  , SimplifierTrace
  , Term
  , defaultSimplifyOpts
  , runSimplifierT
  , soCseWhichSubterms
  , soInlineCallsiteGrowth
  , soMaxCseIterations
  , soMaxSimplifierIterations
  , soPreserveLogging
  , termSimplifier
  )
import UntypedPlutusCore.Transform.Certify.Hints qualified as Hints
import UntypedPlutusCore.Transform.Certify.Trace qualified as Trace

-- TODO Fix duplication with other golden tests, quite annoying
goldenVsPretty :: PrettyPlc a => String -> String -> a -> TestTree
goldenVsPretty extn name value =
  goldenVsString name ("untyped-plutus-core/test/Transform/" ++ name ++ extn) $
    pure . BSL.fromStrict . encodeUtf8 . render $
      prettyPlcReadableSimple value

goldenVsSimplified :: String -> Term Name PLC.DefaultUni PLC.DefaultFun () -> TestTree
goldenVsSimplified name t =
  testGroup
    name
    [ goldenVsPretty ".golden.uplc" name t'
    , goldenVsString (name ++ ".certifier-hints") hintsPath
        . pure
        . BSL.fromStrict
        . encodeUtf8
        $ renderCertifierHints trace
    ]
  where
    (t', trace) = PLC.runQuote (testSimplify t)
    hintsPath = "untyped-plutus-core/test/Transform/" ++ name ++ ".golden.certifier-hints"

renderCertifierHints :: Trace.SimplifierTrace Name PLC.DefaultUni PLC.DefaultFun () -> Text
renderCertifierHints (Trace.SimplifierTrace ss)
  | null ss = "<no certifier hints in trace>"
  | otherwise =
      T.unlines $
        zipWith
          renderHintsWithIdx
          [(1 :: Int) ..]
          ((Trace.stage &&& Trace.hints) <$> reverse ss)
  where
    renderHintsWithIdx i (st, h) =
      ("-- Certifier hints #" <> T.pack (show i) <> " (" <> T.pack (show st) <> ") --\n")
        <> renderHints h
        <> "\n"

    renderHints = \case
      Hints.NoHints -> "NoHints"
      Hints.Inline h -> renderInlineHints 0 h

    renderInlineHints i = \case
      Hints.InlVar -> line i "InlVar"
      Hints.InlLam body -> line i "InlLam" <> renderInlineHints (i + 2) body
      Hints.InlApply fun arg ->
        line i "InlApply"
          <> renderInlineHints (i + 2) fun
          <> renderInlineHints (i + 2) arg
      Hints.InlDelay body -> line i "InlDelay" <> renderInlineHints (i + 2) body
      Hints.InlForce body -> line i "InlForce" <> renderInlineHints (i + 2) body
      Hints.InlCon -> line i "InlCon"
      Hints.InlBuiltin -> line i "InlBuiltin"
      Hints.InlError -> line i "InlError"
      Hints.InlConstr args ->
        line i "InlConstr" <> foldMap (renderInlineHints (i + 2)) args
      Hints.InlCase scrut alts ->
        line i "InlCase"
          <> renderInlineHints (i + 2) scrut
          <> foldMap (renderInlineHints (i + 2)) alts
      Hints.InlExpand x -> line i "InlExpand" <> renderInlineHints (i + 2) x
      Hints.InlDrop x -> line i "InlDrop" <> renderInlineHints (i + 2) x

    line i payload = T.replicate i " " <> payload <> "\n"

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

goldenVsCse
  :: CseWhichSubterms
  -> String
  -> Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> TestTree
goldenVsCse whichSubterms name =
  goldenVsPretty ".golden.uplc" name
    . PLC.runQuote
    . fmap fst
    . testCse whichSubterms

testCse
  :: CseWhichSubterms
  -> Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> PLC.Quote
       ( Term Name PLC.DefaultUni PLC.DefaultFun ()
       , SimplifierTrace Name PLC.DefaultUni PLC.DefaultFun ()
       )
testCse whichSubterms =
  runSimplifierT
    . termSimplifier
      ( defaultSimplifyOpts
          -- Just run one iteration, to see what that does
          & soMaxSimplifierIterations .~ 0
          & soMaxCseIterations .~ 1
          & soCseWhichSubterms .~ whichSubterms
          & soInlineCallsiteGrowth .~ 0
          & soPreserveLogging .~ False
      )
      (def :: BuiltinSemanticsVariant PLC.DefaultFun)
