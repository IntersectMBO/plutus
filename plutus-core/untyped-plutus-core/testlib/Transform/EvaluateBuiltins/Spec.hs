{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Transform.EvaluateBuiltins.Spec where

import Control.Lens ((&), (.~))
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Text.Encoding (encodeUtf8)
import PlutusCore qualified as PLC
import PlutusCore.Builtin (BuiltinSemanticsVariant)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModelForTesting)
import PlutusCore.MkPlc (mkConstant, mkIterApp)
import PlutusCore.Pretty (PrettyPlc, Render (render), prettyPlcReadableSimple)
import PlutusPrelude (Default (def))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Transform.Simplify.Lib (renderCertifierHints, testOptimize)
import UntypedPlutusCore
  ( Name
  , OptimizerTrace
  , Term (..)
  , defaultOptimizeOpts
  , ooCertifiedOptsOnly
  , ooInlineCallsiteGrowth
  , ooMaxCseIterations
  , ooMaxSimplifierIterations
  , ooPreserveLogging
  , runOptimizerT
  , termOptimizer
  )

test_evaluateBuiltins :: TestTree
test_evaluateBuiltins =
  testGroup
    "EvaluateBuiltins"
    [ goldenVsOptimized "cfAddInteger" cfAddInteger
    , goldenVsOptimized "cfNested" cfNested
    , goldenVsOptimized "cfIfThenElse" cfIfThenElse
    , goldenVsOptimized "cfEqualsInteger" cfEqualsInteger
    , goldenVsOptimized "cfDivisionByZero" cfDivisionByZero
    , goldenVsOptimized "cfUnderApplied" cfUnderApplied
    , goldenVsOptimized "cfAppendByteString" cfAppendByteString
    , goldenVsCertifiedOnly "cfAppendByteStringCertifiedOnly" cfAppendByteString
    ]

-- | @addInteger 1 2@ — folds to @3@.
cfAddInteger :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cfAddInteger =
  Apply
    ()
    (Apply () (Builtin () PLC.AddInteger) (mkConstant @Integer () 1))
    (mkConstant @Integer () 2)

-- | @addInteger (multiplyInteger 2 3) 4@ — bottom-up folding produces @10@.
cfNested :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cfNested =
  Apply
    ()
    ( Apply
        ()
        (Builtin () PLC.AddInteger)
        ( Apply
            ()
            (Apply () (Builtin () PLC.MultiplyInteger) (mkConstant @Integer () 2))
            (mkConstant @Integer () 3)
        )
    )
    (mkConstant @Integer () 4)

-- | @(force ifThenElse) True 1 2@ — folds to @1@.
cfIfThenElse :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cfIfThenElse =
  mkIterApp
    (Force () (Builtin () PLC.IfThenElse))
    [ ((), mkConstant @Bool () True)
    , ((), mkConstant @Integer () 1)
    , ((), mkConstant @Integer () 2)
    ]

-- | @equalsInteger 3 3@ — folds to @True@.
cfEqualsInteger :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cfEqualsInteger =
  Apply
    ()
    (Apply () (Builtin () PLC.EqualsInteger) (mkConstant @Integer () 3))
    (mkConstant @Integer () 3)

-- | @divideInteger 1 0@ — not folded because evaluation fails.
cfDivisionByZero :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cfDivisionByZero =
  Apply
    ()
    (Apply () (Builtin () PLC.DivideInteger) (mkConstant @Integer () 1))
    (mkConstant @Integer () 0)

-- | @addInteger 1@ — not folded because it is under-applied.
cfUnderApplied :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cfUnderApplied =
  Apply () (Builtin () PLC.AddInteger) (mkConstant @Integer () 1)

{-| @appendByteString "ab" "cd"@ — an uncertified builtin.
Folds to @"abcd"@ in normal mode; left unchanged in certified-only mode
(see 'cfAppendByteStringCertifiedOnly'). -}
cfAppendByteString :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cfAppendByteString =
  Apply
    ()
    ( Apply
        ()
        (Builtin () PLC.AppendByteString)
        (mkConstant @BS.ByteString () "ab")
    )
    (mkConstant @BS.ByteString () "cd")

----------------------------------------------------------------------------------------------------
-- Helpers -----------------------------------------------------------------------------------------

goldenDir :: String
goldenDir = "untyped-plutus-core/test/Transform/EvaluateBuiltins/"

goldenVsOptimized :: String -> Term Name PLC.DefaultUni PLC.DefaultFun () -> TestTree
goldenVsOptimized name t =
  testGroup
    name
    [ goldenVsPretty ".golden.uplc" name t'
    , goldenVsString (name ++ ".certifier-hints") (goldenDir ++ name ++ ".golden.certifier-hints")
        . pure
        . BSL.fromStrict
        . encodeUtf8
        $ renderCertifierHints trace
    ]
  where
    (t', trace) = PLC.runQuote (testOptimize t)

goldenVsCertifiedOnly :: String -> Term Name PLC.DefaultUni PLC.DefaultFun () -> TestTree
goldenVsCertifiedOnly name t =
  testGroup
    name
    [ goldenVsPretty ".golden.uplc" name t'
    , goldenVsString (name ++ ".certifier-hints") (goldenDir ++ name ++ ".golden.certifier-hints")
        . pure
        . BSL.fromStrict
        . encodeUtf8
        $ renderCertifierHints trace
    ]
  where
    (t', trace) = PLC.runQuote (testOptimizeCertifiedOnly t)

goldenVsPretty :: PrettyPlc a => String -> String -> a -> TestTree
goldenVsPretty extn name value =
  goldenVsString name (goldenDir ++ name ++ extn) $
    pure . BSL.fromStrict . encodeUtf8 . render $
      prettyPlcReadableSimple value

testOptimizeCertifiedOnly
  :: Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> PLC.Quote
       ( Term Name PLC.DefaultUni PLC.DefaultFun ()
       , OptimizerTrace Name PLC.DefaultUni PLC.DefaultFun ()
       )
testOptimizeCertifiedOnly =
  runOptimizerT
    . termOptimizer
      ( defaultOptimizeOpts
          & ooMaxSimplifierIterations .~ 1
          & ooMaxCseIterations .~ 0
          & ooInlineCallsiteGrowth .~ 0
          & ooPreserveLogging .~ False
          & ooCertifiedOptsOnly .~ True
      )
      (def :: BuiltinSemanticsVariant PLC.DefaultFun)
      defaultBuiltinCostModelForTesting
