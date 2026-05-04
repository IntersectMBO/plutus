{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Transform.EvaluateBuiltins.Spec where

import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Char8 qualified as BS8
import Data.ByteString.Lazy qualified as BSL
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant, mkIterApp)
import PlutusCore.Pretty (Render (render), prettyPlcReadableSimple)
import PlutusCore.Quote (freshName, runQuote)
import PlutusPrelude (Default (def))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import UntypedPlutusCore (DefaultFun, DefaultUni, Name, Term (..))
import UntypedPlutusCore.Transform.EvaluateBuiltins (evaluateBuiltinsPass)
import UntypedPlutusCore.Transform.Optimizer (evalOptimizer)

test_evaluateBuiltins :: TestTree
test_evaluateBuiltins =
  testGroup "EvaluateBuiltins" $
    map
      (uncurry $ goldenVsEvaluated True)
      [ ("addInteger", addIntegerTerm)
      , ("ifThenElse", ifThenElseTerm)
      , ("traceConservative", traceTerm)
      , ("failingBuiltin", failingBuiltinTerm)
      , ("nonConstantArg", nonConstantArgTerm)
      , ("overApplication", overApplicationTerm)
      , ("underApplication", underApplicationTerm)
      , ("uncompressBlsConservative", uncompressBlsG2Term)
      ]
      ++ map
        (uncurry $ goldenVsEvaluated False)
        [ ("traceNonConservative", traceTerm)
        , ("uncompressBlsNonConservative", uncompressBlsG2Term)
        , ("uncompressAndEqualBlsNonConservative", uncompressAndEqualBlsTerm)
        ]

goldenVsEvaluated :: Bool -> String -> Term Name DefaultUni DefaultFun () -> TestTree
goldenVsEvaluated conservative name term =
  goldenVsString
    name
    ("untyped-plutus-core/test/Transform/EvaluateBuiltins/" ++ name ++ ".golden.uplc")
    . pure
    . BSL.fromStrict
    . encodeUtf8
    . render
    . prettyPlcReadableSimple
    $ runEvaluateBuiltins conservative term

runEvaluateBuiltins
  :: Bool
  -> Term Name DefaultUni DefaultFun ()
  -> Term Name DefaultUni DefaultFun ()
runEvaluateBuiltins conservative = evalOptimizer . evaluateBuiltinsPass conservative def def

addIntegerTerm :: Term Name DefaultUni DefaultFun ()
addIntegerTerm =
  Apply
    ()
    (Apply () (Builtin () PLC.AddInteger) (mkConstant @Integer () 1))
    (mkConstant @Integer () 2)

ifThenElseTerm :: Term Name DefaultUni DefaultFun ()
ifThenElseTerm =
  mkIterApp
    (Force () (Builtin () PLC.IfThenElse))
    [ ((), mkConstant @Bool () True)
    , ((), mkConstant @Integer () 1)
    , ((), mkConstant @Integer () 2)
    ]

-- Used for both traceConservative (unchanged) and traceNonConservative (reduced to 1)
traceTerm :: Term Name DefaultUni DefaultFun ()
traceTerm =
  Apply
    ()
    (Apply () (Force () (Builtin () PLC.Trace)) (mkConstant @Text () "hello"))
    (mkConstant @Integer () 1)

-- Division by zero; evaluates to error so should be left in place
failingBuiltinTerm :: Term Name DefaultUni DefaultFun ()
failingBuiltinTerm =
  Apply
    ()
    (Apply () (Builtin () PLC.DivideInteger) (mkConstant @Integer () 1))
    (mkConstant @Integer () 0)

-- The variable argument prevents evaluation
nonConstantArgTerm :: Term Name DefaultUni DefaultFun ()
nonConstantArgTerm = runQuote $ do
  x <- freshName "x"
  pure $
    Apply
      ()
      (Apply () (Builtin () PLC.AddInteger) (Var () x))
      (mkConstant @Integer () 2)

-- ifThenElse returns a function (lambda), then applied to an extra argument
overApplicationTerm :: Term Name DefaultUni DefaultFun ()
overApplicationTerm = runQuote $ do
  x <- freshName "x"
  pure $
    Apply
      ()
      ( mkIterApp
          (Force () (Builtin () PLC.IfThenElse))
          [ ((), mkConstant @Bool () True)
          , ((), LamAbs () x (mkConstant @Integer () 1))
          , ((), LamAbs () x (mkConstant @Integer () 2))
          ]
      )
      (mkConstant @Integer () 3)

-- Missing an argument, should be left unchanged
underApplicationTerm :: Term Name DefaultUni DefaultFun ()
underApplicationTerm =
  Apply () (Builtin () PLC.AddInteger) (mkConstant @Integer () 1)

-- In both conservative and non-conservative mode: left unchanged because the
-- result (a G2 element) is an unserializable constant
uncompressBlsG2Term :: Term Name DefaultUni DefaultFun ()
uncompressBlsG2Term =
  Apply () (Builtin () PLC.Bls12_381_G2_uncompress) (mkConstant @BS.ByteString () blsG2Bytes)
  where
    blsG2Bytes =
      decodeHex
        ( "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
            ++ "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
        )

-- In non-conservative mode: left unchanged because intermediate results
-- (G1 elements) are unserializable, so we can't evaluate through them
uncompressAndEqualBlsTerm :: Term Name DefaultUni DefaultFun ()
uncompressAndEqualBlsTerm =
  Apply
    ()
    ( Apply
        ()
        (Builtin () PLC.Bls12_381_G1_equal)
        (Apply () (Builtin () PLC.Bls12_381_G1_uncompress) blsG1BytesTerm)
    )
    (Apply () (Builtin () PLC.Bls12_381_G1_uncompress) blsG1BytesTerm)
  where
    blsG1BytesTerm =
      mkConstant @BS.ByteString () $
        decodeHex
          "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"

decodeHex :: String -> BS.ByteString
decodeHex hex = case Base16.decode (BS8.pack hex) of
  Right bs -> bs
  Left err -> error $ "Transform.EvaluateBuiltins.Spec: invalid hex: " <> err
