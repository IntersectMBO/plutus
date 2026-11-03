{-# LANGUAGE TypeApplications #-}

module Transform.EvaluateBuiltins.Spec where

import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Char8 qualified as BS8
import PlutusCore qualified as PLC
import PlutusCore.Data (Data (I))
import PlutusCore.MkPlc (mkConstant)
import PlutusPrelude (Default (def))
import Test.Tasty (TestTree, testGroup)
import Transform.Lib (app, builtin, builtinTrue, con, delay, err, force, ite, lam, text, var)
import Transform.Simplify.Lib (goldenVsPretty)
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
      , ("ifThenElseErrorArg", ifThenElseErrorArgTerm)
      , ("ifThenElseImpureArg", ifThenElseImpureArgTerm)
      , ("chooseListImpureArg", chooseListImpureArgTerm)
      , ("chooseDataImpureArg", chooseDataImpureArgTerm)
      , ("ifThenElseVarArg", ifThenElseVarArgTerm)
      , ("ifThenElseDelayedErrorArg", ifThenElseDelayedErrorArgTerm)
      , ("ifThenElseNestedFoldableArg", ifThenElseNestedFoldableArgTerm)
      ]
      ++ map
        (uncurry $ goldenVsEvaluated False)
        [ ("traceNonConservative", traceTerm)
        , ("uncompressBlsNonConservative", uncompressBlsG2Term)
        , ("uncompressAndEqualBlsNonConservative", uncompressAndEqualBlsTerm)
        ]

goldenVsEvaluated :: Bool -> String -> Term Name DefaultUni DefaultFun () -> TestTree
goldenVsEvaluated conservative testName =
  goldenVsPretty ".golden.uplc" ("EvaluateBuiltins/" ++ testName)
    . runEvaluateBuiltins conservative

runEvaluateBuiltins
  :: Bool
  -> Term Name DefaultUni DefaultFun ()
  -> Term Name DefaultUni DefaultFun ()
runEvaluateBuiltins conservative = evalOptimizer . evaluateBuiltinsPass conservative def def

addIntegerTerm :: Term Name DefaultUni DefaultFun ()
addIntegerTerm = builtin PLC.AddInteger `app` con 1 `app` con 2

ifThenElseTerm :: Term Name DefaultUni DefaultFun ()
ifThenElseTerm = ite builtinTrue (con 1) (con 2)

-- Used for both traceConservative (unchanged) and traceNonConservative (reduced to 1)
traceTerm :: Term Name DefaultUni DefaultFun ()
traceTerm = force (builtin PLC.Trace) `app` text "hello" `app` con 1

-- Division by zero; evaluates to error so should be left in place
failingBuiltinTerm :: Term Name DefaultUni DefaultFun ()
failingBuiltinTerm = builtin PLC.DivideInteger `app` con 1 `app` con 0

-- The variable argument prevents evaluation
nonConstantArgTerm :: Term Name DefaultUni DefaultFun ()
nonConstantArgTerm = builtin PLC.AddInteger `app` var "x" `app` con 2

-- ifThenElse returns a function (lambda), then applied to an extra argument
overApplicationTerm :: Term Name DefaultUni DefaultFun ()
overApplicationTerm = ite builtinTrue (lam "x" (con 1)) (lam "x" (con 2)) `app` con 3

-- Missing an argument, should be left unchanged
underApplicationTerm :: Term Name DefaultUni DefaultFun ()
underApplicationTerm = builtin PLC.AddInteger `app` con 1

-- In both conservative and non-conservative mode: left unchanged because the
-- result (a G2 element) is an unserializable constant
uncompressBlsG2Term :: Term Name DefaultUni DefaultFun ()
uncompressBlsG2Term =
  builtin PLC.Bls12_381_G2_uncompress `app` mkConstant @BS.ByteString () blsG2Bytes
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
  builtin PLC.Bls12_381_G1_equal
    `app` (builtin PLC.Bls12_381_G1_uncompress `app` blsG1BytesTerm)
    `app` (builtin PLC.Bls12_381_G1_uncompress `app` blsG1BytesTerm)
  where
    blsG1BytesTerm =
      mkConstant @BS.ByteString () $
        decodeHex
          "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"

-- Fails when x is 0, so must not be discarded. See Note [Evaluating builtins with
-- impure arguments] in PlutusIR.Transform.EvaluateBuiltins
impureTerm :: Term Name DefaultUni DefaultFun ()
impureTerm = builtin PLC.DivideInteger `app` con 1 `app` var "x"

-- The unselected branch is an error, so should be left in place
ifThenElseErrorArgTerm :: Term Name DefaultUni DefaultFun ()
ifThenElseErrorArgTerm = ite builtinTrue (con 7) err

-- The unselected branch may fail, so should be left in place
ifThenElseImpureArgTerm :: Term Name DefaultUni DefaultFun ()
ifThenElseImpureArgTerm = ite builtinTrue (con 7) impureTerm

-- The unselected branch may fail, so should be left in place
chooseListImpureArgTerm :: Term Name DefaultUni DefaultFun ()
chooseListImpureArgTerm =
  force (force (builtin PLC.ChooseList))
    `app` mkConstant @[Integer] () []
    `app` con 7
    `app` impureTerm

-- The unselected branches may fail, so should be left in place
chooseDataImpureArgTerm :: Term Name DefaultUni DefaultFun ()
chooseDataImpureArgTerm =
  force (builtin PLC.ChooseData)
    `app` mkConstant @Data () (I 0)
    `app` impureTerm
    `app` impureTerm
    `app` impureTerm
    `app` con 7
    `app` impureTerm

-- Variables are bound to values, so this reduces to 7
ifThenElseVarArgTerm :: Term Name DefaultUni DefaultFun ()
ifThenElseVarArgTerm = ite builtinTrue (con 7) (var "x")

-- Delayed terms are values, so this reduces to 7
ifThenElseDelayedErrorArgTerm :: Term Name DefaultUni DefaultFun ()
ifThenElseDelayedErrorArgTerm = ite builtinTrue (con 7) (delay err)

-- The inner application is folded first, after which this reduces to 7
ifThenElseNestedFoldableArgTerm :: Term Name DefaultUni DefaultFun ()
ifThenElseNestedFoldableArgTerm = ite builtinTrue (con 7) (builtin PLC.AddInteger `app` con 1 `app` con 2)

decodeHex :: String -> BS.ByteString
decodeHex hex = case Base16.decode (BS8.pack hex) of
  Right bs -> bs
  Left e -> error $ "Transform.EvaluateBuiltins.Spec: invalid hex: " <> e
