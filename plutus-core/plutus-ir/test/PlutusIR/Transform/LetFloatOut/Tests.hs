{-# LANGUAGE TypeApplications #-}
module PlutusIR.Transform.LetFloatOut.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Name
import PlutusCore.Quote
import PlutusIR.Error as PIR
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.LetFloatOut qualified as LetFloatOut
import PlutusIR.Transform.LetMerge qualified as LetMerge
import PlutusIR.Transform.RecSplit qualified as RecSplit
import PlutusIR.Transform.Rename ()
import PlutusIR.TypeCheck as TC
import PlutusPrelude

import PlutusCore.Builtin
import PlutusCore.Default
import PlutusIR.Analysis.Builtins
import PlutusIR.Properties.Typecheck (pureTypecheckProp)
import Test.QuickCheck.Property (Property, withMaxSuccess)
import Test.Tasty.QuickCheck (testProperty)

test_letFloatOut :: TestTree
test_letFloatOut = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "LetFloatOut" $
        map
            (goldenPirM goldenFloatTC pTerm)
            [ "letInLet"
            , "listMatch"
            , "maybe"
            , "ifError"
            , "mutuallyRecursiveTypes"
            , "mutuallyRecursiveValues"
            , "nonrec1"
            , "nonrec2"
            , "nonrec3"
            , "nonrec4"
            , "nonrec6"
            , "nonrec7"
            , "nonrec8"
            , "nonrec9"
            , "rec1"
            , "rec2"
            , "rec3"
            , "rec4"
            , "nonrecToRec"
            , "nonrecToNonrec"
            , "oldLength"
            , "strictValue"
            , "strictNonValue"
            , "strictNonValue2"
            , "strictNonValue3"
            , "strictValueNonValue"
            , "strictValueValue"
            , "even3Eval"
            , "strictNonValueDeep"
            , "oldFloatBug"
            , "outRhs"
            , "outLam"
            , "inLam"
            , "rhsSqueezeVsNest"
            ]
  where
    goldenFloatTC pir = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
        let pirFloated = RecSplit.recSplit . LetFloatOut.floatTerm def . runQuote $ PLC.rename pir
        -- make sure the floated result typechecks
        _ <- runQuoteT . flip inferType (() <$ pirFloated) =<< TC.getDefTypeCheckConfig ()
        -- letmerge is not necessary for floating, but is a nice visual transformation
        pure $ LetMerge.letMerge pirFloated

-- | Check that a term typechecks after a
-- `PlutusIR.Transform.LetFloatOut.floatTerm` pass.
typecheck_floatTerm_prop :: BuiltinSemanticsVariant PLC.DefaultFun -> Property
typecheck_floatTerm_prop biVariant =
  pureTypecheckProp $ LetFloatOut.floatTerm (BuiltinsInfo biVariant)

test_typecheck :: TestTree
test_typecheck = testGroup "typechecking"
  [ testProperty "Builtin Variant 1" $
      withMaxSuccess 3000 $ typecheck_floatTerm_prop DefaultFunSemanticsVariant1
  , testProperty "Builtin Variant 1" $
      withMaxSuccess 3000 $ typecheck_floatTerm_prop DefaultFunSemanticsVariant2
  ]

