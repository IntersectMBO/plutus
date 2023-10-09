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
