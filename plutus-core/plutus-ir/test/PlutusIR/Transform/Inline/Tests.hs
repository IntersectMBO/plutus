{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
module PlutusIR.Transform.Inline.Tests where

import Test.Tasty
import Test.Tasty.Extras

import Control.Monad.Except
import PlutusCore qualified as PLC
import PlutusCore.Quote
import PlutusIR
import PlutusIR.Check.Uniques qualified as Uniques
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Inline.Inline qualified as Inline
import PlutusPrelude

-- | Tests of the inliner, include global uniqueness test.
test_inline :: TestTree
test_inline = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    let goldenInlineUnique :: Term TyName Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan ->
            IO (Term TyName Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan)
        goldenInlineUnique pir =
            rethrow . asIfThrown @(PLC.UniqueError PLC.SrcSpan) $ do
                let pirInlined = runQuote $ do
                        renamed <- PLC.rename pir
                        Inline.inline mempty def renamed
                -- Make sure the inlined term is globally unique.
                _ <- checkUniques pirInlined
                pure pirInlined
    in
    testNested "Inline" $
        map
            (goldenPirM goldenInlineUnique pTerm)
            [ "var"
            , "builtin"
            , "callsite-non-trivial-body"
            , "constant"
            , "transitive"
            , "tyvar"
            , "single"
            , "immediateVar"
            , "immediateApp"
            , "firstEffectfulTerm1"
            , "firstEffectfulTerm2"
            -- these tests are all let bindings of functions
            , "letFunConstInt" -- const fn fully applied (integer)
            , "letFunConstBool" -- const fn fully applied (bool)
            , "letFunConstMulti" -- multiple occurrences of a let binding of the const fn.
            , "letFunInFun" -- fully applied fn inside another let, single occurrence.
            , "letFunInFunMulti" -- fully applied fn inside another let, multiple occurrences.
            -- similar to "letFunInFunMulti" but all fns are fully applied.
            , "letTypeAppMulti"
            -- singe occurrence of a polymorphic id function that is fully applied
            , "letTypeApp"
            , "letTypeApp2" -- multiple occurrences of a function with type application
            -- multiple occurrences of a polymorphic id function that IS fully applied
            , "letTypeAppMultiSat"
            -- multiple occurrences of a polymorphic id function that is NOT fully applied
            , "letTypeAppMultiNotSat"
            , "letApp" -- single occurrence of a function application in rhs
            -- multiple occurrences of a function application in rhs with not acceptable body
            , "letAppMultiNotAcceptable"
            , "letOverApp" -- over-application of a function, single occurrence
            , "letOverAppMulti" -- multiple occurrences of an over-application of a function
            -- multiple occurrences of an over-application of a function with type arguments
            , "letOverAppType"
            , "letNonPure" -- multiple occurrences of a non-pure binding
            , "letNonPureMulti"
            , "letNonPureMultiStrict"
            , "rhs-modified"
            , "partiallyApp"
            , "effectfulBuiltinArg"
            ]

-- | Tests that the inliner doesn't incorrectly capture variable names.
test_nameCapture :: TestTree
test_nameCapture = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    let goldenNameCapture :: Term TyName Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan ->
            IO String
        goldenNameCapture pir =
            rethrow . asIfThrown @(PLC.UniqueError PLC.SrcSpan) $ do
                let pirInlined = runQuote $ do
                        renamed <- PLC.rename pir
                        Inline.inline mempty def renamed
                -- Make sure the inlined term is globally unique.
                _ <- checkUniques pirInlined
                pure . render $ prettyPirReadable pirInlined
    in
    testNested "Inline" $
        map
            (goldenPirMUnique goldenNameCapture pTerm)
            [ "nameCapture"]

-- | Check whether a term is globally unique.
checkUniques :: (Ord a, MonadError (PLC.UniqueError a) m) => Term TyName Name uni fun a -> m ()
checkUniques =
    Uniques.checkTerm (\case { Uniques.MultiplyDefined{} -> True; _ -> False})
