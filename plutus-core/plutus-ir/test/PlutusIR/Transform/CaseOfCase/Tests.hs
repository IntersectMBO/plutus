{-# LANGUAGE TypeApplications #-}
module PlutusIR.Transform.CaseOfCase.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Name
import PlutusCore.Quote
import PlutusIR.Analysis.Builtins
import PlutusIR.Error as PIR
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.CaseOfCase qualified as CaseOfCase
import PlutusIR.TypeCheck as TC
import PlutusPrelude

test_caseOfCase :: TestTree
test_caseOfCase = runTestNestedIn ["plutus-ir", "test", "PlutusIR", "Transform"] $
    testNested "CaseOfCase" $
        map
            (goldenPirM goldenCoCTC pTerm)
            [ "basic"
            , "builtinBool"
            , "largeExpr"
            , "exponential"
            ]
    where
      binfo = def & biMatcherLike .~ defaultUniMatcherLike
      goldenCoCTC t = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
        let newT = runQuote $ CaseOfCase.caseOfCase binfo True mempty t
        -- make sure the floated result typechecks
        _ <- runQuoteT . flip inferType (() <$ newT) =<< TC.getDefTypeCheckConfig ()
        pure $ newT
