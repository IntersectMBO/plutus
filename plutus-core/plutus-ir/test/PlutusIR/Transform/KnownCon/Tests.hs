{-# LANGUAGE TypeApplications #-}
module PlutusIR.Transform.KnownCon.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Name
import PlutusCore.Quote
import PlutusIR.Error as PIR
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.KnownCon qualified as KnownCon
import PlutusIR.TypeCheck as TC

test_knownCon :: TestTree
test_knownCon = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "KnownCon" $
        map
            (goldenPirM goldenKnownConTC pTerm)
            [ "applicative"
            , "bool"
            , "list"
            , "maybe-just"
            , "maybe-just-unsaturated"
            , "maybe-nothing"
            , "pair"
            ]
  where
    goldenKnownConTC pir = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
        let simplified = runQuote $ KnownCon.knownCon pir
        -- make sure the result typechecks
        _ <- runQuoteT . flip inferType (() <$ simplified) =<< TC.getDefTypeCheckConfig ()
        pure simplified
