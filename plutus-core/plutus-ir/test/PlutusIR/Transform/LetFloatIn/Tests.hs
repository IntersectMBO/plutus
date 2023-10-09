{-# LANGUAGE TypeApplications #-}
module PlutusIR.Transform.LetFloatIn.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Name
import PlutusCore.Quote
import PlutusIR.Error as PIR
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.LetFloatIn qualified as LetFloatIn
import PlutusIR.Transform.LetMerge qualified as LetMerge
import PlutusIR.Transform.Rename ()
import PlutusIR.TypeCheck as TC
import PlutusPrelude

test_letFloatInConservative :: TestTree
test_letFloatInConservative = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform/LetFloatIn"] $
    testNested "conservative" $
        map
            (goldenPirM goldenFloatTC pTerm)
            [ "avoid-floating-into-lam"
            , "avoid-floating-into-tyabs"
            ]
  where
    goldenFloatTC pir = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
        let pirFloated = runQuote $ LetFloatIn.floatTerm def False pir
        -- make sure the floated result typechecks
        _ <- runQuoteT . flip inferType (() <$ pirFloated) =<< TC.getDefTypeCheckConfig ()
        -- letmerge is not necessary for floating, but is a nice visual transformation
        pure $ LetMerge.letMerge pirFloated

test_letFloatInRelaxed :: TestTree
test_letFloatInRelaxed = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform/LetFloatIn"] $
    testNested "relaxed" $
        map
            (goldenPirM goldenFloatTC pTerm)
            [ "avoid-floating-into-RHS"
            , "avoid-moving-strict-nonvalue-bindings"
            , "cannot-float-into-app"
            , "datatype1"
            , "datatype2"
            , "float-into-fun-and-arg-1"
            , "float-into-fun-and-arg-2"
            , "float-into-lam1"
            , "float-into-lam2"
            , "float-into-RHS"
            , "float-into-tyabs1"
            , "float-into-tyabs2"
            , "float-into-constr"
            , "float-into-case-arg"
            , "float-into-case-branch"
            , "type"
            ]
  where
    goldenFloatTC pir = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
        let pirFloated = runQuote $ LetFloatIn.floatTerm def True pir
        -- make sure the floated result typechecks
        _ <- runQuoteT . flip inferType (() <$ pirFloated) =<< TC.getDefTypeCheckConfig ()
        -- letmerge is not necessary for floating, but is a nice visual transformation
        pure $ LetMerge.letMerge pirFloated
