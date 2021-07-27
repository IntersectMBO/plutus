{-# LANGUAGE TypeApplications #-}

module NamesSpec
    ( names
    ) where

import           PlutusIR.Generators.AST
import           PlutusIR.Transform.Rename ()

import           PlutusCore.Check.Scoping
import           PlutusCore.Generators
import           PlutusCore.Quote
import           PlutusCore.Rename

import           Control.Exception
import           Hedgehog
import           System.IO.Unsafe
import           Test.Tasty
import           Test.Tasty.Hedgehog

scopingRename :: TestTree
scopingRename =
    testProperty "renaming does not destroy scoping" . withTests 1000 . property $ do
        prog <- forAllPretty $ runAstGen genProgram
        let catchEverything = unsafePerformIO . try @SomeException . evaluate
        case catchEverything $ checkRespectsScoping (runQuote . rename) prog of
            Left  exc        -> fail $ show exc
            Right (Left err) -> fail $ show err
            Right (Right ()) -> success

names :: TestTree
names =
    testGroup "names"
        [ scopingRename
        ]
