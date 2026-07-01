module PlutusIR.Compiler.Recursion.Tests where

import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (ask)
import Data.Text.IO qualified as T
import PlutusCore qualified as PLC
import PlutusCore.Default (someValue)
import PlutusCore.MkPlc (constant)
import PlutusCore.Pretty (pretty)
import PlutusCore.Pretty qualified as PrettyPLC
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Test (runUPlc, runUPlcFull)
import PlutusCore.Version (latestVersion)
import PlutusIR qualified as PIR
import PlutusIR.Parser (parse)
import PlutusIR.Test

import System.FilePath (joinPath, (</>))
import Test.Tasty
import Test.Tasty.Extras

test_recursion :: TestTree
test_recursion =
  runTestNested
    ["plutus-ir", "test", "PlutusIR", "Compiler", "Recursion"]
    [ goldenNamedUPlcFromPir pTermAsProg "factorial"
    , goldenPlcFromPir pTermAsProg "even3"
    , goldenEvalPir pTermAsProg "even3Eval"
    , goldenPlcFromPir pTermAsProg "stupidZero"
    , goldenPlcFromPir pTermAsProg "mutuallyRecursiveValues"
    , goldenEvalPir pTermAsProg "errorBinding"
    , goldenNamedUPlcFromPir pTermAsProg "evenOddIntegerMutual"
    , goldenEvalPirAppliedInteger "evenOddIntegerMutual" "evenOddIntegerMutual-10" 10
    , goldenEvalPirAppliedInteger "evenOddIntegerMutual" "evenOddIntegerMutual-11" 11
    , goldenBudgetPirAppliedInteger "evenOddIntegerMutual" "evenOddIntegerMutual-200" 200
    , goldenNamedUPlcFromPir pTermAsProg "evenIntegerSelf"
    , goldenEvalPirAppliedInteger "evenIntegerSelf" "evenIntegerSelf-10" 10
    , goldenEvalPirAppliedInteger "evenIntegerSelf" "evenIntegerSelf-11" 11
    , goldenBudgetPirAppliedInteger "evenIntegerSelf" "evenIntegerSelf-200" 200
    , goldenNamedUPlcFromPir pTermAsProg "divisibleByThreeIntegerMutual"
    , goldenEvalPirAppliedInteger "divisibleByThreeIntegerMutual" "divisibleByThreeIntegerMutual-9" 9
    , goldenEvalPirAppliedInteger "divisibleByThreeIntegerMutual" "divisibleByThreeIntegerMutual-10" 10
    , goldenBudgetPirAppliedInteger
        "divisibleByThreeIntegerMutual"
        "divisibleByThreeIntegerMutual-300"
        300
    , goldenNamedUPlcFromPir pTermAsProg "divisibleByThreeIntegerSelf"
    , goldenEvalPirAppliedInteger "divisibleByThreeIntegerSelf" "divisibleByThreeIntegerSelf-9" 9
    , goldenEvalPirAppliedInteger "divisibleByThreeIntegerSelf" "divisibleByThreeIntegerSelf-10" 10
    , goldenBudgetPirAppliedInteger "divisibleByThreeIntegerSelf" "divisibleByThreeIntegerSelf-300" 300
    ]

goldenEvalPirAppliedInteger :: String -> TestName -> Integer -> TestNested
goldenEvalPirAppliedInteger sourceName goldenName n = do
  sourceDir <- joinPath <$> ask
  nestedGoldenVsDocM goldenName ".eval" $ do
    program <- loadPirProgram (sourceDir </> sourceName)
    result <- runExceptT $ runUPlc [program, integerProgram n]
    pure $ either (pretty . show) PrettyPLC.prettyPlcReadableSimple result

goldenBudgetPirAppliedInteger :: String -> TestName -> Integer -> TestNested
goldenBudgetPirAppliedInteger sourceName goldenName n = do
  sourceDir <- joinPath <$> ask
  nestedGoldenVsDocM goldenName ".budget" $ do
    program <- loadPirProgram (sourceDir </> sourceName)
    result <- runExceptT $ runUPlcFull [program, integerProgram n]
    pure $
      either
        (pretty . show)
        ( \(termRes, budget, _) ->
            pretty $
              "Final budget: "
                <> show budget
                <> "\nResult: "
                <> PrettyPLC.render (PrettyPLC.prettyPlcReadableSimple termRes)
        )
        result

loadPirProgram
  :: FilePath
  -> IO (PIR.Program PIR.TyName PIR.Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan)
loadPirProgram filePath = do
  contents <- T.readFile filePath
  case runQuoteT $ parse pTermAsProg filePath contents of
    Left err -> fail $ show err
    Right program -> pure program

integerProgram
  :: Integer
  -> PIR.Program PIR.TyName PIR.Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan
integerProgram n = PIR.Program topSrcSpan latestVersion $ constant topSrcSpan $ someValue n
