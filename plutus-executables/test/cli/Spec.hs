-- | Tests for the CLI UX of uplc/plc/pir: @--help@ examples, completion-script
-- generation, completion queries, and the shared @Examples@ footer renderer.
module Main (main) where

import PlutusCore.Executable.Help (Example, eg, examplesDoc)

import Data.List (isInfixOf, isPrefixOf)
import Data.Maybe (isNothing)
import Prettyprinter (defaultLayoutOptions, layoutPretty)
import Prettyprinter.Render.String (renderString)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)
import Test.Tasty
import Test.Tasty.HUnit

runOk :: String -> [String] -> IO String
runOk prog args = runOkIn prog args ""

runOkIn :: String -> [String] -> String -> IO String
runOkIn prog args stdin' = do
  (code, out, err) <- readProcessWithExitCode prog args stdin'
  case code of
    ExitSuccess -> pure out
    ExitFailure n ->
      assertFailure $
        prog
          <> " "
          <> unwords args
          <> " exited with code "
          <> show n
          <> "\nstderr:\n"
          <> err

assertInfix :: String -> String -> Assertion
assertInfix needle haystack =
  assertBool
    ("expected to find " <> show needle <> " in:\n" <> haystack)
    (needle `isInfixOf` haystack)

assertHasLine :: String -> String -> Assertion
assertHasLine needle haystack =
  assertBool
    ("expected a line " <> show needle <> " in:\n" <> haystack)
    (needle `elem` lines haystack)

helpHasExample :: String -> [String] -> String -> TestTree
helpHasExample prog args exampleCmd =
  testCase (prog <> " " <> unwords args) $ do
    out <- runOk prog (args <> ["--help"])
    assertInfix "Examples:" out
    assertInfix exampleCmd out
    -- Catch dead examples: every long flag an example mentions must still be a
    -- real flag of the subcommand. (Top-level help doesn't list subcommand
    -- flags, so only subcommand helps are checked.)
    mapM_ (`assertInfix` out) longFlags
  where
    longFlags
      | null args = []
      | otherwise = [w | w <- words exampleCmd, "--" `isPrefixOf` w]

helpTests :: TestTree
helpTests =
  testGroup
    "--help includes worked examples"
    [ helpHasExample "uplc" [] "uplc evaluate -i program.uplc"
    , helpHasExample "uplc" ["evaluate"] "uplc evaluate --if hex"
    , helpHasExample "uplc" ["convert"] "uplc convert --if hex --of textual"
    , helpHasExample "uplc" ["apply"] "uplc apply --if flat"
    , helpHasExample "uplc" ["optimise"] "uplc optimize -i program.uplc"
    , helpHasExample "uplc" ["benchmark"] "uplc benchmark -i program.uplc"
    , helpHasExample "plc" [] "plc typecheck -i program.plc"
    , helpHasExample "pir" [] "pir compile"
    ]

completionScriptTests :: TestTree
completionScriptTests =
  testGroup
    "completion scripts generate"
    [ testCase "bash" $ do
        out <- runOk "uplc" ["--bash-completion-script", "uplc"]
        assertInfix "complete" out
        assertInfix "_uplc" out
    , testCase "zsh" $ do
        out <- runOk "uplc" ["--zsh-completion-script", "uplc"]
        assertBool "zsh completion script should be non-empty" (not (null out))
    , testCase "fish" $ do
        out <- runOk "uplc" ["--fish-completion-script", "uplc"]
        assertBool "fish completion script should be non-empty" (not (null out))
    ]

queryCompletions :: String -> [String] -> Int -> IO [String]
queryCompletions prog cmdWords idx =
  lines
    <$> runOk
      prog
      ( ["--bash-completion-index", show idx]
          <> concatMap (\w -> ["--bash-completion-word", w]) cmdWords
      )

completionQueryTests :: TestTree
completionQueryTests =
  testGroup
    "completion queries"
    [ testCase "subcommand names complete" $ do
        cs <- queryCompletions "uplc" ["uplc", ""] 1
        mapM_ (`assertElem` cs) ["evaluate", "convert", "apply", "optimise", "debug"]
    , testCase "--if completes format names" $ do
        cs <- queryCompletions "uplc" ["uplc", "convert", "--if", ""] 3
        mapM_ (`assertElem` cs) ["textual", "flat", "hex", "blueprint", "flat-named"]
    , testCase "--builtin-semantics-variant completes A..E" $ do
        cs <- queryCompletions "uplc" ["uplc", "evaluate", "--builtin-semantics-variant", ""] 3
        mapM_ (`assertElem` cs) ["A", "B", "C", "D", "E"]
    ]
  where
    assertElem x xs =
      assertBool ("expected " <> show x <> " among completions " <> show xs) (x `elem` xs)

runnableExampleTests :: TestTree
runnableExampleTests =
  testGroup
    "help examples actually run"
    [ testCase "stdin evaluate example" $ do
        out <- runOkIn "uplc" ["evaluate"] "(program 1.1.0 (con integer 42))"
        assertInfix "42" out
    , testCase "example -a lists examples" $ do
        out <- runOk "uplc" ["example", "-a"]
        assertInfix "succInteger" out
    ]

render :: [Example] -> Maybe String
render = fmap (renderString . layoutPretty defaultLayoutOptions) . examplesDoc

examplesDocTests :: TestTree
examplesDocTests =
  testGroup
    "examplesDoc renders correctly"
    [ testCase "empty list produces no footer" $
        assertBool "expected Nothing for []" (isNothing (examplesDoc []))
    , testCase "single example" $ case render [eg "Evaluate a program" "uplc evaluate -i p.uplc"] of
        Nothing -> assertFailure "expected a rendered footer"
        Just s -> do
          let ls = lines s
          assertEqual "first line is the section header" "Examples:" (head ls)
          assertHasLine "  # Evaluate a program" s
          assertHasLine "  uplc evaluate -i p.uplc" s
    , testCase "multiple examples are blank-line separated" $ case render [eg "d1" "c1", eg "d2" "c2"] of
        Nothing -> assertFailure "expected a rendered footer"
        Just s -> do
          assertHasLine "  c1" s
          assertHasLine "  c2" s
          assertBool "expected at least two blank separator lines" (length (filter null (lines s)) >= 2)
    ]

main :: IO ()
main =
  defaultMain $
    testGroup
      "CLI UX"
      [ examplesDocTests
      , helpTests
      , completionScriptTests
      , completionQueryTests
      , runnableExampleTests
      ]
