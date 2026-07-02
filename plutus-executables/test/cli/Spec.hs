{-| Tests for the command-line UX of the @uplc@, @plc@, and @pir@ tools:

* the @Examples@ sections added to @--help@ output,
* shell-completion script generation, and
* completion queries (subcommand names and enumerated option values).

These run the built executables (made available on @PATH@ via
@build-tool-depends@) and inspect their output. There is also a pure test of the
shared @Examples@ footer renderer in "PlutusCore.Executable.Help". -}
module Main (main) where

import PlutusCore.Executable.Help (Example, eg, examplesDoc)

import Data.List (isInfixOf)
import Data.Maybe (isNothing)
import Prettyprinter (defaultLayoutOptions, layoutPretty)
import Prettyprinter.Render.String (renderString)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)
import Test.Tasty
import Test.Tasty.HUnit

{-| Run @prog args@ with empty stdin, asserting it exits successfully, and return
its stdout. Both @--help@ and optparse-applicative completion queries exit with
success and print to stdout, so this works for all cases here. -}
runOk :: String -> [String] -> IO String
runOk prog args = do
  (code, out, err) <- readProcessWithExitCode prog args ""
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

-- | Assert that @needle@ occurs somewhere in @haystack@.
assertInfix :: String -> String -> Assertion
assertInfix needle haystack =
  assertBool
    ("expected to find " <> show needle <> " in:\n" <> haystack)
    (needle `isInfixOf` haystack)

-- | Assert that @needle@ occurs as a whole line in @haystack@.
assertHasLine :: String -> String -> Assertion
assertHasLine needle haystack =
  assertBool
    ("expected a line " <> show needle <> " in:\n" <> haystack)
    (needle `elem` lines haystack)

---------------- --help examples ----------------

-- | @--help@ (top-level or subcommand) should include an @Examples@ section.
helpHasExample :: String -> [String] -> String -> TestTree
helpHasExample prog args exampleCmd =
  testCase (prog <> " " <> unwords args) $ do
    out <- runOk prog (args <> ["--help"])
    assertInfix "Examples:" out
    assertInfix exampleCmd out

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

---------------- shell completion ----------------

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

{-| Query completions the way the generated bash script does: pass every word of
the command line (word 0 is the program name) as @--bash-completion-word@, and
the index of the word being completed as @--bash-completion-index@. The
candidate completions are printed to stdout, one per line. -}
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
        -- `uplc <tab>`
        cs <- queryCompletions "uplc" ["uplc", ""] 1
        mapM_ (`assertElem` cs) ["evaluate", "convert", "apply", "optimise", "debug"]
    , testCase "--if completes format names" $ do
        -- `uplc convert --if <tab>`
        cs <- queryCompletions "uplc" ["uplc", "convert", "--if", ""] 3
        mapM_ (`assertElem` cs) ["textual", "flat", "hex", "blueprint", "flat-named"]
    , testCase "--builtin-semantics-variant completes A..E" $ do
        -- `uplc evaluate --builtin-semantics-variant <tab>`
        cs <- queryCompletions "uplc" ["uplc", "evaluate", "--builtin-semantics-variant", ""] 3
        mapM_ (`assertElem` cs) ["A", "B", "C", "D", "E"]
    ]
  where
    assertElem x xs =
      assertBool ("expected " <> show x <> " among completions " <> show xs) (x `elem` xs)

---------------- pure: Examples footer renderer ----------------

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
          -- one blank line before each example block
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
      ]
