-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}

{-| The tests in this file run the various Adga PLC evaluators on the examples
    provided by `plc example` and `uplc example` and checks that the output is
    the same as that produced by the Haskell `plc` and `uplc` evaluators and the
    other Agda evaluators.. -}
module Main (main) where

import PlutusCore.Name.Unique (isIdentifierChar)

import Control.Exception
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as BSL
import Data.Char (isDigit, isSpace)
import Data.Text qualified as T
import GHC.IO.Encoding (setLocaleEncoding)
import GHC.IO.Handle
import System.Directory
import System.Environment
import System.Exit
import System.FilePath ((</>))
import System.IO
import System.IO.Extra
import System.Process
import Test.Tasty
import Test.Tasty.HUnit

import MAlonzo.Code.Main qualified as M

-- Running external programs

-- this function is based on this stackoverflow answer:
-- https://stackoverflow.com/a/9664017
catchOutput :: IO () -> IO String
catchOutput act = do
  tmpD <- getTemporaryDirectory
  (tmpFP, tmpH) <- openTempFile tmpD "stdout"
  stdoutDup <- hDuplicate stdout
  hDuplicateTo tmpH stdout
  hClose tmpH
  act
  hDuplicateTo stdoutDup stdout
  str <- readFile tmpFP
  removeFile tmpFP
  return str

-- | Run plc-agda with some arguments.  This is for use inside HUnit Assertions
runPlcAgda :: [String] -> IO String
runPlcAgda args =
  catchOutput $
    catch
      (withArgs args M.main)
      ( \case
          ExitFailure _ -> assertFailure "plc-agda failed"
          ExitSuccess -> return ()
      )

{-| Run an external executable with some arguments.  This is for use inside HUnit
   Assertions -}
runProg :: String -> [String] -> String -> IO String
runProg prog args stdin' = do
  (exitCode, output, err) <- readProcessWithExitCode prog args stdin'
  case exitCode of
    ExitFailure _ -> assertFailure $ prog ++ " failed: " ++ err
    ExitSuccess -> pure ()
  pure output

{- These tests were previously broken because they produced textual output from
different progams and then compared them using Agda functions like
Evaluator.Term.alphaTm, which read them back in using the PLC/UPLC parsers and
then compare them up to alpha-equivalence.  The problem is that the Agda
evaluators only produce output whose variables are (non-unique) names with de
Bruijn indices appended and the Haskell parsers can't parse those.  This led to
test failures which were (a) unexpected, and (b) confusing because `alphaTm`
will return `False` for two identical inputs which don't parse even though they
look the same.

The current code works around this by converting the textual output to a
canonical form which only involves de Bruijn indices and comparing the strings
directly.  This depends crucially on names with de Bruijn indices being of the
form `[A-Za-z0-9_]*![0-9]+`.
-}

{-| This takes a string and reverses it while squashing all sequences of
   whitespace (including '\n' and '\t') down to single spaces -}
squashRev :: String -> String
squashRev s = go s []
  where
    go [] acc = acc
    go (c : cs) acc =
      if isSpace c
        then go (dropWhile isSpace cs) (' ' : acc)
        else go cs (c : acc)

{-| This takes a string with de Bruijn indices of the form abc!456 and converts
   them to things like !456.  We actually take a reversed string and when we
   find a digit we seek along the string for a '!'; if we find one then we skip
   all characters after it which are allowed in textual IDs until we get to one
   that isn't.  Conveniently `squashRev` provides us with a reversed string for
   input to this function. -}
anonDeBruijn :: String -> String
anonDeBruijn s = go s []
  where
    go [] acc = acc
    go (c : cs) acc =
      if isDigit c
        then go2 cs (c : acc)
        else go cs (c : acc)
    {- go2: copy all digits to the output until we find a '!'; after that drop all
     characters that might appear in a textual name.  Strictly we should also
     check that the final character is an identifierStartingChar and maybe also
     account for quoted ideintfiers. -}
    go2 [] acc = acc
    go2 ('!' : cs) acc = go (dropWhile isIdentifierChar cs) ('!' : acc)
    go2 s' acc = go s' acc

{-| Convert a textual PLC term containing de Bruijn-named variables of the form id!index
to a canonical form.

eg, "(lam var!0   [(  builtin    addInteger)   var!1 x!4  ])"
 -> "(lam !0 [( builtin addInteger) var!1 x!4 ])"

The main point of this is to (a) ignore everything in names apart from the de
Bruijn index, and (b) to remove newlines and indentation.  This could be
misleading if a program happens tocontain a literal string that has a substring
that looks like one of our de Bruijn-named variables.  However that seems very
improbable, and for it to cause problems in our tests we'd need to have two
terms that contain literal strings in the same place which have different
de-Bruijn-like substrings, which seems even more unlikely. -}
canonicalise :: String -> String
canonicalise = anonDeBruijn . squashRev

-- Compare the output of plc vs plc-agda in its default (typed) mode.  The
-- equality comparison in this and similar functions takes terms in the form of
-- Text objects because that's how Agda represents strings. -}
compareResultPlc :: (T.Text -> T.Text -> Bool) -> String -> String -> Assertion
compareResultPlc eq mode testname = withTempFile $ \tmp -> do
  example <- runProg "plc" ["example", "-s", testname] []
  writeFile tmp example
  plcOutput <- runProg "plc" [mode, "--input", tmp, "--print-mode", "Classic", "--debruijn"] []
  plcAgdaOutput <- runPlcAgda [mode, "--input", tmp]
  let plcOutput' = canonicalise plcOutput
      plcAgdaOutput' = canonicalise plcAgdaOutput
  assertBool
    ( "plc: "
        ++ plcOutput
        ++ "plc-agda: "
        ++ plcAgdaOutput
        ++ "** If these look the same they may be failing to parse."
    )
    $ T.pack plcOutput' `eq` T.pack plcAgdaOutput'

-- If `eq` was M.alphaTm here it would return False if either of the inputs
-- didn't parse, which is confusing.

-- Compare the output of uplc vs plc-agda in untyped mode
compareResultUplc :: (T.Text -> T.Text -> Bool) -> String -> String -> Assertion
compareResultUplc eq mode testname = withTempFile $ \tmp -> do
  example <- runProg "uplc" ["example", "-s", testname] []
  writeFile tmp example
  plcOutput <- runProg "uplc" [mode, "--input", tmp, "--print-mode", "Classic", "--debruijn"] []
  plcAgdaOutput <- runPlcAgda [mode, "-mU", "--input", tmp]
  let plcOutput' = canonicalise plcOutput
      plcAgdaOutput' = canonicalise plcAgdaOutput
  assertBool
    ( "uplc: "
        ++ plcAgdaOutput
        ++ "plc-agda: "
        ++ plcOutput
        ++ "** If these look the same they may be failing to parse."
    )
    $ T.pack plcOutput' `eq` T.pack plcAgdaOutput'

-- Compare the results of two different (typed) plc-agda modes
compareResultAgda :: (T.Text -> T.Text -> Bool) -> String -> String -> String -> Assertion
compareResultAgda eq mode1 mode2 testname = withTempFile $ \tmp -> do
  example <- runProg "plc" ["example", "-s", testname] []
  writeFile tmp example
  plcAgdaOutput1 <- runPlcAgda ["evaluate", "--input", tmp, "--mode", mode1]
  plcAgdaOutput2 <- runPlcAgda ["evaluate", "--input", tmp, "--mode", mode2]
  -- The outputs are both produced by plc-agda so we don't have to canonicalise them.
  assertBool
    ( mode1
        ++ ": "
        ++ plcAgdaOutput1
        ++ mode2
        ++ ": "
        ++ plcAgdaOutput2
        ++ "** If these look the same they may be failing to parse."
    )
    $ T.pack plcAgdaOutput1 `eq` T.pack plcAgdaOutput2

-- These come from `plc example -a` but there are a couple of failing tests which are omitted.
-- `uplc` provides the same examples, but erased.
testNames :: [String]
testNames =
  [ "succInteger"
  , "unitval"
  , "true"
  , "false"
  , "churchZero"
  , "churchSucc"
  , "overapplication"
  , "factorial"
  , "fibonacci"
  , "NatRoundTrip"
  , "ScottListSum"
  , "IfIntegers"
  , "ApplyAdd1"
  , "ApplyAdd2"
  ]

-- test plc against plc-agda
mkTestPlc :: (T.Text -> T.Text -> Bool) -> String -> String -> TestTree
mkTestPlc eq mode testname = testCase testname (compareResultPlc eq mode testname)

-- test uplc against plc-agda untyped mode
mkTestUplc :: (T.Text -> T.Text -> Bool) -> String -> String -> TestTree
mkTestUplc eq mode testname = testCase testname (compareResultUplc eq mode testname)

-- test different (typed) plc-agda modes against each other
mkTestAgda :: (T.Text -> T.Text -> Bool) -> String -> String -> String -> TestTree
mkTestAgda eq mode1 mode2 testname = testCase testname (compareResultAgda eq mode1 mode2 testname)

-- | Test that .hex and .flat files produce the same output when used with uplc
testHexFlatEquivalence :: String -> Assertion
testHexFlatEquivalence testname = withTempDir $ \tmpDir -> do
  let textualFile = tmpDir </> "input.uplc"
      flatFile = tmpDir </> "test.flat"
      hexFile = tmpDir </> "test.hex"

  example <- runProg "uplc" ["example", "-s", testname] []
  writeFile textualFile example

  _ <-
    runProg
      "uplc"
      [ "convert"
      , "--if"
      , "textual"
      , "--of"
      , "flat"
      , "--input"
      , textualFile
      , "--output"
      , flatFile
      ]
      []
  flatBytes <- BSL.readFile flatFile

  BS.writeFile hexFile (Base16.encode (BSL.toStrict flatBytes))

  flatOutput <-
    runProg
      "uplc"
      [ "evaluate"
      , "--if"
      , "flat"
      , "--input"
      , flatFile
      , "--print-mode"
      , "Classic"
      ]
      []
  hexOutput <-
    runProg
      "uplc"
      [ "evaluate"
      , "--if"
      , "flat"
      , "--input"
      , hexFile
      , "--print-mode"
      , "Classic"
      ]
      []
  assertBool
    ( "Flat file output: "
        ++ flatOutput
        ++ "\nHex file output: "
        ++ hexOutput
        ++ "\n** Outputs should be identical"
    )
    $ flatOutput == hexOutput

-- | Test case for hex/flat equivalence
mkTestHexFlat :: String -> TestTree
mkTestHexFlat testname = testCase ("hex/flat equivalence: " ++ testname) $ testHexFlatEquivalence testname

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain $
    testGroup
      "Detailed"
      -- These should really use M.alphaTm or M.alphaTy instead of (==).
      [ testGroup "plc-agda vs. uplc: evaluation" . mkTests $ mkTestUplc (==) "evaluate"
      , testGroup "plc-agda vs. plc: evaluation" . mkTests $ mkTestPlc (==) "evaluate"
      , testGroup "plc-agda vs. plc: typechecking" . mkTests $ mkTestPlc (==) "typecheck"
      , testGroup "TL vs. TCK" . mkTests $ mkTestAgda (==) "TL" "TCK"
      , testGroup "TCK vs. TCEK" . mkTests $ mkTestAgda (==) "TCK" "TCEK"
      , testGroup "Hex/Flat file format equivalence" [mkTestHexFlat "unitval"]
      -- tests against extrinisically typed interpreter disabled
      -- , mkTestMode "L" "TL" M.alphaTm
      -- , mkTestMode "L" "CK" M.alphaTm
      -- , mkTestMode "CK" "TCK" M.alphaTm
      ]
  where
    mkTests mktest = map mktest testNames
