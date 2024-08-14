-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}

{- | The tests in this file run the various Adga PLC evaluators on the examples
    provided by `plc example` and `uplc example` and checks that the output is
    the same as that produced by the Haskell `plc` and `uplc` evaluators. -}
-- TODO: use Hedgehog or something instead

module Spec where
import Control.Exception
import Data.Text qualified as T
import GHC.IO.Handle
import System.Directory
import System.Environment
import System.Exit
import System.IO
import System.Process

import Data.Char (isAlphaNum, isDigit, isSpace)
import Distribution.TestSuite

import PlutusCore.Name.Unique (isIdentifierChar)

import MAlonzo.Code.Evaluator.Term qualified as M
import MAlonzo.Code.Main qualified as M
import MAlonzo.Code.Raw qualified as R

import System.IO.Extra

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

{- These tests were previously broken because they produced textual output from
different progams and then compared them using Agda functions like
Evaluator.Term.alphaTm, which read them back in using the PLC/UPLC parsers and
then compare them up to alpha-equivalence.  The problem is that the Agda
evaluators only produce output whose varaibles are (non-unique) names with de
Bruijn indices appended and the Haskell parsers can't parse those.  The current
code works around this by converting the textual onput to a canonical form which
only involves de Bruijn indices and comparing the strings directly.  This all
depends crucially on names with de Bruijn indices being of the form
`[A-Za-z0-9_]*![0-9]+`.
-}

{- | This takes a string and reverses it while squashing all sequences of
   whitespace (including '\n' and '\t') down to single spaces -}
squashRev :: String -> String
squashRev s = go s []
  where go [] acc = acc
        go (c:cs) acc =
          if isSpace c
          then go (dropWhile isSpace cs) (' ':acc)
          else go cs (c:acc)

{- | This takes a string with de Bruijn indices of the form abc!456 and converts
   them to things like !456.  We actually take a reversed string and when we
   find a digit we seek along the string for a '!'; if we find one then we skip
   all characters after it which are allowed in textual IDs until we get to one
   that isn't.  Conveniently `squashRev` provides us with a reversed string for
   input to this function. -}
anonDeBruijn :: String -> String
anonDeBruijn s = go s []
  where
    go [] acc = acc
    go (c:cs) acc =
      if isDigit c
      then go2 cs (c:acc)
      else go cs (c:acc)
    {- go2: copy all digits to the output until we find a '!'; after that drop all
     characters that might appear in a textual name.  Strictly we should also
     check that the final character is an identifierStartingChar and maybe also
     account for quoted ideintfiers. -}
    go2 [] acc       = acc
    go2 ('!':cs) acc =  go (dropWhile isIdentifierChar cs) ('!':acc)
    go2 s acc        = go s acc

{- | Convert a textual PLC term containing de Bruijn-named variables of the form id!index
to a canonical form.

eg, "(lam var!0   [(  builtin    addInteger)   var!1 x!4  ])"
 -> "(lam !0 [( builtin addInteger) var!1 x!4 ])"

The main point of this is to (a) ignore everything in names apart from the de
Bruijn index, and (b) to remove newlines and indentation.  This could be
misleading if a program happens tocontain a literal string that has a substring
that looks like one of our de Bruijn-named variables.  However that seems very
improbable, and for it to cause problems in our tests we'd need to have two
terms that contain literal strings in the same place which have different
de-Bruijn-like substrings, which seems even more unlikely.
-}
canonicalise :: String -> String
canonicalise = anonDeBruijn . squashRev

-- compare the output of plc vs plc-agda in its default (typed) mode
compareResult :: (T.Text -> T.Text -> Bool) -> String -> String -> IO Progress
compareResult eq mode test = withTempFile $ \tmp -> do
  example <- readProcess "plc" ["example", "-s", test] []
  writeFile tmp example
  putStrLn $ "test: " ++ test
  plcOutput <- readProcess "plc" [mode, "--input", tmp, "--print-mode", "Classic", "--debruijn"] []
  plcAgdaOutput <- catchOutput $ catch
    (withArgs [mode, "--input", tmp]  M.main)
    (\case
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ()) -- does this ever happen?
  let plcOutput' = canonicalise plcOutput
      plcAgdaOutput' = canonicalise plcAgdaOutput
      result =
        if plcOutput' == plcAgdaOutput'
        then Pass
        else Fail $ "plc: '" ++ plcOutput' ++ "' " ++ "plc-agda: '" ++ plcAgdaOutput' ++ "'"
  return $ Finished result

-- compare the output of uplc vs plc-agda in untyped mode
compareResultU :: (T.Text -> T.Text -> Bool) -> String -> IO Progress
compareResultU eq test = withTempFile $ \tmp -> do
  example <- readProcess "uplc" ["example", "-s", test] []
  writeFile tmp example
  putStrLn $ "test: " ++ test
  plcOutput <- readProcess "uplc" ["evaluate", "--input", tmp, "--print-mode", "Classic", "--debruijn"] []
  plcAgdaOutput <- catchOutput $ catch
    (withArgs ["evaluate", "-mU", "--input", tmp]  M.main)
    (\case
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  let plcOutput' = canonicalise plcOutput
      plcAgdaOutput' = canonicalise plcAgdaOutput
      result =
        if plcOutput' == plcAgdaOutput'
        then Pass
        else Fail $ "uplc: '" ++ plcOutput' ++ "' " ++ "plc-agda: '" ++ plcAgdaOutput' ++ "'"
  return $ Finished result

-- compare the results of two different (typed) plc-agda modes
compareResultMode :: String -> String -> (T.Text -> T.Text -> Bool) -> String -> IO Progress
compareResultMode mode1 mode2 eq test = withTempFile $ \tmp -> do
  example <- readProcess "plc" ["example", "-s", test] []
  writeFile tmp example
  putStrLn $ "test: " ++ test
  plcAgdaOutput1 <- catchOutput $ catch
    (withArgs ["evaluate", "--input", tmp, "--mode", mode1]  M.main)
    (\case
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  plcAgdaOutput2 <- catchOutput $ catch
    (withArgs ["evaluate", "--input", tmp, "--mode", mode2]  M.main)
    (\case
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  let result =
        if T.pack plcAgdaOutput1 `eq` T.pack plcAgdaOutput2
        then Pass else
          Fail $ mode1 ++ ": '" ++ plcAgdaOutput1 ++ "' "
          ++ mode2 ++ ": '" ++ plcAgdaOutput2 ++ "'"
          ++ " === "++ T.unpack (M.blah (T.pack plcAgdaOutput1) (T.pack plcAgdaOutput2))
  return $ Finished result

testNames = ["succInteger"
            ,"unitval"
            ,"true"
            ,"false"
            ,"churchZero"
            ,"churchSucc"
            ,"overapplication"
            ,"factorial"
            ,"fibonacci"
            ,"NatRoundTrip"
            ,"ScottListSum"
            ,"IfIntegers"
            ,"ApplyAdd1"
            ,"ApplyAdd2"
            ]
-- test plc against plc-agda
mkTest :: (T.Text -> T.Text -> Bool) -> String -> String -> TestInstance
mkTest eq mode test = TestInstance
        { run = compareResult eq mode test
        , name = mode ++ " " ++ test
        , tags = []
        , options = []
        , setOption = \_ _ -> Right (mkTest eq mode test)
        }

-- test uplc against plc-agda untyped mode
mkTestU :: (T.Text -> T.Text -> Bool) -> String -> TestInstance
mkTestU eq test = TestInstance
        { run = compareResultU eq test
        , name = "evaluate" ++ " " ++ test
        , tags = []
        , options = []
        , setOption = \_ _ -> Right (mkTestU eq test)
        }

-- test different (typed) plc-agda modes against each other
mkTestMode :: String -> String -> (T.Text -> T.Text -> Bool) -> String -> TestInstance
mkTestMode mode1 mode2 eq test = TestInstance
        { run = compareResultMode mode1 mode2 eq test
        , name = mode1 ++ " " ++  mode2 ++ " " ++ test
        , tags = []
        , options = []
        , setOption = \_ _ -> Right (mkTestMode mode1 mode2 eq test)
        }

tests :: IO [Test]
tests = pure $ concatMap (\f -> map (Test . f) testNames)
        [ mkTest (==) "evaluate"         -- Should really use M.alphaTm
        , mkTestMode "TL" "TCK" (==)     -- Should really use M.alphaTm
        , mkTestMode "TCK" "TCEK" (==)   -- Should really use M.alphaTm
        , mkTest (==) "typecheck"        -- Should really use M.alphaTy
        , mkTestU (==)                   -- Should really use M.alphaTm
        -- tests against extrinisically typed interpreter disabled
        -- , mkTestMode "L" "TL" M.alphaTm
        -- , mkTestMode "L" "CK" M.alphaTm
        -- , mkTestMode "CK" "TCK" M.alphaTm
        ]
