-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}
module TestDetailed where
import Control.Exception
import Data.Text qualified as T
import GHC.IO.Handle
import System.Directory
import System.Environment
import System.Exit
import System.IO
import System.Process

import Distribution.TestSuite

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

-- compare the output of plc vs plc-agda in its default (typed) mode
compareResult :: (T.Text -> T.Text -> Bool) -> String -> String -> IO Progress
compareResult eq mode test = withTempFile $ \tmp -> do
  example <- readProcess "plc" ["example", "-s",test] []
  writeFile tmp example
  putStrLn $ "test: " ++ test
  plcOutput <- readProcess "plc" [mode, "--input",tmp] []
  plcAgdaOutput <- catchOutput $ catch
    (withArgs [mode,"--input",tmp]  M.main)
    (\case
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ()) -- does this ever happen?
  return $ Finished $ if eq (T.pack plcOutput) (T.pack plcAgdaOutput) then Pass else Fail $ "plc: '" ++ plcOutput ++ "' " ++ "plc-agda: '" ++ plcAgdaOutput ++ "'"

-- compare the output of uplc vs plc-agda in untyped mode
compareResultU :: (T.Text -> T.Text -> Bool) -> String -> IO Progress
compareResultU eq test = withTempFile $ \tmp -> do
  example <- readProcess "uplc" ["example","-s",test] []
  writeFile tmp example
  putStrLn $ "test: " ++ test
  plcOutput <- readProcess "uplc" ["evaluate", "--input",tmp] []
  plcAgdaOutput <- catchOutput $ catch
    (withArgs ["evaluate","-mU","--input",tmp]  M.main)
    (\case
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  return $ Finished $ if eq (T.pack plcOutput) (T.pack plcAgdaOutput) then Pass else Fail $ "plc: '" ++ plcOutput ++ "' " ++ "plc-agda: '" ++ plcAgdaOutput ++ "'"
-- compare the results of two different (typed) plc-agda modes
compareResultMode :: String -> String -> (T.Text -> T.Text -> Bool) -> String -> IO Progress
compareResultMode mode1 mode2 eq test = withTempFile $ \tmp -> do
  example <- readProcess "plc" ["example","-s",test] []
  writeFile tmp example
  putStrLn $ "test: " ++ test
  plcAgdaOutput1 <- catchOutput $ catch
    (withArgs ["evaluate","--input",tmp,"--mode",mode1]  M.main)
    (\case
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  plcAgdaOutput2 <- catchOutput $ catch
    (withArgs ["evaluate","--input",tmp,"--mode",mode2]  M.main)
    (\case
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  return $ Finished $ if eq (T.pack plcAgdaOutput1) (T.pack plcAgdaOutput2) then Pass else Fail $ mode1 ++ ": '" ++ plcAgdaOutput1 ++ "' " ++ mode2 ++ ": '" ++ plcAgdaOutput2 ++ "'" ++ " === "++ T.unpack (M.blah (T.pack plcAgdaOutput1) (T.pack plcAgdaOutput2))

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
tests = do
  return $ map Test $
    map (mkTest M.alphaTm "evaluate") testNames
     ++

{- -- tests against extrinisically typed interpreter disabled
map (mkTestMode "L" "TL" M.alphaTm) testNames
     ++
    map (mkTestMode "L" "CK" M.alphaTm) testNames
     ++
    map (mkTestMode "CK" "TCK" M.alphaTm) testNames
     ++
-}
    map (mkTestMode "TL" "TCK" M.alphaTm) testNames
     ++
    map (mkTestMode "TCK" "TCEK" M.alphaTm) testNames
    ++
    map (mkTest M.alphaTy "typecheck") testNames
     ++
    map (mkTestU M.alphaU) testNames
  where
    fails = TestInstance
        { run = return $ Finished $ Fail "Always fails!"
        , name = "fails"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right fails
        }
