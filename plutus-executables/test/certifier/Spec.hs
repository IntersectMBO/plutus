{-# LANGUAGE OverloadedStrings #-}

{- | The tests in this file run tests of the uplc certifier. Various unoptimised UPLC is
    fed to the optimiser with the certifier turned on, which will then call the Agda decision
    procedures for each of the phases. -}

module Main (main) where

import Data.Text qualified as T (Text, pack)
import GHC.IO.Encoding (setLocaleEncoding)
import System.Exit
import System.FilePath
import System.IO
import System.Process
import Test.Tasty
import Test.Tasty.HUnit

import Test.Tasty.Extras (goldenVsTextM)

{- | Run an external executable with some arguments.  This is for use inside HUnit
   Assertions -}
runProg :: String -> [String] -> String -> IO T.Text
runProg prog args stdin' = do
  (exitCode, output, err) <- readProcessWithExitCode prog args stdin'
  case exitCode of
    ExitFailure _ -> assertFailure $ prog ++ " failed: " ++ err
    ExitSuccess   -> pure ()
  return $ T.pack output

makeGoldenUplcCert :: [ String ] -> String -> TestTree
makeGoldenUplcCert path name = do
    let inputfile = foldr (</>) ("UPLC" </> name ++ ".uplc") path
    let goldenfile = foldr (</>) ("Golden" </> name ++ ".golden") path
    let args = ["optimise", "--certify", "TestCert",
                "--input", inputfile,
                "--print-mode", "Classic"]
    let result = runProg "uplc" args []
    goldenVsTextM name goldenfile result

-- We were just calling the nested stuff with this constant, so it
-- might as well be constant for now.
fixedPath :: [ String ]
fixedPath = ["test", "certifier"]

simpleTests :: [ String ]
simpleTests = [ "len" ]

makeTestTree :: [ String ] -> [ TestTree ]
makeTestTree = map (\s -> makeGoldenUplcCert fixedPath s)

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain $
    testGroup "Certification"
    [ testGroup "simple certification"  $ makeTestTree simpleTests

    ]
