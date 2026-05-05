module Test.Certifier.Executable where

import Certifier
import PlutusCore.Default.Builtins
import PlutusCore.Executable.Common
import PlutusCore.Quote
import UntypedPlutusCore as UPLC

import Data.Functor
import Data.Time.Clock.System
import System.Directory (getCurrentDirectory, removeDirectoryRecursive, setCurrentDirectory)
import System.Exit
import System.FilePath
import System.Process

import Test.Tasty
import Test.Tasty.HUnit

{-| The tests in this file run tests of the uplc certifier. Various
    unoptimised UPLC is fed to the optimiser with the certifier turned
    on, which will then call the Agda decision procedures for each of
    the phases. -}
loadUplc :: FilePath -> IO (Term Name DefaultUni DefaultFun ())
loadUplc path = UPLC._progTerm . void . snd <$> parseInput (FileInput path)

simplify
  :: Term Name DefaultUni DefaultFun ()
  -> OptimizerTrace Name DefaultUni DefaultFun ()
simplify =
  runQuote
    . fmap snd
    . runOptimizerT
    . termOptimizer
      defaultOptimizeOpts
      DefaultFunSemanticsVariantE

loadAndMakeCert :: String -> IO FilePath
loadAndMakeCert name =
  makeCert name =<< loadUplc (fixedPath </> "UPLC" </> name ++ ".uplc")

makeCert :: String -> Term Name DefaultUni DefaultFun () -> IO FilePath
makeCert name term = do
  time <- systemNanoseconds <$> getSystemTime
  let certDir = name <> "-" <> show time
      certOutput = ProjectOutput certDir
  runCertifier (mkCertifier (simplify term) name certOutput []) >>= \case
    Right True -> pure certDir
    _ -> assertFailure $ "Certifier failed on " <> name

-- Serialisation tests: run the certifier to make a certificate,
-- then try to load it in Agda.
runAgda :: String -> IO (ExitCode, String)
runAgda file = do
  (exitCode, result, _) <- readProcessWithExitCode "agda-with-stdlib-and-metatheory" [file] []
  return (exitCode, result)

agdaTestCert :: String -> Assertion
agdaTestCert name = do
  certDir <- loadAndMakeCert name
  oldDir <- getCurrentDirectory
  setCurrentDirectory certDir
  (resCode, resText) <- runAgda ("src" </> name <.> "agda")
  setCurrentDirectory oldDir
  if resCode == ExitSuccess
    then removeDirectoryRecursive certDir
    else assertFailure $ name ++ " creates an invalid certificate: " ++ resText

{-
agdaExampleCert :: String -> Assertion
agdaExampleCert name = do
    _ <- makeExampleM name
    (resCode, resText) <- runAgda "TestCert.agda"
    assertBool ("Example " ++ name
      ++ " creates an invalid certificate: \\n" ++ resText)
      (resCode == ExitSuccess)
-}

-- We were just calling the nested stuff with this constant, so it
-- might as well be constant for now.
fixedPath :: FilePath
fixedPath = "test/certifier/"

srcTests :: [String]
srcTests =
  [ "inc"
  , "len"
  , "MinBS"
  , "AA2-CSE"
  , "forceDelayIfThenElse"
  , "builtinUnparse"
  ]

makeExampleTests :: [(String, Term Name DefaultUni DefaultFun ())] -> [TestTree]
makeExampleTests = map (\(name, term) -> testCase name (makeCertAndCleanup name term))
  where
    makeCertAndCleanup name term = makeCert name term >>= removeDirectoryRecursive

makeSerialisationTests :: [String] -> [TestTree]
makeSerialisationTests = map (\testname -> testCase testname (agdaTestCert testname))

{-
makeSerialisationExampleTests :: [ String ] -> [ TestTree]
makeSerialisationExampleTests = map (\testname -> testCase testname (agdaExampleCert testname))
-}

executableTests :: [(String, Term Name DefaultUni DefaultFun ())] -> TestTree
executableTests examples =
  testGroup
    "certifier executable tests"
    [ -- TODO: tracked by https://github.com/IntersectMBO/plutus-private/issues/1556
      -- testGroup "example serialisation certification"
      --                $ makeSerialisationExampleTests exampleNames
      testGroup "example certification" $ makeExampleTests examples
    , testGroup "serialisation certification" $ makeSerialisationTests srcTests
    ]
