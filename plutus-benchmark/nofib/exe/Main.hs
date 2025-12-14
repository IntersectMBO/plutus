-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Prelude (fmap, (<>))
import Prelude qualified as Hs

import Control.Lens hiding (argument)
import Control.Monad ()
import Control.Monad.Trans.Except (runExceptT)
import Data.ByteString qualified as BS
import Data.Char (isSpace)
import Data.Foldable (traverse_)
import Data.SatInt
import Data.String (fromString)
import Options.Applicative as Opt hiding (action)
import PlutusCore.Flat qualified as Flat
import Prettyprinter (Doc, indent, line, vsep)
import System.Exit (exitFailure)
import System.IO
import Text.Printf (printf)

import PlutusBenchmark.Common (toAnonDeBruijnTerm)

import PlutusBenchmark.NoFib.Clausify qualified as Clausify
import PlutusBenchmark.NoFib.Knights qualified as Knights
import PlutusBenchmark.NoFib.LastPiece qualified as LastPiece
import PlutusBenchmark.NoFib.Prime qualified as Prime
import PlutusBenchmark.NoFib.Queens qualified as Queens

import PlutusCore qualified as PLC
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Pretty (prettyPlc)
import PlutusPrelude (unsafeFromRight)
import PlutusTx (getPlcNoAnn)
import PlutusTx.Code (CompiledCode, countAstNodes)
import PlutusTx.List
import PlutusTx.Prelude hiding (fmap, mappend, (<$), (<$>), (<*>), (<>))
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

failWithMsg :: Hs.String -> IO a
failWithMsg s = hPutStrLn stderr s >> exitFailure

-- | A program together with its arguments
data ProgAndArgs
  = Clausify Clausify.StaticFormula
  | Queens Hs.Integer Queens.Algorithm
  | Knights Hs.Integer Hs.Integer
  | LastPiece
  | Prime Prime.PrimeID
  | Primetest Integer

-- | The actions this program can perform
data Options
  = RunPLC ProgAndArgs
  | RunHaskell ProgAndArgs
  | DumpPLC ProgAndArgs
  | DumpFlatNamed ProgAndArgs
  | DumpFlatDeBruijn ProgAndArgs
  | SizesAndBudgets

-- Clausify options --

knownFormulae :: Hs.String
knownFormulae = "one of F1, F2, F3, F4, F5, F6, F7"

clausifyFormulaReader :: Hs.String -> Either Hs.String Clausify.StaticFormula
clausifyFormulaReader "F1" = Right Clausify.F1
clausifyFormulaReader "F2" = Right Clausify.F2
clausifyFormulaReader "F3" = Right Clausify.F3
clausifyFormulaReader "F4" = Right Clausify.F4
clausifyFormulaReader "F5" = Right Clausify.F5
clausifyFormulaReader "F6" = Right Clausify.F6
clausifyFormulaReader "F7" = Right Clausify.F7
clausifyFormulaReader f = Left $ "Cannot parse `" <> f <> "`. Expected " ++ knownFormulae ++ "."

clausifyOptions :: Parser ProgAndArgs
clausifyOptions =
  Clausify
    <$> argument
      (eitherReader clausifyFormulaReader)
      ( metavar "FORMULA"
          <> help ("Formula to use for benchmarking: " ++ knownFormulae ++ ".")
      )

-- Knights options --

knightsOptions :: Parser ProgAndArgs
knightsOptions =
  Knights
    <$> argument
      auto
      ( metavar "DEPTH"
          <> help "Maximum search depth."
      )
    <*> argument
      auto
      ( metavar "BOARD-SIZE"
          <> help "Board size (NxN)"
      )

-- Lastpiece options --

lastpieceOptions :: Parser ProgAndArgs
lastpieceOptions = Hs.pure LastPiece

-- Primes options --

knownPrimes :: Hs.String
knownPrimes = "P05, P08, P10, P20, P30, P40, P50, P60, P100, P150, or P200 (a prime with the indicated number of digits)"

primeIdReader :: Hs.String -> Either Hs.String Prime.PrimeID
primeIdReader "P05" = Right Prime.P5
primeIdReader "P08" = Right Prime.P8
primeIdReader "P10" = Right Prime.P10
primeIdReader "P20" = Right Prime.P20
primeIdReader "P30" = Right Prime.P30
primeIdReader "P40" = Right Prime.P40
primeIdReader "P50" = Right Prime.P50
primeIdReader "P60" = Right Prime.P60
primeIdReader "P100" = Right Prime.P100
primeIdReader "P150" = Right Prime.P150
primeIdReader "P200" = Right Prime.P200
primeIdReader f = Left $ "Cannot parse `" <> f <> "`. Possible values are " ++ knownPrimes ++ "."

-- | Apply the primality test to one of the built-in primes
primeOptions :: Parser ProgAndArgs
primeOptions =
  Prime
    <$> ( argument
            (eitherReader primeIdReader)
            (metavar "ID" <> help ("Identifier for known prime: " ++ knownPrimes))
        )

-- Primetest options --

-- | Apply the primality test to a given integer instead of one of the built-in large primes
primetestOptions :: Parser ProgAndArgs
primetestOptions =
  Primetest <$> (argument auto (metavar "N" <> help "a positive integer"))

-- Queens options --

knownAlgorithms :: Hs.String
knownAlgorithms = "bt, bm, bjbt1, bjbt2, fc"

queensAlgorithmReader :: Hs.String -> Either Hs.String Queens.Algorithm
queensAlgorithmReader "bt" = Right Queens.Bt
queensAlgorithmReader "bm" = Right Queens.Bm
queensAlgorithmReader "bjbt1" = Right Queens.Bjbt1
queensAlgorithmReader "bjbt2" = Right Queens.Bjbt2
queensAlgorithmReader "fc" = Right Queens.Fc
queensAlgorithmReader alg = Left $ "Unknown algorithm: " <> alg <> ". Options are " ++ knownAlgorithms

queensOptions :: Parser ProgAndArgs
queensOptions =
  Queens
    <$> argument
      auto
      ( metavar "BOARD-SIZE"
          <> help "Size of the playing board NxN"
      )
    <*> ( argument
            (eitherReader queensAlgorithmReader)
            ( metavar "ALGORITHM"
                <> help ("Algorithm to use for constraint solving. One of: " ++ knownAlgorithms)
            )
        )

-- Main parsers --

progAndArgs :: Parser ProgAndArgs
progAndArgs =
  hsubparser
    ( command "clausify" (info clausifyOptions (progDesc "Run the Clausify benchmark."))
        <> command "queens" (info queensOptions (progDesc "Run the Queens benchmark."))
        <> command "knights" (info knightsOptions (progDesc "Run the Knights benchmark"))
        <> command "lastpiece" (info lastpieceOptions (progDesc "Run the Lastpiece benchmark"))
        <> command "prime" (info primeOptions (progDesc "Run the Prime benchmark on a known prime (see help)"))
        <> command "primetest" (info primetestOptions (progDesc "Run the Prime benchmark on a positive integer N"))
    )

options :: Parser Options
options =
  hsubparser
    ( command
        "run"
        ( info
            (RunPLC <$> progAndArgs)
            (progDesc "same as run-plc")
        )
        <> command
          "run-plc"
          ( info
              (RunPLC <$> progAndArgs)
              (progDesc "compile the program to Plutus Core and evaluate it using the CEK machine")
          )
        <> command
          "run-hs"
          ( info
              (RunHaskell <$> progAndArgs)
              (progDesc "run the program directly as Hs")
          )
        <> command
          "dump-uplc"
          ( info
              (DumpPLC <$> progAndArgs)
              (progDesc "print the program (applied to arguments) as Plutus Core source on standard output")
          )
        <> command
          "dump-flat-named"
          ( info
              (DumpFlatNamed <$> progAndArgs)
              (progDesc "dump the AST as Flat, preserving names")
          )
        <> command
          "dump-flat"
          ( info
              (DumpFlatDeBruijn <$> progAndArgs)
              (progDesc "same as dump-flat-deBruijn, but easier to type")
          )
        <> command
          "dump-flat-deBruijn"
          ( info
              (DumpFlatDeBruijn <$> progAndArgs)
              (progDesc "dump the AST as Flat, with names replaced by de Bruijn indices")
          )
        <> command
          "sizes-and-budgets"
          ( info
              (Hs.pure SizesAndBudgets)
              (progDesc "Print the size and cpu/memory budgets of each program")
          )
    )

---------------- Evaluation ----------------

evaluateWithCek
  :: UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
  -> UPLC.EvaluationResult (UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ())
evaluateWithCek =
  UPLC.unsafeSplitStructuralOperational
    . UPLC.cekResultToEither
    . UPLC._cekReportResult
    . UPLC.runCekDeBruijn PLC.defaultCekParametersForTesting UPLC.restrictingEnormous UPLC.noEmitter

writeFlatNamed :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun () -> IO ()
writeFlatNamed prog = BS.putStr . Flat.flat . UPLC.UnrestrictedProgram $ prog

writeFlatDeBruijn :: UPLC.Program UPLC.DeBruijn DefaultUni DefaultFun () -> IO ()
writeFlatDeBruijn prog = BS.putStr . Flat.flat . UPLC.UnrestrictedProgram $ prog

description :: Hs.String
description =
  "This program provides operations on a number of Plutus programs "
    ++ "ported from the nofib Hs test suite.  "
    ++ "The programs are written in Hs and can be run directly "
    ++ "or compiled into Plutus Core and run on the CEK machine.  "
    ++ "Compiled programs can also be output in a number of formats."

knownProgs :: [Doc ann]
knownProgs = map fromString ["clausify", "knights", "lastpiece", "prime", "primetest", "queens"]

-- Extra information about the available programs.  We need a Doc because if you
-- just make it a string it removes newlines and other formatting.  There's some
-- manual formatting in here because the text doesn't wrap as expected, presumably
-- due to what optparse-applicative is doing internally.
footerInfo :: Doc ann
footerInfo =
  fromString "Most commands take the name of a program and a (possbily empty) list of arguments."
    <> line
    <> line
    <> fromString "The available programs are: "
    <> line
    <> indent 2 (vsep knownProgs)
    <> line
    <> line
    <> fromString
      ( "See 'nofib-exe run <programe-name> --help' for information about the arguments\n"
          ++ "for a particular program."
      )
    <> line
    <> line
    <> fromString
      ( "The 'dump' commands construct a Plutus Core term applying the program to its\n"
          ++ "arguments and prints the result to the terminal in the specified format.\n"
          ++ "You'll probably want to redirect the output to a file."
      )

-- Copied pretty much directly from plutus-tx/testlib/PlutusTx/Test.hs
measureBudget :: CompiledCode a -> (Integer, Integer)
measureBudget compiledCode =
  let programE =
        PLC.runQuote
          $ runExceptT @PLC.FreeVariableError
          $ traverseOf UPLC.progTerm UPLC.unDeBruijnTerm
          $ getPlcNoAnn compiledCode
   in case programE of
        Left _ -> (-1, -1) -- Something has gone wrong but I don't care.
        Right program ->
          let (_, UPLC.TallyingSt _ budget) = UPLC.runCekNoEmit PLC.defaultCekParametersForTesting UPLC.tallying $ program ^. UPLC.progTerm
              ExCPU cpu = exBudgetCPU budget
              ExMemory mem = exBudgetMemory budget
           in (fromSatInt cpu, fromSatInt mem)

getInfo :: (Hs.String, CompiledCode a) -> (Hs.String, Integer, Integer, Integer)
getInfo (name, code) =
  let size = countAstNodes code
      (cpu, mem) = measureBudget code
   in (name, size, cpu, mem)

printSizesAndBudgets :: IO ()
printSizesAndBudgets = do
  -- The applied programs to measure, which are the same as the ones in the benchmarks.
  -- We can't put all of these in one list because the 'a's in 'CompiledCode a' are different
  let clausify =
        [ ("clausify/F1", Clausify.mkClausifyCode Clausify.F1)
        , ("clausify/F2", Clausify.mkClausifyCode Clausify.F2)
        , ("clausify/F3", Clausify.mkClausifyCode Clausify.F3)
        , ("clausify/F4", Clausify.mkClausifyCode Clausify.F4)
        , ("clausify/F5", Clausify.mkClausifyCode Clausify.F5)
        ]
      knights =
        [ ("knights/4x4", Knights.mkKnightsCode 100 4)
        , ("knights/6x6", Knights.mkKnightsCode 100 6)
        , ("knights/8x8", Knights.mkKnightsCode 100 8)
        ]
      primetest =
        [ ("primes/05digits", Prime.mkPrimalityCode Prime.P5)
        , ("primes/08digits", Prime.mkPrimalityCode Prime.P8)
        , ("primes/10digits", Prime.mkPrimalityCode Prime.P10)
        , ("primes/20digits", Prime.mkPrimalityCode Prime.P20)
        , ("primes/30digits", Prime.mkPrimalityCode Prime.P30)
        , ("primes/40digits", Prime.mkPrimalityCode Prime.P40)
        , ("primes/50digits", Prime.mkPrimalityCode Prime.P50)
        ]
      queens4x4 =
        [ ("queens4x4/bt", Queens.mkQueensCode 4 Queens.Bt)
        , ("queens4x4/bm", Queens.mkQueensCode 4 Queens.Bm)
        , ("queens4x4/bjbt1", Queens.mkQueensCode 4 Queens.Bjbt1)
        , ("queens4x4/bjbt2", Queens.mkQueensCode 4 Queens.Bjbt2)
        , ("queens4x4/fc", Queens.mkQueensCode 4 Queens.Fc)
        ]
      queens5x5 =
        [ ("queens5x5/bt", Queens.mkQueensCode 5 Queens.Bt)
        , ("queens5x5/bm", Queens.mkQueensCode 5 Queens.Bm)
        , ("queens5x5/bjbt1", Queens.mkQueensCode 5 Queens.Bjbt1)
        , ("queens5x5/bjbt2", Queens.mkQueensCode 5 Queens.Bjbt2)
        , ("queens5x5/fc", Queens.mkQueensCode 5 Queens.Fc)
        ]
      statistics = map getInfo clausify ++ map getInfo knights ++ map getInfo primetest ++ map getInfo queens4x4 ++ map getInfo queens5x5
      formatInfo (name, size, cpu, mem) = printf "%-20s %10d %15d %15d\n" name size cpu mem

  putStrLn "Script                     Size     CPU budget      Memory budget"
  putStrLn "-----------------------------------------------------------------"
  traverse_ (putStr . formatInfo) statistics

main :: IO ()
main = do
  execParser (info (helper <*> options) (fullDesc <> progDesc description <> footerDoc (Just footerInfo))) >>= \case
    RunPLC pa ->
      print . prettyPlc . fmap fromNamedDeBruijnUPLC . evaluateWithCek . getTerm $ pa
    RunHaskell pa ->
      case pa of
        Clausify formula -> print $ Clausify.runClausify formula
        Knights depth boardSize -> print $ Knights.runKnights depth boardSize
        LastPiece -> print $ LastPiece.runLastPiece
        Queens boardSize alg -> print $ Queens.runQueens boardSize alg
        Prime input -> print $ Prime.runFixedPrimalityTest input
        Primetest n ->
          if n < 0
            then Hs.error "Positive number expected"
            else print $ Prime.runPrimalityTest n
    DumpPLC pa ->
      traverse_ putStrLn
        $ unindent
        . prettyPlc
        . UPLC.Program () PLC.latestVersion
        . fromNamedDeBruijnUPLC
        . getTerm
        $ pa
      where
        -- These are big programs and with indentation the output is > 90% whitespace
        unindent d = map (dropWhile isSpace) $ (Hs.lines . Hs.show $ d)
    DumpFlatNamed pa ->
      writeFlatNamed . UPLC.Program () PLC.latestVersion . getTerm $ pa
    DumpFlatDeBruijn pa ->
      writeFlatDeBruijn . UPLC.Program () PLC.latestVersion . toAnonDeBruijnTerm . getTerm $ pa
    SizesAndBudgets ->
      printSizesAndBudgets
  where
    -- Write the output to stdout and let the user deal with redirecting it.
    getTerm :: ProgAndArgs -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
    getTerm =
      \case
        Clausify formula -> Clausify.mkClausifyTerm formula
        Queens boardSize alg -> Queens.mkQueensTerm boardSize alg
        Knights depth boardSize -> Knights.mkKnightsTerm depth boardSize
        LastPiece -> LastPiece.mkLastPieceTerm
        Prime input -> Prime.mkPrimalityBenchTerm input
        Primetest n ->
          if n < 0
            then Hs.error "Positive number expected"
            else Prime.mkPrimalityTestTerm n
    fromNamedDeBruijnUPLC
      :: UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
      -> UPLC.Term UPLC.Name DefaultUni DefaultFun ()
    fromNamedDeBruijnUPLC =
      unsafeFromRight @PLC.FreeVariableError
        . PLC.runQuoteT
        . UPLC.unDeBruijnTerm
