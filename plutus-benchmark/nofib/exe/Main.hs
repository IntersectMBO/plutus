{-# LANGUAGE LambdaCase #-}

module Main where

import           Prelude                                           ((<>))
import qualified Prelude                                           as P

import           Control.Monad
import           Control.Monad                                     ()
import           Control.Monad.Trans.Except                        (runExceptT)
import qualified Data.ByteString.Lazy                              as BSL
import           Data.Char                                         (isSpace)
import           Options.Applicative                               as Opt hiding (action)
import           System.Exit                                       (exitFailure)
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen                      (Doc, indent, line, string, text, vsep)

import           Language.PlutusCore                               (Name (..))
import qualified Language.PlutusCore                               as PLC
import           Language.PlutusCore.Builtins
import           Language.PlutusCore.CBOR                          ()
import           Language.PlutusCore.Evaluation.Machine.Cek        ()
import qualified Language.PlutusCore.Pretty                        as PLC
import           Language.PlutusCore.Universe
import           Language.PlutusTx.Prelude                         as TxPrelude hiding (fmap, mappend, (<$), (<$>),
                                                                                 (<*>), (<>))
import           Language.UntypedPlutusCore                        as UPLC
import qualified Language.UntypedPlutusCore.DeBruijn               as UPLC
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek
import qualified Plutus.Benchmark.Clausify                         as Clausify
import qualified Plutus.Benchmark.Knights                          as Knights
import qualified Plutus.Benchmark.LastPiece                        as LastPiece
import qualified Plutus.Benchmark.Prime                            as Prime
import qualified Plutus.Benchmark.Queens                           as Queens

failWithMsg :: String -> IO a
failWithMsg s = hPutStrLn stderr s >> exitFailure


-- | A program together with its arguments
data ProgAndArgs =
    Clausify  Clausify.StaticFormula
  | Queens    P.Integer Queens.Algorithm
  | Knights   P.Integer P.Integer
  | LastPiece
  | Prime     Prime.PrimeID
  | Primetest Integer

-- | The actions this program can perform
data Options
    = RunPLC           ProgAndArgs
    | RunHaskell       ProgAndArgs
    | DumpPLC          ProgAndArgs
    | DumpCBORnamed    ProgAndArgs
    | DumpCBORdeBruijn ProgAndArgs


-- Clausify options --

knownFormulae :: String
knownFormulae = "one of F1, F2, F3, F4, F5, F6, F7"

clausifyFormulaReader :: String -> Either String Clausify.StaticFormula
clausifyFormulaReader "F1" = Right Clausify.F1
clausifyFormulaReader "F2" = Right Clausify.F2
clausifyFormulaReader "F3" = Right Clausify.F3
clausifyFormulaReader "F4" = Right Clausify.F4
clausifyFormulaReader "F5" = Right Clausify.F5
clausifyFormulaReader "F6" = Right Clausify.F6
clausifyFormulaReader "F7" = Right Clausify.F7
clausifyFormulaReader f    = Left $ "Cannot parse `" <> f <> "`. Expected " ++ knownFormulae ++ "."

clausifyOptions :: Parser ProgAndArgs
clausifyOptions =
  Clausify <$> argument (eitherReader clausifyFormulaReader)
                          (metavar "FORMULA" <>
                           help ("Formula to use for benchmarking: " ++ knownFormulae ++ "."))


-- Knights options --

knightsOptions :: Parser ProgAndArgs
knightsOptions =
  Knights <$> argument auto (metavar "DEPTH" <>
                               help "Maximum search depth.")
          <*> argument auto (metavar "BOARD-SIZE" <>
                               help "Board size (NxN)")


-- Lastpiece options --

lastpieceOptions :: Parser ProgAndArgs
lastpieceOptions = P.pure LastPiece


-- Primes options --

knownPrimes :: String
knownPrimes = "P05, P08, P10, P20, P30, P40, P50, or P60 (a prime with the indicated number of digits)"

primeIdReader :: String -> Either String Prime.PrimeID
primeIdReader "P05" = Right Prime.P5
primeIdReader "P08" = Right Prime.P8
primeIdReader "P10" = Right Prime.P10
primeIdReader "P20" = Right Prime.P20
primeIdReader "P30" = Right Prime.P30
primeIdReader "P40" = Right Prime.P40
primeIdReader "P50" = Right Prime.P50
primeIdReader "P60" = Right Prime.P60
primeIdReader f     = Left $ "Cannot parse `" <> f <> "`. Possible values are " ++ knownPrimes ++"."

-- | Apply the primality test to one of the built-in primes
primeOptions :: Parser ProgAndArgs
primeOptions =
  Prime <$> (argument (eitherReader primeIdReader)
             (metavar "ID" <> help ("Identifier for known prime: " ++ knownPrimes)))


-- Primetest options --

-- | Apply the primality test to a given integer instead of one of the built-in large primes
primetestOptions :: Parser ProgAndArgs
primetestOptions =
  Primetest <$> (argument auto (metavar "N" <> help "a positive integer"))


-- Queens options --

knownAlgorithms :: String
knownAlgorithms = "bt, bm, bjbt1, bjbt2, fc"

queensAlgorithmReader :: String -> Either String Queens.Algorithm
queensAlgorithmReader "bt"    = Right Queens.Bt
queensAlgorithmReader "bm"    = Right Queens.Bm
queensAlgorithmReader "bjbt1" = Right Queens.Bjbt1
queensAlgorithmReader "bjbt2" = Right Queens.Bjbt2
queensAlgorithmReader "fc"    = Right Queens.Fc
queensAlgorithmReader alg     = Left $ "Unknown algorithm: " <> alg <> ". Options are " ++ knownAlgorithms

queensOptions :: Parser ProgAndArgs
queensOptions =
  Queens <$> argument auto (metavar "BOARD-SIZE" <>
                              help "Size of the playing board NxN")
         <*> (argument (eitherReader queensAlgorithmReader)
                        (metavar "ALGORITHM" <>
                         help ("Algorithm to use for constraint solving. One of: " ++ knownAlgorithms)))

-- Main parsers --

progAndArgs :: Parser ProgAndArgs
progAndArgs = hsubparser
  (  command "clausify"  (info clausifyOptions      (progDesc "Run the Clausify benchmark."))
  <> command "queens"    (info queensOptions        (progDesc "Run the Queens benchmark."))
  <> command "knights"   (info knightsOptions       (progDesc "Run the Knights benchmark"))
  <> command "lastpiece" (info lastpieceOptions     (progDesc "Run the Lastpiece benchmark"))
  <> command "prime"     (info primeOptions         (progDesc "Run the Prime benchmark on a known prime (see help)"))
  <> command "primetest" (info primetestOptions (progDesc "Run the Prime benchmark on a positive integer N")) )


options :: Parser Options
options = hsubparser
  (  command "run"
     (info (RunPLC <$> progAndArgs)
      (progDesc "same as runPLC"))
  <> command "runPLC"
     (info (RunPLC <$> progAndArgs)
      (progDesc "compile the program to Plutus Core and evaluate it using the CEK machine"))
  <> command "runHaskell"
     (info (RunHaskell <$> progAndArgs)
      (progDesc "run the program directly as Haskell"))
  <> command "dumpPLC"
     (info (DumpPLC <$> progAndArgs)
      (progDesc "print the program (applied to arguments) as Plutus Core source on standard output"))
  <> command "dumpCBORnamed"
     (info (DumpCBORnamed <$> progAndArgs)
      (progDesc "dump the AST as CBOR, preserving names"))
  <> command "dumpCBOR"
     (info (DumpCBORdeBruijn <$> progAndArgs)
      (progDesc "same as dumpCBORdeBruijn, but easier to type"))
  <> command "dumpCBORdeBruijn"
     (info (DumpCBORdeBruijn <$> progAndArgs)
      (progDesc "dump the AST as CBOR, with names replaced by de Bruijn indices"))
  )


---------------- Evaluation ----------------

evaluateWithCek :: Term Name DefaultUni DefaultFun () -> EvaluationResult (Term Name DefaultUni DefaultFun ())
evaluateWithCek = unsafeEvaluateCek defBuiltinsRuntime

toDeBruijn :: Program Name DefaultUni DefaultFun a -> IO (Program UPLC.DeBruijn DefaultUni DefaultFun a)
toDeBruijn prog = do
  r <- PLC.runQuoteT $ runExceptT (UPLC.deBruijnProgram prog)
  case r of
    Left e  -> failWithMsg (show e)
    Right p -> return $ UPLC.programMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix) p

data CborMode = Named | DeBruijn

writeCBOR :: CborMode -> Program Name DefaultUni DefaultFun () -> IO ()
writeCBOR cborMode prog =
    case cborMode of
      Named    -> BSL.putStr $ serialiseOmittingUnits prog
      DeBruijn -> toDeBruijn prog >>= BSL.putStr . serialiseOmittingUnits

description :: String
description = "This program provides operations on a number of Plutus programs "
              ++ "ported from the nofib Haskell test suite.  "
              ++ "The programs are written in Haskell and can be run directly "
              ++ "or compiled into Plutus Core and run on the CEK machine.  "
              ++ "Compiled programs can also be output in a number of formats."

knownProgs :: [Doc]
knownProgs = map text ["clausify", "knights", "lastpiece", "prime", "primetest", "queens"]

-- Extra information about the available programs.  We need a Doc because if you
-- just make it a string it removes newlines and other formatting.  There's some
-- manual formatting in here because the text doesn't wrap as expected, presumably
-- due to what optparse-applicative is doing internally.
footerInfo :: Doc
footerInfo = text "Every command takes the name of a program and a (possbily empty) list of arguments."
           <> line <> line
           <> (text "The available programs are: ")
           <> line
           <> indent 2 (vsep knownProgs)
           <> line <> line
           <> string ("See 'nofib-exe run <programe-name> --help' for information about the arguments\n"
                   ++ "for a particular program.")
           <> line <> line
           <> string ("The 'dump' commands construct a Plutus Core term applying the program to its\n"
                   ++ "arguments and prints the result to the terminal in the specified format.\n"
                   ++ "You'll probably want to redirect the output to a file.")

main :: IO ()
main = do
  execParser (info (helper <*> options) (fullDesc <> progDesc description <> footerDoc (Just footerInfo))) >>= \case
    RunPLC pa -> do
        let program = getProgram pa
            result = unsafeEvaluateCek defBuiltinsRuntime program
        print . PLC.prettyPlcClassicDebug $ result
    RunHaskell pa ->
        case pa of
          Clausify formula        -> print $ Clausify.runClausify formula
          Knights depth boardSize -> print $ Knights.runKnights depth boardSize
          LastPiece               -> print $ LastPiece.runLastPiece
          Queens boardSize alg    -> print $ Queens.runQueens boardSize alg
          Prime input             -> print $ Prime.runFixedPrimalityTest input
          Primetest n             -> if n<0 then P.error "Positive number expected"
                                     else print $ Prime.runPrimalityTest n
    DumpPLC pa -> mapM_ putStrLn $ unindent . PLC.prettyPlcClassicDebug $ getWrappedProgram pa
               where unindent d = map (dropWhile isSpace) $ (lines . show $ d)
    DumpCBORnamed pa   -> writeCBOR Named $ getWrappedProgram pa
    DumpCBORdeBruijn pa-> writeCBOR DeBruijn $ getWrappedProgram pa
    -- ^ Write the output to stdout and let the user deal with redirecting it.
    where getProgram =
              \case
               Clausify formula        -> Clausify.mkClausifyTerm formula
               Queens boardSize alg    -> Queens.mkQueensTerm boardSize alg
               Knights depth boardSize -> Knights.mkKnightsTerm depth boardSize
               LastPiece               -> LastPiece.mkLastPieceTerm
               Prime input             -> Prime.mkPrimalityBenchTerm input
               Primetest n             -> if n<0 then P.error "Positive number expected"
                                          else Prime.mkPrimalityTestTerm n
          getWrappedProgram = Program () (Version () 1 0 0) . getProgram
