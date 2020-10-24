{-# LANGUAGE LambdaCase #-}

module Main where

import           Codec.Serialise
import           Control.Monad
import qualified Data.ByteString.Lazy                                       as BSL
import           Options.Applicative                                        hiding (action)
import           System.Environment
import           System.Exit                                                (exitFailure)
import           System.IO

import           Control.Monad                                              ()
import           Control.Monad.Trans.Except                                 (runExceptT)
import           Data.Char                                                  (isSpace)
import qualified Data.Map                                                   as Map
import           Language.PlutusCore                                        (Name (..))
import qualified Language.PlutusCore                                        as PLC
import           Language.PlutusCore.CBOR                                   ()
import           Language.PlutusCore.Constant                               (DynamicBuiltinNameMeanings (..))
import           Language.PlutusCore.Evaluation.Machine.Cek                 ()
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import qualified Language.PlutusCore.Pretty                                 as PLC
import           Language.PlutusCore.Universe
import qualified Language.PlutusTx                                          as Tx
import           Language.PlutusTx.Prelude                                  as TxPrelude hiding (replicate, (<$), (<$>),
                                                                                          (<*>))
import           Language.UntypedPlutusCore                                 as UPLC
import qualified Language.UntypedPlutusCore.DeBruijn                        as UPLC
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek
import           Plutus.Benchmark.Clausify                                  (Formula (..), clauses, replicate)
import qualified Plutus.Benchmark.Clausify                                  as Clausify
import qualified Plutus.Benchmark.Knights                                   as Knights
import qualified Plutus.Benchmark.LastPiece                                 as LastPiece
import qualified Plutus.Benchmark.Prime                                     as Prime
import qualified Plutus.Benchmark.Queens                                    as Queens
import qualified Prelude                                                    as P

data Action = RunPLC | RunHaskell | DumpPLC | DumpCBORnamed | DumpCBORdeBruijn

actionReader :: String -> Maybe Action
actionReader =
    \case
      "run"              -> Just RunPLC
      "runPLC"           -> Just RunPLC
      "runHaskell"       -> Just RunHaskell
      "dumpPLC"          -> Just DumpPLC
      "dumpCBORnamed"    -> Just DumpCBORnamed
      "dumpCBOR"         -> Just DumpCBORdeBruijn
      "dumpCBORdeBruijn" -> Just DumpCBORdeBruijn
      _ -> Nothing

action :: Parser Action
action = argument (maybeReader actionReader)
         ( metavar "ACTION")

data ProgAndArgs =
    Clausify Clausify.StaticFormula
  | Queens P.Integer Queens.Algorithm
  | Knights P.Integer P.Integer
  | LastPiece
  | Prime Prime.PrimeID

data Command = Command Action ProgAndArgs


clausifyFormulaReader :: String -> Either String Clausify.StaticFormula
clausifyFormulaReader "1" = Right Clausify.F1
clausifyFormulaReader "2" = Right Clausify.F2
clausifyFormulaReader "3" = Right Clausify.F3
clausifyFormulaReader "4" = Right Clausify.F4
clausifyFormulaReader "5" = Right Clausify.F5
clausifyFormulaReader "6" = Right Clausify.F6
clausifyFormulaReader "7" = Right Clausify.F7
clausifyFormulaReader f   = Left $ "Cannot parse `" <> f <> "`. Should be 1, 2, 3, 4, 5, 6 or 7."

clausifyOptions :: Parser ProgAndArgs
clausifyOptions =
  Clausify P.<$> argument (eitherReader clausifyFormulaReader)
                          (metavar "FORMULA" P.<>
                           help "Formula to use for benchmarking: 1, 2, 3, 4, 5, 6 or 7")

queensOptions :: Parser ProgAndArgs
queensOptions =
  Queens P.<$> argument auto (metavar "BOARD-SIZE" P.<>
                              help "Size of the playing board NxN")
         P.<*> (argument (eitherReader queensAlgorithmReader)
                        (metavar "ALGORITHM" P.<>
                         help "Algorithm to use for constraint solving. I know of: bt, bm, bjbt, bjbt' or fc"))

knightsOptions :: Parser ProgAndArgs
knightsOptions =
  Knights P.<$> argument auto (metavar "DEPTH" P.<>
                               help "How deep does the search go.")
          P.<*> argument auto (metavar "BOARD-SIZE" P.<>
                               help "Board size NxN")

queensAlgorithmReader :: String -> Either String Queens.Algorithm
queensAlgorithmReader "bt"    = Right Queens.Bt
queensAlgorithmReader "bm"    = Right Queens.Bm
queensAlgorithmReader "bjbt1" = Right Queens.Bjbt1
queensAlgorithmReader "bjbt2" = Right Queens.Bjbt2
queensAlgorithmReader "fc"    = Right Queens.Fc
queensAlgorithmReader alg     = Left $ "Unknown algorithm: " <> alg <> ". I know of: bt, bm, bjbt, bjbt1 or fc."

lastpieceOptions :: Parser ProgAndArgs
lastpieceOptions = P.pure LastPiece

primeIdReader :: String -> Either String Prime.PrimeID
primeIdReader "5"  = Right Prime.P5
primeIdReader "8"  = Right Prime.P8
primeIdReader "10" = Right Prime.P10
primeIdReader "20" = Right Prime.P20
primeIdReader "30" = Right Prime.P30
primeIdReader "40" = Right Prime.P40
primeIdReader "50" = Right Prime.P50
primeIdReader "60" = Right Prime.P60
primeIdReader f    = Left $ "Cannot parse `" <> f <> "`. Should be 'P' plus number of digits (5, 8, 10, 20, 30, 40, 50, or 60 .)"

primeOptions :: Parser ProgAndArgs
primeOptions =
  Prime P.<$> (argument auto (metavar "INPUT" P.<>
                              help "Identifier for input prime: P<number of digits>"))

progAndArgs = hsubparser
  ( command "clausify"  (info clausifyOptions  (progDesc "Run the clausify benchmark.")) P.<>
    command "queens"    (info queensOptions    (progDesc "Run the queens benchmark."))   P.<>
    command "knights"   (info knightsOptions   (progDesc "Run the knights benchmark"))   P.<>
    command "lastpiece" (info lastpieceOptions (progDesc "Run the lastpiece benchmark")) P.<>
    command "prime"     (info primeOptions     (progDesc "Run the primes benchmark")) )

options :: Parser Command
options = Command <$> action <*> progAndArgs

emptyBuiltins :: DynamicBuiltinNameMeanings (CekValue DefaultUni)
emptyBuiltins = DynamicBuiltinNameMeanings Map.empty

evaluateWithCek :: Term Name DefaultUni () -> EvaluationResult (Term Name DefaultUni ())
evaluateWithCek term =
  unsafeEvaluateCek emptyBuiltins defaultCostModel term

toDeBruijn :: Program Name DefaultUni a -> IO (Program UPLC.DeBruijn DefaultUni a)
toDeBruijn prog = do
  r <- PLC.runQuoteT $ runExceptT (UPLC.deBruijnProgram prog)
  case r of
    Left e  -> hPutStrLn stderr (show e) >> exitFailure
    Right p -> return $ UPLC.programMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix) p

data CborMode = Named | DeBruijn

writeCBOR :: CborMode -> Program Name DefaultUni () -> IO ()
writeCBOR cborMode prog =
    case cborMode of
      Named    -> BSL.putStr $ serialise prog
      DeBruijn -> toDeBruijn prog >>= BSL.putStr . serialise


main :: IO ()
main = do
  Command act panda <- execParser (info (helper P.<*> options) idm)
  case act of
    RunPLC -> do
        let program = getProgram panda
            result = unsafeEvaluateCek emptyBuiltins defaultCostModel program
        print . PLC.prettyPlcClassicDebug $ result
    RunHaskell ->
        case panda of
          Clausify formula        -> print $ Clausify.runClausify formula
          Queens boardSize alg    -> print $ Queens.runQueens boardSize alg
          Knights depth boardSize -> print $ Knights.runKnights depth boardSize
          LastPiece               -> print $ "Not yet"
          Prime input             -> print $ Prime.runFixedPrimalityTest input
    DumpPLC -> mapM_ putStrLn $ unindent . PLC.prettyPlcClassicDebug $ getWrappedProgram panda
               where unindent d = map (dropWhile isSpace) $ (lines . show $ d)
    DumpCBORnamed    -> writeCBOR Named $ getWrappedProgram panda
    DumpCBORdeBruijn -> writeCBOR DeBruijn $ getWrappedProgram panda
    -- ^ Write the output to stdout and let the user deal with redirecting it.
    where getProgram =
              \case
               Clausify formula        -> Clausify.mkClausifyTerm formula
               Queens boardSize alg    -> Queens.mkQueensTerm boardSize alg
               Knights depth boardSize -> Knights.mkKnightsTerm depth boardSize
               LastPiece               -> LastPiece.mkLastPieceTerm
               Prime input             -> Prime.mkPrimalityBenchTerm input
          getWrappedProgram = Program () (Version () 1 0 0) . getProgram
