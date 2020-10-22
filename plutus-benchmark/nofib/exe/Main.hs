module Main where

import           Control.Monad
import           Options.Applicative
import           System.Environment

import           Control.Monad                                              ()
import qualified Data.Map                                                   as Map
import           Language.PlutusCore                                        (Name (..))
import           Language.PlutusCore.Constant                               (DynamicBuiltinNameMeanings (..))
import           Language.PlutusCore.Evaluation.Machine.Cek                 ()
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import qualified Language.PlutusCore.Pretty                                 as PLC
import           Language.PlutusCore.Universe
import qualified Language.PlutusTx                                          as Tx
import           Language.PlutusTx.Prelude                                  as TxPrelude hiding (replicate)
import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek
import           Plutus.Benchmark.Clausify                                  (Formula (..), clauses, replicate)
import qualified Plutus.Benchmark.Clausify                                  as Clausify
import qualified Plutus.Benchmark.Knights                                   as Knights
import qualified Plutus.Benchmark.LastPiece                                 as LastPiece
import qualified Plutus.Benchmark.Prime                                     as Prime
import qualified Plutus.Benchmark.Queens                                    as Queens
import qualified Prelude                                                    as P

data Command =
    Clausify P.Integer Clausify.StaticFormula
  | Queens P.Integer Queens.Algorithm
  | Knights P.Integer P.Integer
  | LastPiece
  | Prime Prime.PrimeID

clausifyFormulaReader :: String -> Either String Clausify.StaticFormula
clausifyFormulaReader "1" = Right Clausify.F1
clausifyFormulaReader "2" = Right Clausify.F2
clausifyFormulaReader "3" = Right Clausify.F3
clausifyFormulaReader "4" = Right Clausify.F4
clausifyFormulaReader "5" = Right Clausify.F5
clausifyFormulaReader "6" = Right Clausify.F6
clausifyFormulaReader "7" = Right Clausify.F7
clausifyFormulaReader f   = Left $ "Cannot parse `" <> f <> "`. Should be 1, 2, 3, 4, 5, 6 or 7."

clausifyOptions :: Parser Command
clausifyOptions =
  Clausify P.<$> argument auto (metavar "COUNT" P.<>
                                help "How many times you want the formula replicated")
           P.<*> argument (eitherReader clausifyFormulaReader)
                          (metavar "FORMULA" P.<>
                           help "Formula to use for benchmarking: 1, 2, 3, 4, 5, 6 or 7")

queensOptions :: Parser Command
queensOptions =
  Queens P.<$> argument auto (metavar "BOARD-SIZE" P.<>
                              help "Size of the playing board NxN")
         P.<*> (argument (eitherReader queensAlgorithmReader)
                        (metavar "ALGORITHM" P.<>
                         help "Algorithm to use for constraint solving. I know of: bt, bm, bjbt, bjbt' or fc"))

knightsOptions :: Parser Command
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

lastpieceOptions :: Parser Command
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
primeIdReader f    = Left $ "Cannot parse `" <> f <> "`. Should be 5, 8, 10, 20, 30, 40, 50, or 60."

primeOptions :: Parser Command
primeOptions =
  Prime P.<$> (argument auto (metavar "INPUT" P.<>
                              help "Identifier for input prime: P<number of digits>"))

options :: Parser Command
options = hsubparser
  ( command "clausify" (info clausifyOptions (progDesc "Run the clausify benchmark.")) P.<>
    command "queens" (info queensOptions (progDesc "Run the queens benchmark.")) P.<>
    command "knights" (info knightsOptions (progDesc "Run the knights benchmark")) P.<>
    command "lastpiece" (info lastpieceOptions (progDesc "Run the lastpiece benchmark")) P.<>
    command "prime" (info primeOptions (progDesc "Run the primes benchmark")) )

emptyBuiltins :: DynamicBuiltinNameMeanings (CekValue DefaultUni)
emptyBuiltins = DynamicBuiltinNameMeanings Map.empty

evaluateWithCek :: Term Name DefaultUni () -> EvaluationResult (Term Name DefaultUni ())
evaluateWithCek term =
  unsafeEvaluateCek emptyBuiltins defaultCostModel term

main :: IO ()
main = do
  cmd <- execParser (info (helper P.<*> options) idm)
  let program =
        case cmd of
          Clausify cnt formula    -> Clausify.mkClausifyTerm cnt formula
          Queens boardSize alg    -> Queens.mkQueensTerm boardSize alg
          Knights depth boardSize -> Knights.mkKnightsTerm depth boardSize
          LastPiece               -> LastPiece.mkLastPieceTerm
          Prime input             -> Prime.mkPrimeTerm input
  let result = unsafeEvaluateCek emptyBuiltins defaultCostModel program
  print . PLC.prettyPlcClassicDebug $ result
