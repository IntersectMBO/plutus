module Main where

import           Control.Monad
import           Options.Applicative
import           System.Environment

import           Control.Monad                                              ()
import qualified Data.Map                                                   as Map
import           Language.PlutusCore                                        (Name (..))
import           Language.PlutusCore.Builtins
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
  | Queens P.Integer [Queens.Algorithm]
  | Knights P.Integer P.Integer
  | LastPiece
  | Prime [P.Integer]

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
         P.<*> some (argument (eitherReader queensAlgorithmReader)
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
queensAlgorithmReader "bjbt"  = Right Queens.Bjbt
queensAlgorithmReader "bjbt'" = Right Queens.Bjbt'
queensAlgorithmReader "fc"    = Right Queens.Fc
queensAlgorithmReader alg     = Left $ "Unknown algorithm: " <> alg <> ". I know of: bt, bm, bjbt, bjbt' or fc."

lastpieceOptions :: Parser Command
lastpieceOptions = P.pure LastPiece

primeOptions :: Parser Command
primeOptions =
  Prime P.<$> some (argument auto (metavar "INPUT" P.<>
                                   help "The input number"))

options :: Parser Command
options = hsubparser
  ( command "clausify" (info clausifyOptions (progDesc "Run the clausify benchmark.")) P.<>
    command "queens" (info queensOptions (progDesc "Run the queens benchmark.")) P.<>
    command "knights" (info knightsOptions (progDesc "Run the knights benchmark")) P.<>
    command "lastpiece" (info lastpieceOptions (progDesc "Run the lastpiece benchmark")) P.<>
    command "prime" (info primeOptions (progDesc "Run the primes benchmark")) )

evaluateWithCek :: Term Name DefaultUni DefaultFun () -> EvaluationResult (Term Name DefaultUni DefaultFun ())
evaluateWithCek = unsafeEvaluateCek defBuiltinsRuntime

main :: IO ()
main = do
  cmd <- execParser (info (helper P.<*> options) idm)
  let program =
        case cmd of
          Clausify cnt formula    -> Clausify.mkClausifyTerm cnt formula
          Queens boardSize algs   -> Queens.mkQueensTerm boardSize algs
          Knights depth boardSize -> Knights.mkKnightsTerm depth boardSize
          LastPiece               -> LastPiece.mkLastPieceTerm
          Prime input             -> Prime.mkPrimeTerm input
  let result = evaluateWithCek program
  print . PLC.prettyPlcClassicDebug $ result
