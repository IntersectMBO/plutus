-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module FFI.Opts where

import Data.Foldable (asum)
import Options.Applicative hiding (asum)

import PlutusCore.Executable.Common
import PlutusCore.Executable.Parsers

import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekMachineCostsForTesting)
import PlutusCore.Evaluation.Machine.SimpleBuiltinCostModel
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts)


-- the different budget modes of plc-agda
data BudgetMode a = Silent
                 | Counting a
                 | Tallying a
      deriving Functor

countingbudget :: Parser (BudgetMode ())
countingbudget = flag' (Counting ())
                 (  long "counting"
                 <> short 'c'
                 <> help "Run machine in counting mode and report results" )

tallyingbudget :: Parser (BudgetMode ())
tallyingbudget = flag' (Tallying ())
                 (  long "tallying"
                 <> short 't'
                 <> help "Run machine in tallying mode and report results" )

budgetmode :: Parser (BudgetMode ())
budgetmode = asum
    [ countingbudget
    , tallyingbudget
    , pure Silent
    ]

-- The different evaluation modes of plc-agda
data EvalMode = U | TL | TCK | TCEK deriving stock (Show, Read)

data EvalOptions a = EvalOpts Input Format EvalMode (BudgetMode a)
  deriving Functor

evalMode :: Parser EvalMode
evalMode = option auto
  (  long "mode"
  <> short 'm'
  <> metavar "MODE"
  <> value TL
  <> showDefault
  <> help "Evaluation mode (U , TL, TCK, TCEK)" )

evalOpts :: Parser (EvalOptions ())
evalOpts = EvalOpts <$> input <*> inputformat <*> evalMode <*> budgetmode

data TypecheckOptions = TCOpts Input Format

typecheckOpts :: Parser TypecheckOptions
typecheckOpts = TCOpts <$> input <*> inputformat

data Command a = Eval (EvalOptions a)
             | Typecheck TypecheckOptions
          deriving Functor

commands :: Parser (Command ())
commands = hsubparser (
         command "evaluate"
          (info (Eval <$> evalOpts)
          (fullDesc <> progDesc "run a Plutus Core program"))
      <> command "typecheck"
          (info (Typecheck <$> typecheckOpts)
          (fullDesc <> progDesc "typecheck a Plutus Core program")))

-- A CostModel has all the information to run the Agda machine
-- with cost reporting
type CostModel = (CekMachineCosts , BuiltinCostMap)

addJSONParameters :: Command a -> Command CostModel
addJSONParameters = fmap (const (defaultCekMachineCostsForTesting, defaultSimpleBuiltinCostModel))

execP :: IO (Command CostModel)
execP = addJSONParameters <$> execParser (info (commands <**> helper)
                    (fullDesc
                     <> progDesc "Plutus Core tool"
                     <> header "plc-agda - a Plutus Core implementation written in Agda"))





