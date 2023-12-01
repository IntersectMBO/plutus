{-# LANGUAGE LambdaCase #-}

-- editorconfig-checker-disable-file
module Opts where

import Data.Semigroup ((<>))
import Data.Text qualified as T
import Data.Text.IO qualified as T

import Control.Applicative
import Options.Applicative

import PlutusCore.Executable.Common
import PlutusCore.Executable.Parsers

-- the different budget modes of plc-agda
data BudgetMode  = Silent
                 | Counting
                 | Tallying

countingbudget :: Parser BudgetMode
countingbudget = flag' Counting
                 (  long "counting"
                 <> short 'c'
                 <> help "Run machine in counting mode and report results" )

tallyingbudget :: Parser BudgetMode
tallyingbudget = flag' Tallying
                 (  long "tallying"
                 <> short 't'
                 <> help "Run machine in tallying mode and report results" )

budgetmode :: Parser BudgetMode
budgetmode = asum
    [ countingbudget
    , tallyingbudget
    , pure Silent
    ]

-- The different evaluation modes of plc-agda
data EvalMode = U | TL | TCK | TCEK deriving stock (Show, Read)

data EvalOptions = EvalOpts Input Format EvalMode BudgetMode



evalMode :: Parser EvalMode
evalMode = option auto
  (  long "mode"
  <> short 'm'
  <> metavar "MODE"
  <> value TL
  <> showDefault
  <> help "Evaluation mode (U , TL, TCK, TCEK)" )

evalOpts :: Parser EvalOptions
evalOpts = EvalOpts <$> input <*> inputformat <*> evalMode <*> budgetmode

data TypecheckOptions = TCOpts Input Format

typecheckOpts :: Parser TypecheckOptions
typecheckOpts = TCOpts <$> input <*> inputformat

data Command = Eval EvalOptions
             | Typecheck TypecheckOptions

commands :: Parser Command
commands = hsubparser (
         command "evaluate"
          (info (Eval <$> evalOpts)
          (fullDesc <> progDesc "run a Plutus Core program"))
      <> command "typecheck"
          (info (Typecheck <$> typecheckOpts)
          (fullDesc <> progDesc "typecheck a Plutus Core program")))

execP :: IO Command
execP = execParser (info (commands <**> helper)
                    (fullDesc
                     <> progDesc "Plutus Core tool"
                     <> header "plc-agda - a Plutus Core implementation written in Agda"))
