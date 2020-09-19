{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fwarn-missing-signatures     #-}
{-# OPTIONS_GHC -fno-warn-unused-imports      #-}

{-# OPTIONS_GHC -fexpose-all-unfoldings       #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr              #-}
{-# OPTIONS_GHC -fno-strictness               #-}
{-# OPTIONS_GHC -fno-worker-wrapper           #-}

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
import qualified Prelude                                                    as P

data Command =
    Clausify P.Integer Clausify.StaticFormula

clausifyFormulaReader :: String -> Maybe Clausify.StaticFormula
clausifyFormulaReader "5" = Just Clausify.F5
clausifyFormulaReader _   = Nothing

clausifyOptions :: Parser Command
clausifyOptions =
  Clausify P.<$> argument auto (metavar "COUNT")
           P.<*> argument (maybeReader clausifyFormulaReader)
                          (metavar "FORMULA")

options :: Parser Command
options = subparser
  ( command "clausify" (info clausifyOptions (progDesc "Run the clausify benchmark")) )

emptyBuiltins :: DynamicBuiltinNameMeanings (CekValue DefaultUni)
emptyBuiltins = DynamicBuiltinNameMeanings Map.empty

evaluateWithCek :: Term Name DefaultUni () -> EvaluationResult (Term Name DefaultUni ())
evaluateWithCek term =
  unsafeEvaluateCek emptyBuiltins defaultCostModel term

main :: IO ()
main = do
  let code = Clausify.mkClausifyTerm 1 Clausify.F6
      result = unsafeEvaluateCek (DynamicBuiltinNameMeanings Map.empty) defaultCostModel code
  print . PLC.prettyPlcClassicDebug $ result
