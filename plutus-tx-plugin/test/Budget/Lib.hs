{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-context #-}
module Budget.Lib where

import           Common

import qualified PlutusCore                               as PLC
import qualified PlutusCore.Evaluation.Machine.ExBudget   as PLC
import           PlutusTx.Code                            (CompiledCode, getPlc)
import qualified PlutusTx.Evaluation                      as PlutusTx
import qualified UntypedPlutusCore                        as UPLC
import qualified UntypedPlutusCore.Evaluation.Machine.Cek as UPLC

import           Control.Monad.Except                     (runExceptT)
import qualified Control.Monad.Reader                     as Reader
import qualified Data.Text                                as Text
import           System.FilePath                          ((</>))
import           Test.Tasty                               (TestName)

goldenBudget :: TestName -> CompiledCode a -> TestNested
goldenBudget name compiledCode = do
  path <- Reader.ask
  let budgetText = measureBudget compiledCode
  return $
    goldenVsText name
                 (foldr (</>) (name ++ ".budget.golden") path)
                 (maybe "" (Text.pack . show) budgetText)

measureBudget :: CompiledCode a  -> Maybe PLC.ExBudget
measureBudget compiledCode =
  let programE = PLC.runQuote
               $ runExceptT @PLC.FreeVariableError
               $ UPLC.unDeBruijnProgram
               $ getPlc compiledCode
   in case programE of
        Left _ -> Nothing
        Right program ->
          let (_, UPLC.TallyingSt _ budget, _) = PlutusTx.evaluateCekTrace program
           in Just budget
