{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

module Budget.Lib where

import Common

import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusTx.Code (CompiledCode, getPlc)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

import Control.Lens
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader qualified as Reader
import Data.Text qualified as Text
import System.FilePath ((</>))
import Test.Tasty (TestName)

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
               $ traverseOf UPLC.progTerm UPLC.unDeBruijnTerm
               $ getPlc compiledCode
   in case programE of
        Left _ -> Nothing
        Right program ->
          let (_, UPLC.TallyingSt _ budget) = UPLC.runCekNoEmit PLC.defaultCekParameters UPLC.tallying $ program ^. UPLC.progTerm
           in Just budget
