{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module PlutusTx.Test.Run.Uplc where

import Prelude

import Control.Exception (SomeException (..))
import Control.Lens ((^.))
import Control.Monad.Except (ExceptT, MonadError (throwError))
import Data.Either.Extras (fromRightM)
import Data.Text (Text)
import PlutusCore (DefaultFun, DefaultUni)
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Test (ToUPlc (..))
import PlutusIR.Test ()
import PlutusTx.Test.Orphans ()
import Test.Tasty.Extras ()
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

type Term = UPLC.Term PLC.Name DefaultUni DefaultFun ()

runPlcCek
  :: ToUPlc a PLC.DefaultUni PLC.DefaultFun
  => a
  -> ExceptT
       SomeException
       IO
       (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
runPlcCek val = do
  term <- toUPlc val
  fromRightM (throwError . SomeException) $
    UPLC.evaluateCekNoEmit
      PLC.defaultCekParametersForTesting
      (term ^. UPLC.progTerm)

runPlcCekTrace
  :: ToUPlc a PLC.DefaultUni PLC.DefaultFun
  => a
  -> ExceptT
       SomeException
       IO
       ( [Text]
       , UPLC.CekExTally PLC.DefaultFun
       , UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ()
       )
runPlcCekTrace value = do
  term <- toUPlc value
  let UPLC.CekReport (UPLC.cekResultToEither -> result) (UPLC.TallyingSt tally _) logOut =
        UPLC.runCek
          PLC.defaultCekParametersForTesting
          UPLC.tallying
          UPLC.logEmitter
          (term ^. UPLC.progTerm)
  res <- fromRightM (throwError . SomeException) result
  pure (logOut, tally, res)

runPlcCekBudget
  :: ToUPlc a PLC.DefaultUni PLC.DefaultFun
  => a
  -> ExceptT
       SomeException
       IO
       (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun (), PLC.ExBudget)
runPlcCekBudget val = do
  term <- toUPlc val
  fromRightM (throwError . SomeException) $ do
    let
      (evalRes, UPLC.CountingSt budget) =
        UPLC.runCekNoEmit
          PLC.defaultCekParametersForTesting
          UPLC.counting
          (term ^. UPLC.progTerm)
    (,budget) <$> evalRes
