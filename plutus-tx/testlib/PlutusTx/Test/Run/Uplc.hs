{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module PlutusTx.Test.Run.Uplc where

import Prelude

import Control.Exception (SomeException (..))
import Control.Lens ((^.))
import Control.Monad.Except (ExceptT, MonadError (throwError))
import Data.Either.Extras (fromRightM)
import Data.Text (Text)
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Test (ToUPlc (..))
import PlutusIR.Test ()
import PlutusPrelude (unsafeFromRight, (.*))
import PlutusTx.Test.Orphans ()
import Test.Tasty.Extras ()
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

runPlcCek
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => [a]
  -> ExceptT
       SomeException
       IO
       (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
runPlcCek values = do
  ps <- traverse toUPlc values
  let p = foldl1 (unsafeFromRight .* UPLC.applyProgram) ps
  fromRightM (throwError . SomeException) $
    UPLC.evaluateCekNoEmit
      PLC.defaultCekParametersForTesting
      (p ^. UPLC.progTerm)

runPlcCekTrace
  :: (ToUPlc a PLC.DefaultUni PLC.DefaultFun)
  => [a]
  -> ExceptT
       SomeException
       IO
       ( [Text]
       , UPLC.CekExTally PLC.DefaultFun
       , UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ()
       )
runPlcCekTrace values = do
  ps <- traverse toUPlc values
  let p = foldl1 (unsafeFromRight .* UPLC.applyProgram) ps
  let (result, UPLC.TallyingSt tally _, logOut) =
        UPLC.runCek
          PLC.defaultCekParametersForTesting
          UPLC.tallying
          UPLC.logEmitter
          (p ^. UPLC.progTerm)
  res <- fromRightM (throwError . SomeException) result
  pure (logOut, tally, res)
