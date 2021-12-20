{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wno-orphans  #-}
module Lib where

import Common
import Control.Exception
import Control.Lens
import Control.Monad.Except
import Data.Text (Text)
import Flat (Flat)

import PlcTestUtils

import PlutusTx.Code

import PlutusCore qualified as PLC
import PlutusCore.Pretty

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek

instance (PLC.Closed uni, uni `PLC.Everywhere` Flat, uni `PLC.Everywhere` PrettyConst, PLC.GShow uni, Pretty fun, Flat fun) =>
            ToUPlc (CompiledCodeIn uni fun a) uni fun where
    toUPlc v = do
        v' <- catchAll $ getPlc v
        toUPlc v'

goldenPir
    :: (PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, uni `PLC.Everywhere` Flat, PLC.GShow uni, Pretty fun, Flat fun)
    => String -> CompiledCodeIn uni fun a -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ pretty $ getPir value

runPlcCek :: ToUPlc a PLC.DefaultUni PLC.DefaultFun => [a] -> ExceptT SomeException IO (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
runPlcCek values = do
     ps <- traverse toUPlc values
     let p = foldl1 UPLC.applyProgram ps
     either (throwError . SomeException) pure $ evaluateCekNoEmit PLC.defaultCekParameters (p ^. UPLC.progTerm)

runPlcCekTrace ::
     ToUPlc a PLC.DefaultUni PLC.DefaultFun =>
     [a] ->
     ExceptT SomeException IO ([Text], CekExTally PLC.DefaultFun, UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun ())
runPlcCekTrace values = do
     ps <- traverse toUPlc values
     let p = foldl1 UPLC.applyProgram ps
     let (result, TallyingSt tally _, logOut) = runCek PLC.defaultCekParameters tallying logEmitter (p ^. UPLC.progTerm)
     res <- either (throwError . SomeException) pure result
     pure (logOut, tally, res)

goldenEvalCek :: ToUPlc a PLC.DefaultUni PLC.DefaultFun => String -> [a] -> TestNested
goldenEvalCek name values = nestedGoldenVsDocM name $ prettyPlcClassicDebug <$> (rethrow $ runPlcCek values)

goldenEvalCekLog :: ToUPlc a PLC.DefaultUni PLC.DefaultFun => String -> [a] -> TestNested
goldenEvalCekLog name values = nestedGoldenVsDocM name $ pretty . view _1 <$> (rethrow $ runPlcCekTrace values)
