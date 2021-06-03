{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

module Evaluation.Builtins.Common
    ( typecheckAnd
    , typecheckEvaluateCek
    , typecheckEvaluateCekNoEmit
    , typecheckReadKnownCek
    ) where

import qualified PlutusCore                                      as TPLC
import           PlutusCore.Constant
import           PlutusCore.Default
import           PlutusCore.Evaluation.Machine.ExMemory
import           PlutusCore.Evaluation.Machine.MachineParameters
import           PlutusCore.Name

import qualified UntypedPlutusCore                               as UPLC
import           UntypedPlutusCore.Evaluation.Machine.Cek

import           Control.Monad.Except

-- | Type check and evaluate a term.
typecheckAnd
    :: (MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni)
    => (params -> UPLC.Term Name uni fun () -> a)
    -> params -> TPLC.Term TyName Name uni fun () -> m a
typecheckAnd action runtime term = TPLC.runQuoteT $ do
    tcConfig <- TPLC.getDefTypeCheckConfig ()
    _ <- TPLC.inferType tcConfig term
    return . action runtime $ UPLC.erase term

-- | Type check and evaluate a term, logging enabled.
typecheckEvaluateCek
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni fun
       )
    => MachineParameters CekMachineCosts CekValue uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (EvaluationResult (UPLC.Term Name uni fun ()), [String])
typecheckEvaluateCek = typecheckAnd unsafeEvaluateCek

-- | Type check and evaluate a term, logging disabled.
typecheckEvaluateCekNoEmit
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni fun
       )
    => MachineParameters CekMachineCosts CekValue uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (EvaluationResult (UPLC.Term Name uni fun ()))
typecheckEvaluateCekNoEmit = typecheckAnd unsafeEvaluateCekNoEmit

-- | Type check and convert a Plutus Core term to a Haskell value.
typecheckReadKnownCek
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni fun
       , KnownType (UPLC.Term Name uni fun ()) a
       )
    => MachineParameters CekMachineCosts CekValue uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (Either (CekEvaluationException uni fun) a)
typecheckReadKnownCek = typecheckAnd readKnownCek
