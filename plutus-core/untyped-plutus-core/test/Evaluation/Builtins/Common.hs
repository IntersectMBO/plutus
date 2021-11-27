{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}

module Evaluation.Builtins.Common
    ( typecheckAnd
    , typecheckEvaluateCek
    , typecheckEvaluateCekNoEmit
    , typecheckReadKnownCek
    ) where

import PlutusCore qualified as TPLC
import PlutusCore.Constant
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Name

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import Control.Monad.Except
import Data.Text (Text)

-- | Type check and evaluate a term.
typecheckAnd
    :: (MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni)
    => ((forall s. MachineParameters CekMachineCosts fun (CekM uni fun s) (UPLC.Term Name uni fun ()) (CekValue uni fun s)) -> UPLC.Term Name uni fun () -> a)
    -> (forall s. MachineParameters CekMachineCosts fun (CekM uni fun s) (UPLC.Term Name uni fun ()) (CekValue uni fun s)) -> TPLC.Term TyName Name uni fun () -> m a
typecheckAnd action runtime term = TPLC.runQuoteT $ do
    tcConfig <- TPLC.getDefTypeCheckConfig ()
    _ <- TPLC.inferType tcConfig term
    return . action runtime $ UPLC.erase term

-- | Type check and evaluate a term, logging enabled.
typecheckEvaluateCek
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni fun
       )
    => (forall s. MachineParameters CekMachineCosts fun (CekM uni fun s) (UPLC.Term Name uni fun ()) (CekValue uni fun s))
    -> TPLC.Term TyName Name uni fun ()
    -> m (EvaluationResult (UPLC.Term Name uni fun ()), [Text])
typecheckEvaluateCek = typecheckAnd $ unsafeEvaluateCek logEmitter

-- | Type check and evaluate a term, logging disabled.
typecheckEvaluateCekNoEmit
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni fun
       )
    => (forall s. MachineParameters CekMachineCosts fun (CekM uni fun s) (UPLC.Term Name uni fun ()) (CekValue uni fun s))
    -> TPLC.Term TyName Name uni fun ()
    -> m (EvaluationResult (UPLC.Term Name uni fun ()))
typecheckEvaluateCekNoEmit = typecheckAnd unsafeEvaluateCekNoEmit

-- | Type check and convert a Plutus Core term to a Haskell value.
typecheckReadKnownCek
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni fun
       , KnownType (UPLC.Term Name uni fun ()) a
       )
    => (forall s. MachineParameters CekMachineCosts fun (CekM uni fun s) (UPLC.Term Name uni fun ()) (CekValue uni fun s))
    -> TPLC.Term TyName Name uni fun ()
    -> m (Either (CekEvaluationException uni fun) a)
typecheckReadKnownCek = typecheckAnd readKnownCek
