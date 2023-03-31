{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

module Evaluation.Builtins.Common
    ( unsafeEvaluateCek
    , unsafeEvaluateCekNoEmit
    , readKnownCek
    , typecheckAnd
    , typecheckEvaluateCek
    , typecheckEvaluateCekNoEmit
    , typecheckReadKnownCek
    ) where

import PlutusCore qualified as TPLC
import PlutusCore.Builtin
import PlutusCore.Compiler.Erase qualified as TPLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Name
import PlutusCore.TypeCheck

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.Monad.Except
import Data.Text (Text)

-- | Type check and evaluate a term.
typecheckAnd
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , Closed uni, uni `Everywhere` ExMemoryUsage
       )
    => BuiltinVersion fun
    -> (MachineParameters CekMachineCosts fun (CekValue uni fun ()) ->
            UPLC.Term Name uni fun () -> a)
    -> CostingPart uni fun -> TPLC.Term TyName Name uni fun () -> m a
typecheckAnd ver action costingPart term = TPLC.runQuoteT $ do
    -- here we don't use `getDefTypeCheckConfig`, to cover the
    -- absurd case where versioned-builtins can change their type.
    tcConfig <- TypeCheckConfig defKindCheckConfig <$> builtinMeaningsToTypes ver ()
    _ <- TPLC.inferType tcConfig term
    return . action runtime $ TPLC.eraseTerm term
    where
      runtime = mkMachineParameters ver $
                   CostModel defaultCekMachineCosts costingPart

-- | Type check and evaluate a term, logging enabled.
typecheckEvaluateCek
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni fun
       )
    => BuiltinVersion fun
    -> CostingPart uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (EvaluationResult (UPLC.Term Name uni fun ()), [Text])
typecheckEvaluateCek ver = typecheckAnd ver $ unsafeEvaluateCek logEmitter

-- | Type check and evaluate a term, logging disabled.
typecheckEvaluateCekNoEmit
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni fun
       )
    => BuiltinVersion fun
    -> CostingPart uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (EvaluationResult (UPLC.Term Name uni fun ()))
typecheckEvaluateCekNoEmit ver = typecheckAnd ver unsafeEvaluateCekNoEmit

-- | Type check and convert a Plutus Core term to a Haskell value.
typecheckReadKnownCek
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni fun
       , ReadKnown (UPLC.Term Name uni fun ()) a
       )
    => BuiltinVersion fun
    -> CostingPart uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (Either (CekEvaluationException Name uni fun) a)
typecheckReadKnownCek ver = typecheckAnd ver readKnownCek
