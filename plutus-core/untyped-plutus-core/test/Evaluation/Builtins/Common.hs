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
import PlutusCore.Pretty
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
    => BuiltinSemanticsVariant fun
    -> (MachineParameters CekMachineCosts fun (CekValue uni fun ()) ->
            UPLC.Term Name uni fun () -> a)
    -> CostingPart uni fun -> TPLC.Term TyName Name uni fun () -> m a
typecheckAnd semvar action costingPart term = TPLC.runQuoteT $ do
    -- Here we don't use `getDefTypeCheckConfig`, to cover the absurd case where
    -- builtins can change their type according to their BuiltinSemanticsVariant
    tcConfig <- TypeCheckConfig defKindCheckConfig <$> builtinMeaningsToTypes semvar ()
    _ <- TPLC.inferType tcConfig term
    return . action runtime $ TPLC.eraseTerm term
    where
      runtime = mkMachineParameters semvar $
                   CostModel defaultCekMachineCosts costingPart

-- | Type check and evaluate a term, logging enabled.
typecheckEvaluateCek
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni, Pretty fun
       )
    => BuiltinSemanticsVariant fun
    -> CostingPart uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (EvaluationResult (UPLC.Term Name uni fun ()), [Text])
typecheckEvaluateCek semvar = typecheckAnd semvar $ unsafeEvaluateCek logEmitter

-- | Type check and evaluate a term, logging disabled.
typecheckEvaluateCekNoEmit
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni, Pretty fun
       )
    => BuiltinSemanticsVariant fun
    -> CostingPart uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (EvaluationResult (UPLC.Term Name uni fun ()))
typecheckEvaluateCekNoEmit semvar = typecheckAnd semvar unsafeEvaluateCekNoEmit

-- | Type check and convert a Plutus Core term to a Haskell value.
typecheckReadKnownCek
    :: ( MonadError (TPLC.Error uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni, Pretty fun
       , ReadKnown (UPLC.Term Name uni fun ()) a
       )
    => BuiltinSemanticsVariant fun
    -> CostingPart uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (Either (CekEvaluationException Name uni fun) a)
typecheckReadKnownCek semvar = typecheckAnd semvar readKnownCek
