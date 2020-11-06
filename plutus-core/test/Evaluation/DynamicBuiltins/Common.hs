{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

module Evaluation.DynamicBuiltins.Common
    ( typecheckAnd
    , typecheckEvaluateCek
    , typecheckReadKnownCek
    ) where

import           PlutusPrelude

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory

import           Control.Monad.Except

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckAnd
    :: (MonadError (Error uni fun ()) m, ToBuiltinMeaning uni fun, GShow uni, GEq uni)
    => (BuiltinsRuntime fun (CekValue uni fun) -> Term TyName Name uni fun () -> a)
    -> BuiltinsRuntime fun (CekValue uni fun) -> Term TyName Name uni fun () -> m a
typecheckAnd action runtime term = runQuoteT $ do
    tcConfig <- getDefTypeCheckConfig ()
    _ <- inferType tcConfig term
    -- The bang is important in order to force the effects of a computation regardless of whether
    -- the result of the computation is forced or not.
    return $! action runtime term

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckEvaluateCek
    :: ( MonadError (Error uni fun ()) m, ToBuiltinMeaning uni fun
       , GShow uni, GEq uni, Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Typeable uni, Typeable fun, Pretty fun, Hashable fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term TyName Name uni fun ()
    -> m (EvaluationResult (Term TyName Name uni fun ()))
typecheckEvaluateCek = typecheckAnd unsafeEvaluateCek

-- | Type check and convert a Plutus Core term to a Haskell value.
typecheckReadKnownCek
    :: ( MonadError (Error uni fun ()) m, ToBuiltinMeaning uni fun
       , KnownType (Term TyName Name uni fun ()) a, GShow uni, GEq uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Hashable fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term TyName Name uni fun ()
    -> m (Either (CekEvaluationException uni fun) a)
typecheckReadKnownCek = typecheckAnd readKnownCek
