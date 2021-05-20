-- | Computing constant application.

{-# LANGUAGE GADTs #-}

module PlutusCore.Constant.Apply
    ( applyTypeSchemed
    ) where

import           PlutusCore.Constant.Dynamic.Emit
import           PlutusCore.Constant.Typed
import           PlutusCore.Evaluation.Machine.ExBudget
import           PlutusCore.Evaluation.Machine.Exception
import           PlutusCore.Evaluation.Result

import           Control.Monad.Except
import           Data.Proxy

-- This INLINE pragma has the effect of making 'go' a local function definition at the use site.
-- This lets GHC be a bit more aggressive, in particular it helps get rid of the small overhead
-- from the constant arguments (e.g. the budget-spending function).
{-# INLINE applyTypeSchemed #-}
-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: forall exc err m args fun term res .
       ( exc ~ ErrorWithCause err term, MonadEmitter m, MonadError exc m
       , AsUnliftingError err, AsEvaluationFailure err, AsConstAppError err
       , ToExMemory term
       )
    =>
    (fun -> ExBudget -> m ())
    -> fun
    -> TypeScheme term args res
    -> FoldArgs args res
    -> FoldArgsEx args
    -> [term]
    -> m term
applyTypeSchemed spend name = go where
    go
        :: forall args'.
           TypeScheme term args' res
        -> FoldArgs args' res
        -> FoldArgsEx args'
        -> [term]
        -> m term
    go (TypeSchemeResult _)        y _ args =
        -- TODO: The costing function is NOT run here. Might cause problems if there's never a TypeSchemeArrow.
        case args of
            [] -> makeKnown y                            -- Computed the result.
            _  -> undefined
    go (TypeSchemeAll _ schK)    f exF args =
        go (schK Proxy) f exF args
    go (TypeSchemeArrow _ schB)  f exF args = case args of
        []          -> undefined
        arg : args' -> do                                 -- Peel off one argument.
            -- Coerce the argument to a Haskell value.
            x <- readKnown arg
            -- Note that it is very important to feed the costing function purely,
            -- otherwise (i.e. if instead of using a pure 'toExMemory' we use a function supplying
            -- an argument to 'exF' in a monadic fashion) execution time skyrockets for some reason.
            let exF' = exF $ toExMemory arg
            -- Apply the function to the coerced argument and proceed recursively.
            case schB of
                (TypeSchemeResult _) -> do
                    spend name exF'
                    go schB (f x) exF' args'
                _ -> go schB (f x) exF' args'
