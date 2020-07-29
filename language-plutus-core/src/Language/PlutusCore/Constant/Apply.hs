-- | Computing constant application.

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Apply
    ( ConstAppResult (..)
    , evaluationConstAppResult
    , nonZeroArg
    , integerToInt64
    , applyTypeSchemed
    , applyBuiltinName
    ) where

import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Universe

import           Control.Monad.Except
import           Crypto
import qualified Data.ByteString.Lazy                               as BSL
import qualified Data.ByteString.Lazy.Hash                          as Hash
import           Data.Coerce
import           Data.Int
import           Data.Proxy

-- This type is only needed because of how the CEK machine is currently structured.
-- Once we fix the machine, the 'ConstAppStuck' constructor will become obsolete,
-- making the type isomorphic to 'EvaluationResult'.
-- | The result of evaluation of a builtin applied to some arguments.
data ConstAppResult term
    = ConstAppFailure
    | ConstAppSuccess term
      -- ^ Successfully computed a value.
    | ConstAppStuck
      -- ^ Not enough arguments.
    deriving (Show, Eq, Functor)

evaluationConstAppResult :: EvaluationResult term -> ConstAppResult term
evaluationConstAppResult EvaluationFailure        = ConstAppFailure
evaluationConstAppResult (EvaluationSuccess term) = ConstAppSuccess term

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

integerToInt64 :: Integer -> Int64
integerToInt64 = fromIntegral

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: forall err m args term res.
       ( MonadError (ErrorWithCause err term) m, AsUnliftingError err, AsConstAppError err term
       , SpendBudget m term
       )
    => StagedBuiltinName
    -> TypeScheme term args res
    -> FoldArgs args res
    -> FoldArgsEx args
    -> [term]
    -> m (ConstAppResult term)
applyTypeSchemed name = go where
    go
        :: forall args'.
           TypeScheme term args' res
        -> FoldArgs args' res
        -> FoldArgsEx args'
        -> [term]
        -> m (ConstAppResult term)
    go (TypeSchemeResult _)        y _ args =
        -- TODO: The costing function is NOT run here. Might cause problems if there's never a TypeSchemeArrow.
        case args of
            [] -> pure . evaluationConstAppResult $ makeKnown y  -- Computed the result.
            _  -> throwingWithCause _ConstAppError               -- Too many arguments.
                    (ExcessArgumentsConstAppError args)
                    Nothing
    go (TypeSchemeAll _ _ schK)  f exF args =
        go (schK Proxy) f exF args
    go (TypeSchemeArrow _ schB)    f exF args = case args of
        []          -> pure ConstAppStuck                 -- Not enough arguments to compute.
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
                    -- Note that that if this fails, then the cause is reported to be @arg@, i.e.
                    -- the last argument in the builtin application being processed, not the whole
                    -- application. It would probably make sense to recreate the application here.
                    spendBudget (BBuiltin name) arg exF'
                    go schB (f x) exF' args'
                _ -> go schB (f x) exF' args'

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyTypedBuiltinName
    :: ( MonadError (ErrorWithCause err term) m, AsUnliftingError err, AsConstAppError err term
       , SpendBudget m term
       )
    => TypedBuiltinName term args res
    -> FoldArgs args res
    -> FoldArgsEx args
    -> [term]
    -> m (ConstAppResult term)
applyTypedBuiltinName (TypedBuiltinName name schema) =
    applyTypeSchemed (StaticStagedBuiltinName name) schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyBuiltinName
    :: forall m err uni term
    .  ( MonadError (ErrorWithCause err term) m, AsUnliftingError err, AsConstAppError err term
       , SpendBudget m term, HasConstantIn uni term, GShow uni, GEq uni, DefaultUni <: uni
       )
    => BuiltinName -> [term] -> m (ConstAppResult term)
applyBuiltinName name args = do
    params <- builtinCostParams
    case name of
        AddInteger ->
            applyTypedBuiltinName
                typedAddInteger
                (+)
                (runCostingFunTwoArguments $ paramAddInteger params)
                args
        SubtractInteger ->
            applyTypedBuiltinName
                typedSubtractInteger
                (-)
                (runCostingFunTwoArguments $ paramSubtractInteger params)
                args
        MultiplyInteger ->
            applyTypedBuiltinName
                typedMultiplyInteger
                (*)
                (runCostingFunTwoArguments $ paramMultiplyInteger params)
                args
        DivideInteger ->
            applyTypedBuiltinName
                typedDivideInteger
                (nonZeroArg div)
                (runCostingFunTwoArguments $ paramDivideInteger params)
                args
        QuotientInteger ->
            applyTypedBuiltinName
                typedQuotientInteger
                (nonZeroArg quot)
                (runCostingFunTwoArguments $ paramQuotientInteger params)
                args
        RemainderInteger ->
            applyTypedBuiltinName
                typedRemainderInteger
                (nonZeroArg rem)
                (runCostingFunTwoArguments $ paramRemainderInteger params)
                args
        ModInteger ->
            applyTypedBuiltinName
                typedModInteger
                (nonZeroArg mod)
                (runCostingFunTwoArguments $ paramModInteger params)
                args
        LessThanInteger ->
            applyTypedBuiltinName
                typedLessThanInteger
                (<)
                (runCostingFunTwoArguments $ paramLessThanInteger params)
                args
        LessThanEqInteger ->
            applyTypedBuiltinName
                typedLessThanEqInteger
                (<=)
                (runCostingFunTwoArguments $ paramLessThanEqInteger params)
                args
        GreaterThanInteger ->
            applyTypedBuiltinName
                typedGreaterThanInteger
                (>)
                (runCostingFunTwoArguments $ paramGreaterThanInteger params)
                args
        GreaterThanEqInteger ->
            applyTypedBuiltinName
                typedGreaterThanInteger
                (>=)
                (runCostingFunTwoArguments $ paramGreaterThanEqInteger params)
                args
        EqInteger ->
            applyTypedBuiltinName
                typedEqInteger
                (==)
                (runCostingFunTwoArguments $ paramEqInteger params)
                args
        Concatenate ->
            applyTypedBuiltinName
                typedConcatenate
                (<>)
                (runCostingFunTwoArguments $ paramConcatenate params)
                args
        TakeByteString ->
            applyTypedBuiltinName
                typedTakeByteString
                (coerce BSL.take . integerToInt64)
                (runCostingFunTwoArguments $ paramTakeByteString params)
                args
        DropByteString ->
            applyTypedBuiltinName
                typedDropByteString
                (coerce BSL.drop . integerToInt64)
                (runCostingFunTwoArguments $ paramDropByteString params)
                args
        SHA2 ->
            applyTypedBuiltinName
                typedSHA2
                (coerce Hash.sha2)
                (runCostingFunOneArgument $ paramSHA2 params)
                args
        SHA3 ->
            applyTypedBuiltinName
                typedSHA3
                (coerce Hash.sha3)
                (runCostingFunOneArgument $ paramSHA3 params)
                args
        VerifySignature ->
            applyTypedBuiltinName
                typedVerifySignature
                (coerce $ verifySignature @EvaluationResult)
                (runCostingFunThreeArguments $ paramVerifySignature params)
                args
        EqByteString ->
            applyTypedBuiltinName
                typedEqByteString
                (==)
                (runCostingFunTwoArguments $ paramEqByteString params)
                args
        LtByteString ->
            applyTypedBuiltinName
                typedLtByteString
                (<)
                (runCostingFunTwoArguments $ paramLtByteString params)
                args
        GtByteString ->
            applyTypedBuiltinName
                typedGtByteString
                (>)
                (runCostingFunTwoArguments $ paramGtByteString params)
                args
        IfThenElse ->
            applyTypedBuiltinName
                typedIfThenElse
                (\b x y -> if b then x else y)
                (runCostingFunThreeArguments $ paramIfThenElse params)
                args
