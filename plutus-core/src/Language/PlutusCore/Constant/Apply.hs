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
    ( nonZeroArg
    , integerToInt
    , applyTypeSchemed
    , applyStaticBuiltinName
    , builtinNameArities
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name                           (Name, TyName)
import           Language.PlutusCore.Universe

import           Control.Monad.Except
import           Crypto
import           Data.Array
import qualified Data.ByteString                                    as BS
import qualified Data.ByteString.Hash                               as Hash
import           Data.Proxy

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

integerToInt :: Integer -> Int
integerToInt = fromIntegral

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: forall err m args exBudgetCat term res.
       ( MonadError (ErrorWithCause err term) m, AsUnliftingError err, AsConstAppError err term
       , SpendBudget m exBudgetCat term
       )
    => BuiltinName
    -> TypeScheme term args res
    -> FoldArgs args res
    -> FoldArgsEx args
    -> [term]
    -> m (EvaluationResult term)
applyTypeSchemed name = go where
    go
        :: forall args'.
           TypeScheme term args' res
        -> FoldArgs args' res
        -> FoldArgsEx args'
        -> [term]
        -> m (EvaluationResult term)
    go (TypeSchemeResult _)        y _ args =
        -- TODO: The costing function is NOT run here. Might cause problems if there's never a TypeSchemeArrow.
        case args of
            [] -> pure $ makeKnown y                     -- Computed the result.
            _  -> throwingWithCause _ConstAppError       -- Too many arguments.
                    (TooManyArgumentsConstAppError name args)
                    Nothing
    go (TypeSchemeAll _ _ schK)  f exF args =
        go (schK Proxy) f exF args
    go (TypeSchemeArrow _ schB)  f exF args = case args of
        []          ->
            throwingWithCause _ConstAppError              -- Too few arguments.
                (TooFewArgumentsConstAppError name)
                Nothing
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
                    spendBudget (exBudgetBuiltin name) exF'
                    go schB (f x) exF' args'
                _ -> go schB (f x) exF' args'

-- | Apply a 'TypedStaticBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyTypedStaticBuiltinName
    :: ( MonadError (ErrorWithCause err term) m, AsUnliftingError err, AsConstAppError err term
       , SpendBudget m exBudgetCat term
       )
    => TypedStaticBuiltinName term args res
    -> FoldArgs args res
    -> FoldArgsEx args
    -> [term]
    -> m (EvaluationResult term)
applyTypedStaticBuiltinName (TypedStaticBuiltinName name schema) =
    applyTypeSchemed (StaticBuiltinName name) schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyStaticBuiltinName
    :: forall m err uni exBudgetCat term
    .  ( MonadError (ErrorWithCause err term) m, AsUnliftingError err, AsConstAppError err term
       , SpendBudget m exBudgetCat term, HasConstantIn uni term
       , GShow uni, GEq uni, DefaultUni <: uni
       )
    => StaticBuiltinName -> [term] -> m (EvaluationResult term)
applyStaticBuiltinName name args = do
    params <- builtinCostParams
    case name of
        AddInteger ->
            applyTypedStaticBuiltinName
                typedAddInteger
                (+)
                (runCostingFunTwoArguments $ paramAddInteger params)
                args
        SubtractInteger ->
            applyTypedStaticBuiltinName
                typedSubtractInteger
                (-)
                (runCostingFunTwoArguments $ paramSubtractInteger params)
                args
        MultiplyInteger ->
            applyTypedStaticBuiltinName
                typedMultiplyInteger
                (*)
                (runCostingFunTwoArguments $ paramMultiplyInteger params)
                args
        DivideInteger ->
            applyTypedStaticBuiltinName
                typedDivideInteger
                (nonZeroArg div)
                (runCostingFunTwoArguments $ paramDivideInteger params)
                args
        QuotientInteger ->
            applyTypedStaticBuiltinName
                typedQuotientInteger
                (nonZeroArg quot)
                (runCostingFunTwoArguments $ paramQuotientInteger params)
                args
        RemainderInteger ->
            applyTypedStaticBuiltinName
                typedRemainderInteger
                (nonZeroArg rem)
                (runCostingFunTwoArguments $ paramRemainderInteger params)
                args
        ModInteger ->
            applyTypedStaticBuiltinName
                typedModInteger
                (nonZeroArg mod)
                (runCostingFunTwoArguments $ paramModInteger params)
                args
        LessThanInteger ->
            applyTypedStaticBuiltinName
                typedLessThanInteger
                (<)
                (runCostingFunTwoArguments $ paramLessThanInteger params)
                args
        LessThanEqInteger ->
            applyTypedStaticBuiltinName
                typedLessThanEqInteger
                (<=)
                (runCostingFunTwoArguments $ paramLessThanEqInteger params)
                args
        GreaterThanInteger ->
            applyTypedStaticBuiltinName
                typedGreaterThanInteger
                (>)
                (runCostingFunTwoArguments $ paramGreaterThanInteger params)
                args
        GreaterThanEqInteger ->
            applyTypedStaticBuiltinName
                typedGreaterThanInteger
                (>=)
                (runCostingFunTwoArguments $ paramGreaterThanEqInteger params)
                args
        EqInteger ->
            applyTypedStaticBuiltinName
                typedEqInteger
                (==)
                (runCostingFunTwoArguments $ paramEqInteger params)
                args
        Concatenate ->
            applyTypedStaticBuiltinName
                typedConcatenate
                (<>)
                (runCostingFunTwoArguments $ paramConcatenate params)
                args
        TakeByteString ->
            applyTypedStaticBuiltinName
                typedTakeByteString
                (coerce BS.take . integerToInt)
                (runCostingFunTwoArguments $ paramTakeByteString params)
                args
        DropByteString ->
            applyTypedStaticBuiltinName
                typedDropByteString
                (coerce BS.drop . integerToInt)
                (runCostingFunTwoArguments $ paramDropByteString params)
                args
        SHA2 ->
            applyTypedStaticBuiltinName
                typedSHA2
                (coerce Hash.sha2)
                (runCostingFunOneArgument $ paramSHA2 params)
                args
        SHA3 ->
            applyTypedStaticBuiltinName
                typedSHA3
                (coerce Hash.sha3)
                (runCostingFunOneArgument $ paramSHA3 params)
                args
        VerifySignature ->
            applyTypedStaticBuiltinName
                typedVerifySignature
                (coerce $ verifySignature @EvaluationResult)
                (runCostingFunThreeArguments $ paramVerifySignature params)
                args
        EqByteString ->
            applyTypedStaticBuiltinName
                typedEqByteString
                (==)
                (runCostingFunTwoArguments $ paramEqByteString params)
                args
        LtByteString ->
            applyTypedStaticBuiltinName
                typedLtByteString
                (<)
                (runCostingFunTwoArguments $ paramLtByteString params)
                args
        GtByteString ->
            applyTypedStaticBuiltinName
                typedGtByteString
                (>)
                (runCostingFunTwoArguments $ paramGtByteString params)
                args
        IfThenElse ->
            applyTypedStaticBuiltinName
                typedIfThenElse
                (\b x y -> if b then x else y)
                (runCostingFunThreeArguments $ paramIfThenElse params)
                args


-- | An array mapping names of built-in functions to the arities of the functions,
-- represented as a list of (possibly interleaved) 'TermArg | TypeArg' values.
-- This is used in the evaluators (a) to detect when we have all of the arguments
-- for a builtin, so that it can be handed to the constant application machinery
-- for evaluation, and (b) to check that term arguments and type instantiations
-- occur in the expected order.
builtinNameArities :: Array StaticBuiltinName Arity
builtinNameArities =
    listArray (minBound, maxBound) $
        [minBound..maxBound] <&> \name ->
            withTypedStaticBuiltinName @_ @(Term TyName Name DefaultUni ()) name $
                \(TypedStaticBuiltinName _ sch) -> getArity sch
{-# NOINLINE builtinNameArities #-}  -- Just in case.
