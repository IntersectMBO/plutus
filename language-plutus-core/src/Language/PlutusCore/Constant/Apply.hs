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
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Control.Monad.Except
import           Crypto
import qualified Data.ByteString.Lazy                               as BSL
import qualified Data.ByteString.Lazy.Hash                          as Hash
import           Data.Coerce
import           Data.Int
import           Data.Proxy

-- | The result of evaluation of a builtin applied to some arguments.
data ConstAppResult uni ann
    = ConstAppSuccess (Term TyName Name uni ann)
      -- ^ Successfully computed a value.
    | ConstAppStuck
      -- ^ Not enough arguments.
    deriving (Show, Eq, Functor)

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
    :: forall e m args uni res.
       ( MonadError (ErrorWithCause uni e) m, AsUnliftingError e, AsConstAppError e uni
       , SpendBudget m uni, Closed uni, uni `Everywhere` ExMemoryUsage
       )
    => StagedBuiltinName
    -> TypeScheme uni args res
    -> FoldArgs args res
    -> FoldArgsEx args
    -> [Value TyName Name uni ExMemory]
    -> m (ConstAppResult uni ExMemory)
applyTypeSchemed name = go where
    go
        :: forall args'.
           TypeScheme uni args' res
        -> FoldArgs args' res
        -> FoldArgsEx args'
        -> [Value TyName Name uni ExMemory]
        -> m (ConstAppResult uni ExMemory)
    go (TypeSchemeResult _)        y _ args =
        -- TODO: The costing function is NOT run here. Might cause problems if there's never a TypeSchemeArrow.
        case args of
            -- TODO is `withMemory` a good idea here?
            [] -> pure . ConstAppSuccess $ withMemory $ makeKnown y    -- Computed the result.
            _  -> throwingWithCause _ConstAppError        -- Too many arguments.
                    (ExcessArgumentsConstAppError $ void <$> args)
                    Nothing
    go (TypeSchemeAllType _ schK)  f exF args =
        go (schK Proxy) f exF args
    go (TypeSchemeArrow _ schB)    f exF args = case args of
        []          -> pure ConstAppStuck                 -- Not enough arguments to compute.
        arg : args' -> do                                 -- Peel off one argument.
            -- Coerce the argument to a Haskell value.
            x <- readKnown $ void arg
            let budget = exF $ termAnn arg
            -- Apply the function to the coerced argument and proceed recursively.
            case schB of
                (TypeSchemeResult _) -> do
                    spendBudget (BBuiltin name) arg budget
                    go schB (f x) budget args'
                _ -> go schB (f x) budget args'

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyTypedBuiltinName
    :: ( MonadError (ErrorWithCause uni e) m, AsUnliftingError e, AsConstAppError e uni
       , SpendBudget m uni, Closed uni, uni `Everywhere` ExMemoryUsage
       )
    => TypedBuiltinName uni args res
    -> FoldArgs args res
    -> FoldArgsEx args
    -> [Value TyName Name uni ExMemory]
    -> m (ConstAppResult uni ExMemory)
applyTypedBuiltinName (TypedBuiltinName name schema) =
    applyTypeSchemed (StaticStagedBuiltinName name) schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyBuiltinName
    :: ( MonadError (ErrorWithCause uni e) m, AsUnliftingError e, AsConstAppError e uni
    , SpendBudget m uni, Closed uni, uni `Everywhere` ExMemoryUsage
    , GShow uni, GEq uni, DefaultUni <: uni
    )
    => CostModel -> BuiltinName -> [Value TyName Name uni ExMemory] -> m (ConstAppResult uni ExMemory)
applyBuiltinName params AddInteger           =
    applyTypedBuiltinName typedAddInteger           (+) (runCostingFunTwoArguments $ paramAddInteger params)
applyBuiltinName params SubtractInteger      =
    applyTypedBuiltinName typedSubtractInteger      (-) (runCostingFunTwoArguments $ paramSubtractInteger params)
applyBuiltinName params MultiplyInteger      =
    applyTypedBuiltinName typedMultiplyInteger      (*) (runCostingFunTwoArguments $ paramMultiplyInteger params)
applyBuiltinName params DivideInteger        =
    applyTypedBuiltinName typedDivideInteger        (nonZeroArg div) (runCostingFunTwoArguments $ paramDivideInteger params)
applyBuiltinName params QuotientInteger      =
    applyTypedBuiltinName typedQuotientInteger      (nonZeroArg quot) (runCostingFunTwoArguments $ paramQuotientInteger params)
applyBuiltinName params RemainderInteger     =
    applyTypedBuiltinName typedRemainderInteger     (nonZeroArg rem) (runCostingFunTwoArguments $ paramRemainderInteger params)
applyBuiltinName params ModInteger           =
    applyTypedBuiltinName typedModInteger           (nonZeroArg mod) (runCostingFunTwoArguments $ paramModInteger params)
applyBuiltinName params LessThanInteger      =
    applyTypedBuiltinName typedLessThanInteger      (<) (runCostingFunTwoArguments $ paramLessThanInteger params)
applyBuiltinName params LessThanEqInteger    =
    applyTypedBuiltinName typedLessThanEqInteger    (<=) (runCostingFunTwoArguments $ paramLessThanEqInteger params)
applyBuiltinName params GreaterThanInteger   =
    applyTypedBuiltinName typedGreaterThanInteger   (>) (runCostingFunTwoArguments $ paramGreaterThanInteger params)
applyBuiltinName params GreaterThanEqInteger =
    applyTypedBuiltinName typedGreaterThanEqInteger (>=) (runCostingFunTwoArguments $ paramGreaterThanEqInteger params)
applyBuiltinName params EqInteger            =
    applyTypedBuiltinName typedEqInteger            (==) (runCostingFunTwoArguments $ paramEqInteger params)
applyBuiltinName params Concatenate          =
    applyTypedBuiltinName typedConcatenate          (<>) (runCostingFunTwoArguments $ paramConcatenate params)
applyBuiltinName params TakeByteString       =
    applyTypedBuiltinName typedTakeByteString       (coerce BSL.take . integerToInt64) (runCostingFunTwoArguments $ paramTakeByteString params)
applyBuiltinName params DropByteString       =
    applyTypedBuiltinName typedDropByteString       (coerce BSL.drop . integerToInt64) (runCostingFunTwoArguments $ paramDropByteString params)
applyBuiltinName params SHA2                 =
    applyTypedBuiltinName typedSHA2                 (coerce Hash.sha2) (runCostingFunOneArgument $ paramSHA2 params)
applyBuiltinName params SHA3                 =
    applyTypedBuiltinName typedSHA3                 (coerce Hash.sha3) (runCostingFunOneArgument $ paramSHA3 params)
applyBuiltinName params VerifySignature      =
    applyTypedBuiltinName typedVerifySignature      (coerce $ verifySignature @EvaluationResult) (runCostingFunThreeArguments $ paramVerifySignature params)
applyBuiltinName params EqByteString         =
    applyTypedBuiltinName typedEqByteString         (==) (runCostingFunTwoArguments $ paramEqByteString params)
applyBuiltinName params LtByteString         =
    applyTypedBuiltinName typedLtByteString         (<) (runCostingFunTwoArguments $ paramLtByteString params)
applyBuiltinName params GtByteString         =
    applyTypedBuiltinName typedGtByteString         (>) (runCostingFunTwoArguments $ paramGtByteString params)
applyBuiltinName params IfThenElse           =
    applyTypedBuiltinName typedIfThenElse           (\b x y -> if b then x else y) (runCostingFunThreeArguments $ paramIfThenElse params)
