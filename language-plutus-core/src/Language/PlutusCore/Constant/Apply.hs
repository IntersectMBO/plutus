-- | Computing constant application.

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Apply
    ( ConstAppResult (..)
    , EvaluateConstApp
    , nonZeroArg
    , applyTypeSchemed
    , applyBuiltinName
    , runApplyBuiltinName
    ) where

import           Language.PlutusCore.Constant.Dynamic.Instances     ()
import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name

import           Control.Monad.Except
import           Crypto
import qualified Data.ByteString.Lazy                               as BSL
import qualified Data.ByteString.Lazy.Hash                          as Hash
import           Data.Proxy

-- | The result of evaluation of a builtin applied to some arguments.
data ConstAppResult ann
    = ConstAppSuccess (Term TyName Name ann)
      -- ^ Successfully computed a value.
    | ConstAppStuck
      -- ^ Not enough arguments.
    deriving (Show, Eq, Functor)

-- | Default constant application computation that in case of 'ConstAppSuccess' returns
-- a 'Value'.
type EvaluateConstApp m ann = EvaluateT m (ConstAppResult ann)

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: forall e m a exA r. (MonadError (ErrorWithCause e) m, AsUnliftingError e, AsConstAppError e, SpendBudget m)
    => StagedBuiltinName -> TypeScheme a exA r -> a -> exA -> [Value TyName Name ExMemory] -> EvaluateConstApp m ExMemory
applyTypeSchemed name = go where
    go
        :: forall b exB.
           TypeScheme b exB r
        -> b
        -> exB
        -> [Value TyName Name ExMemory]
        -> EvaluateConstApp m ExMemory
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
            x <- readKnownM $ void arg
            -- Apply the function to the coerced argument and proceed recursively.
            case schB of
                (TypeSchemeResult _) -> do
                    let
                        budget :: ExBudget
                        budget = (exF x)
                    lift $ spendBudget (BBuiltin name) arg budget
                    go schB (f x) budget args'
                _ -> go schB (f x) (exF x) args'

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyTypedBuiltinName
    :: (MonadError (ErrorWithCause e) m, AsUnliftingError e, AsConstAppError e, SpendBudget m)
    => TypedBuiltinName a exA r -> a -> exA -> [Value TyName Name ExMemory] -> EvaluateConstApp m ExMemory
applyTypedBuiltinName (TypedBuiltinName name schema) = applyTypeSchemed (StaticStagedBuiltinName name) schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
-- TODO all of these cost functions
applyBuiltinName
    :: (MonadError (ErrorWithCause e) m, AsUnliftingError e, AsConstAppError e, SpendBudget m)
    => BuiltinName -> [Value TyName Name ExMemory] -> EvaluateConstApp m ExMemory
applyBuiltinName AddInteger           =
    applyTypedBuiltinName typedAddInteger           (+) (\_ _ -> ExBudget 1 1)
applyBuiltinName SubtractInteger      =
    applyTypedBuiltinName typedSubtractInteger      (-) (\_ _ -> ExBudget 1 1)
applyBuiltinName MultiplyInteger      =
    applyTypedBuiltinName typedMultiplyInteger      (*) (\_ _ -> ExBudget 1 1)
applyBuiltinName DivideInteger        =
    applyTypedBuiltinName typedDivideInteger        (nonZeroArg div) (\_ _ -> ExBudget 1 1)
applyBuiltinName QuotientInteger      =
    applyTypedBuiltinName typedQuotientInteger      (nonZeroArg quot) (\_ _ -> ExBudget 1 1)
applyBuiltinName RemainderInteger     =
    applyTypedBuiltinName typedRemainderInteger     (nonZeroArg rem) (\_ _ -> ExBudget 1 1)
applyBuiltinName ModInteger           =
    applyTypedBuiltinName typedModInteger           (nonZeroArg mod) (\_ _ -> ExBudget 1 1)
applyBuiltinName LessThanInteger      =
    applyTypedBuiltinName typedLessThanInteger      (<) (\_ _ -> ExBudget 1 1)
applyBuiltinName LessThanEqInteger    =
    applyTypedBuiltinName typedLessThanEqInteger    (<=) (\_ _ -> ExBudget 1 1)
applyBuiltinName GreaterThanInteger   =
    applyTypedBuiltinName typedGreaterThanInteger   (>) (\_ _ -> ExBudget 1 1)
applyBuiltinName GreaterThanEqInteger =
    applyTypedBuiltinName typedGreaterThanEqInteger (>=) (\_ _ -> ExBudget 1 1)
applyBuiltinName EqInteger            =
    applyTypedBuiltinName typedEqInteger            (==) (\_ _ -> ExBudget 1 1)
applyBuiltinName Concatenate          =
    applyTypedBuiltinName typedConcatenate          (<>) (\_ _ -> ExBudget 1 1)
applyBuiltinName TakeByteString       =
    applyTypedBuiltinName typedTakeByteString       (BSL.take . fromIntegral) (\_ _ -> ExBudget 1 1)
applyBuiltinName DropByteString       =
    applyTypedBuiltinName typedDropByteString       (BSL.drop . fromIntegral) (\_ _ -> ExBudget 1 1)
applyBuiltinName SHA2                 =
    applyTypedBuiltinName typedSHA2                 Hash.sha2 (\_ -> ExBudget 1 1)
applyBuiltinName SHA3                 =
    applyTypedBuiltinName typedSHA3                 Hash.sha3 (\_ -> ExBudget 1 1)
applyBuiltinName VerifySignature      =
    applyTypedBuiltinName typedVerifySignature      verifySignature (\_ _ _ -> ExBudget 1 1)
applyBuiltinName EqByteString         =
    applyTypedBuiltinName typedEqByteString         (==) (\_ _ -> ExBudget 1 1)
applyBuiltinName LtByteString         =
    applyTypedBuiltinName typedLtByteString         (<) (\_ _ -> ExBudget 1 1)
applyBuiltinName GtByteString         =
    applyTypedBuiltinName typedGtByteString         (>) (\_ _ -> ExBudget 1 1)

-- | Apply a 'BuiltinName' to a list of 'Value's and evaluate the resulting computation usign the
-- given evaluator.
runApplyBuiltinName
    :: (MonadError (ErrorWithCause e) m, AsUnliftingError e, AsConstAppError e, SpendBudget m)
    => Evaluator Term m -> BuiltinName -> [Value TyName Name ExMemory] -> m (ConstAppResult ExMemory)
runApplyBuiltinName eval name = runEvaluateT eval . applyBuiltinName name
