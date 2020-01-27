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

import           Language.PlutusCore.Constant.Dynamic.Instances   ()
import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name

import           Control.Monad.Except
import           Crypto
import qualified Data.ByteString.Lazy                             as BSL
import qualified Data.ByteString.Lazy.Hash                        as Hash
import           Data.Proxy

-- | The result of evaluation of a builtin applied to some arguments.
data ConstAppResult
    = ConstAppSuccess (Term TyName Name ())
      -- ^ Successfully computed a value.
    | ConstAppStuck
      -- ^ Not enough arguments.
    deriving (Show, Eq)

-- | Default constant application computation that in case of 'ConstAppSuccess' returns
-- a 'Value'.
type EvaluateConstApp m = EvaluateT m ConstAppResult

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: forall e m a r. (MonadError (ErrorWithCause e) m, AsUnliftingError e, AsConstAppError e)
    => TypeScheme a r -> a -> [Value TyName Name ()] -> EvaluateConstApp m
applyTypeSchemed = go where
    go
        :: forall b.
           TypeScheme b r
        -> b
        -> [Value TyName Name ()]
        -> EvaluateConstApp m
    go (TypeSchemeResult _)        y args =
        case args of
            [] -> pure . ConstAppSuccess $ makeKnown y    -- Computed the result.
            _  -> throwingWithCause _ConstAppError        -- Too many arguments.
                    (ExcessArgumentsConstAppError args)
                    Nothing
    go (TypeSchemeAllType _ schK)  f args =
        go (schK Proxy) f args
    go (TypeSchemeArrow _ schB)    f args = case args of
        []          -> pure ConstAppStuck                 -- Not enough arguments to compute.
        arg : args' -> do                                 -- Peel off one argument.
            -- Coerce the argument to a Haskell value.
            x <- readKnownM arg
            -- Apply the function to the coerced argument and proceed recursively.
            go schB (f x) args'

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyTypedBuiltinName
    :: (MonadError (ErrorWithCause e) m, AsUnliftingError e, AsConstAppError e)
    => TypedBuiltinName a r -> a -> [Value TyName Name ()] -> EvaluateConstApp m
applyTypedBuiltinName (TypedBuiltinName _ schema) = applyTypeSchemed schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyBuiltinName
    :: (MonadError (ErrorWithCause e) m, AsUnliftingError e, AsConstAppError e)
    => BuiltinName -> [Value TyName Name ()] -> EvaluateConstApp m
applyBuiltinName AddInteger           =
    applyTypedBuiltinName typedAddInteger           (+)
applyBuiltinName SubtractInteger      =
    applyTypedBuiltinName typedSubtractInteger      (-)
applyBuiltinName MultiplyInteger      =
    applyTypedBuiltinName typedMultiplyInteger      (*)
applyBuiltinName DivideInteger        =
    applyTypedBuiltinName typedDivideInteger        (nonZeroArg div)
applyBuiltinName QuotientInteger      =
    applyTypedBuiltinName typedQuotientInteger      (nonZeroArg quot)
applyBuiltinName RemainderInteger     =
    applyTypedBuiltinName typedRemainderInteger     (nonZeroArg rem)
applyBuiltinName ModInteger           =
    applyTypedBuiltinName typedModInteger           (nonZeroArg mod)
applyBuiltinName LessThanInteger      =
    applyTypedBuiltinName typedLessThanInteger      (<)
applyBuiltinName LessThanEqInteger    =
    applyTypedBuiltinName typedLessThanEqInteger    (<=)
applyBuiltinName GreaterThanInteger   =
    applyTypedBuiltinName typedGreaterThanInteger   (>)
applyBuiltinName GreaterThanEqInteger =
    applyTypedBuiltinName typedGreaterThanEqInteger (>=)
applyBuiltinName EqInteger            =
    applyTypedBuiltinName typedEqInteger            (==)
applyBuiltinName Concatenate          =
    applyTypedBuiltinName typedConcatenate          (<>)
applyBuiltinName TakeByteString       =
    applyTypedBuiltinName typedTakeByteString       (BSL.take . fromIntegral)
applyBuiltinName DropByteString       =
    applyTypedBuiltinName typedDropByteString       (BSL.drop . fromIntegral)
applyBuiltinName SHA2                 =
    applyTypedBuiltinName typedSHA2                 Hash.sha2
applyBuiltinName SHA3                 =
    applyTypedBuiltinName typedSHA3                 Hash.sha3
applyBuiltinName VerifySignature      =
    applyTypedBuiltinName typedVerifySignature      verifySignature
applyBuiltinName EqByteString         =
    applyTypedBuiltinName typedEqByteString         (==)
applyBuiltinName LtByteString         =
    applyTypedBuiltinName typedLtByteString         (<)
applyBuiltinName GtByteString         =
    applyTypedBuiltinName typedGtByteString         (>)

-- | Apply a 'BuiltinName' to a list of 'Value's and evaluate the resulting computation usign the
-- given evaluator.
runApplyBuiltinName
    :: (MonadError (ErrorWithCause e) m, AsUnliftingError e, AsConstAppError e)
    => Evaluator Term m -> BuiltinName -> [Value TyName Name ()] -> m ConstAppResult
runApplyBuiltinName eval name = runEvaluateT eval . applyBuiltinName name
