-- | Computing constant application.

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Apply
    ( ConstAppResult (..)
    , EvaluateConstApp
    , nonZeroArg
    , integerToInt64
    , applyTypeSchemed
    , applyBuiltinName
    , runApplyBuiltinName
    ) where

import           Crypto

import           Language.PlutusCore.Constant.DefaultUni
import           Language.PlutusCore.Constant.Dynamic.Instances   ()
import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                             as BSL
import qualified Data.ByteString.Lazy.Hash                        as Hash
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

-- | Default constant application computation that in case of 'ConstAppSuccess' returns
-- a 'Value'.
type EvaluateConstApp uni m ann = EvaluateT uni m (ConstAppResult uni ann)

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
    :: forall e m as uni r.
       (MonadError (ErrorWithCause uni e) m, AsUnliftingError e, AsConstAppError e uni)
    => TypeScheme uni as r
    -> FoldArgs as r
    -> [Value TyName Name uni ()]
    -> EvaluateConstApp uni m ()
applyTypeSchemed = go where
    go
        :: forall as'.
           TypeScheme uni as' r
        -> FoldArgs as' r
        -> [Value TyName Name uni ()]
        -> EvaluateConstApp uni m ()
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
    :: (MonadError (ErrorWithCause uni e) m, AsUnliftingError e, AsConstAppError e uni)
    => TypedBuiltinName uni as r
    -> FoldArgs as r
    -> [Value TyName Name uni ()]
    -> EvaluateConstApp uni m ()
applyTypedBuiltinName (TypedBuiltinName _ schema) = applyTypeSchemed schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyBuiltinName
    :: ( MonadError (ErrorWithCause uni e) m, AsUnliftingError e, AsConstAppError e uni
       , GShow uni, GEq uni, HasDefaultUni uni
       )
    => BuiltinName -> [Value TyName Name uni ()] -> EvaluateConstApp uni m ()
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
    applyTypedBuiltinName typedConcatenate          (coerce BSL.append)
applyBuiltinName TakeByteString       =
    applyTypedBuiltinName typedTakeByteString       (coerce BSL.take . integerToInt64)
applyBuiltinName DropByteString       =
    applyTypedBuiltinName typedDropByteString       (coerce BSL.drop . integerToInt64)
applyBuiltinName SHA2                 =
    applyTypedBuiltinName typedSHA2                 (coerce Hash.sha2)
applyBuiltinName SHA3                 =
    applyTypedBuiltinName typedSHA3                 (coerce Hash.sha3)
applyBuiltinName VerifySignature      =
    applyTypedBuiltinName typedVerifySignature      (coerce $ verifySignature @EvaluationResult)
applyBuiltinName EqByteString         =
    applyTypedBuiltinName typedEqByteString         (==)
applyBuiltinName LtByteString         =
    applyTypedBuiltinName typedLtByteString         (<)
applyBuiltinName GtByteString         =
    applyTypedBuiltinName typedGtByteString         (>)

-- | Apply a 'BuiltinName' to a list of 'Value's and evaluate the resulting computation usign the
-- given evaluator.
runApplyBuiltinName
    :: ( MonadError (ErrorWithCause uni e) m, AsUnliftingError e, AsConstAppError e uni
       , GShow uni, GEq uni, HasDefaultUni uni
       )
    => Evaluator Term uni m -> BuiltinName -> [Value TyName Name uni ()] -> m (ConstAppResult uni ())
runApplyBuiltinName eval name = runEvaluateT eval . applyBuiltinName name
