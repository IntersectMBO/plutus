-- | Computing constant application.

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Apply
    ( ConstAppError (..)
    , EvaluateConstAppDef
    , nonZeroArg
    , applyTypeSchemed
    , applyBuiltinName
    , runApplyBuiltinName
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Constant.Dynamic.Instances ()
import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name

import           Control.Monad.Except
import           Control.Monad.Trans.Reader
import           Crypto
import qualified Data.ByteString.Lazy                           as BSL
import qualified Data.ByteString.Lazy.Hash                      as Hash
import           Data.Proxy
import           Data.Text                                      (Text)

-- | The type of constant applications errors.
data ConstAppError
    = ExcessArgumentsConstAppError [Value TyName Name ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | NonConstantConstAppError (Value TyName Name ())
    | UnreadableBuiltinConstAppError (Value TyName Name ()) Text
      -- ^ Could not construct denotation for a built-in.
    deriving (Show, Eq)

instance PrettyBy config (Term TyName Name ()) => PrettyBy config ConstAppError where
    prettyBy config (ExcessArgumentsConstAppError args)      = fold
        [ "A constant applied to too many arguments:", "\n"
        , "Excess ones are: ", prettyBy config args
        ]
    prettyBy config (NonConstantConstAppError arg)      = fold
        [ "An argument to a builtin type is not a constant:", "\n"
        , prettyBy config arg
        ]
    prettyBy config (UnreadableBuiltinConstAppError arg err) = fold
        [ "Could not construct denotation for a built-in:", "\n"
        , prettyBy config arg, "\n"
        , "The error was: "
        , pretty err
        ]

-- | Default constant application computation that in case of 'ConstAppSuccess' returns
-- a 'Value'.
type EvaluateConstAppDef m = EvaluateT m (Maybe (Value TyName Name ()))

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: MonadError Text m => TypeScheme a r -> a -> [Value TyName Name ()] -> EvaluateConstAppDef m
applyTypeSchemed = go where
    go
        :: MonadError Text m
        => TypeScheme a r
        -> a
        -> [Value TyName Name ()]
        -> EvaluateConstAppDef m
    go (TypeSchemeResult _)        y args =
        case args of
            [] -> pure . Just $ makeKnown y                               -- Computed the result.
            _  -> undefined -- ConstAppError $ ExcessArgumentsConstAppError args  -- Too many arguments.
    go (TypeSchemeAllType _ schK)  f args =
        go (schK Proxy) f args
    go (TypeSchemeArrow _ schB)    f args = case args of
        []          -> pure Nothing                       -- Not enough arguments to compute.
        arg : args' -> do                                 -- Peel off one argument.
            -- Coerce the argument to a Haskell value.
            x <- readKnownM arg
            -- Apply the function to the coerced argument and proceed recursively.
            go schB (f x) args'

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyTypedBuiltinName
    :: MonadError Text m
    => TypedBuiltinName a r -> a -> [Value TyName Name ()] -> EvaluateConstAppDef m
applyTypedBuiltinName (TypedBuiltinName _ schema) = applyTypeSchemed schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyBuiltinName
    :: MonadError Text m => BuiltinName -> [Value TyName Name ()] -> EvaluateConstAppDef m
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
    :: MonadError Text m
    => Evaluator Term m -> BuiltinName -> [Value TyName Name ()] -> m (Maybe (Term TyName Name ()))
runApplyBuiltinName eval name args = runReaderT (applyBuiltinName name args) eval
