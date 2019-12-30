-- | Computing constant application.

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Erasure.Untyped.Constant.Apply
    ( ConstAppError (..)
    , ConstAppResult (..)
    , ConstAppResultDef
    , EvaluateConstApp
    , EvaluateConstAppDef
    , nonZeroArg
    , makeConstAppResult
    , runEvaluateConstApp
    , applyTypeSchemed
    , applyBuiltinName
    , runApplyBuiltinName
    ) where

import qualified Language.PlutusCore.Core                                       as PLC
import           Language.PlutusCore.Erasure.Untyped.Constant.Dynamic.Instances ()
import           Language.PlutusCore.Erasure.Untyped.Constant.Name
import           Language.PlutusCore.Erasure.Untyped.Constant.Typed
import           Language.PlutusCore.Erasure.Untyped.Evaluation.Result
import           Language.PlutusCore.Erasure.Untyped.Instance.Eq                ()
import           Language.PlutusCore.Erasure.Untyped.Term
import           Language.PlutusCore.Name
import           PlutusPrelude

import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Inner
import           Crypto
import qualified Data.ByteString.Lazy                                           as BSL
import qualified Data.ByteString.Lazy.Hash                                      as Hash
import           Data.Proxy
import           Data.Text                                                      (Text)

-- | The type of constant applications errors.
data ConstAppError
    = ExcessArgumentsConstAppError [Value Name ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | NonConstantConstAppError (Value Name ())
    | UnreadableBuiltinConstAppError (Value Name ()) Text
      -- ^ Could not construct denotation for a built-in.
    deriving (Show, Eq)

-- | The type of constant applications results.
data ConstAppResult a
    = ConstAppSuccess a
      -- ^ Successfully computed a value.
    | ConstAppFailure
      -- ^ Not enough gas.
    | ConstAppStuck
      -- ^ Not enough arguments.
    | ConstAppError ConstAppError
      -- ^ An internal error occurred during evaluation.
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance Applicative ConstAppResult where
    pure = ConstAppSuccess

    ConstAppSuccess f <*> a = fmap f a
    ConstAppFailure   <*> _ = ConstAppFailure
    ConstAppStuck     <*> _ = ConstAppStuck
    ConstAppError err <*> _ = ConstAppError err

instance Monad ConstAppResult where
    ConstAppSuccess x >>= f = f x
    ConstAppFailure   >>= _ = ConstAppFailure
    ConstAppStuck     >>= _ = ConstAppStuck
    ConstAppError err >>= _ = ConstAppError err

type ConstAppResultDef = ConstAppResult (Term Name ())

instance PrettyBy config (Term Name ()) => PrettyBy config ConstAppError where
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

instance ( PrettyBy config (Value Name ())
         , PrettyBy config a
         ) => PrettyBy config (ConstAppResult a) where
    prettyBy config (ConstAppSuccess res) = prettyBy config res
    prettyBy _      ConstAppFailure       = "Constant application failure"
    prettyBy _      ConstAppStuck         = "Stuck constant applcation"
    prettyBy config (ConstAppError err)   = prettyBy config err

-- | Constant application computation runs in a monad @m@, requires an evaluator and
-- returns a 'ConstAppResult'.
type EvaluateConstApp m = EvaluateT (InnerT ConstAppResult) m

-- | Default constant application computation that in case of 'ConstAppSuccess' returns
-- a 'Value'.
type EvaluateConstAppDef m = EvaluateConstApp m (Value Name ())

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

-- | Evaluate a constant application computation using the given evaluator.
runEvaluateConstApp :: Evaluator Term m -> EvaluateConstApp m a -> m (ConstAppResult a)
runEvaluateConstApp eval = unInnerT . runEvaluateT eval

-- | Lift the result of a constant application to a constant application computation.
liftConstAppResult :: Monad m => ConstAppResult a -> EvaluateConstApp m a
-- Could it be @yield . yield@?
liftConstAppResult = EvaluateT . lift . yield

-- | Same as 'makeBuiltin', but returns a 'ConstAppResult'.
makeConstAppResult :: KnownType a => a -> ConstAppResultDef
makeConstAppResult = pure . makeKnown

-- | Convert a PLC constant (unwrapped from 'Value') into the corresponding Haskell value.
-- Checks that the constant is of a given built-in type.
extractBuiltin :: (Monad m, KnownType a) => Value Name () -> EvaluateConstApp m a
extractBuiltin value =
    thoist (InnerT . fmap nat . runReflectT) $ readKnownM value where
        nat :: EvaluationResult (Either Text a) -> ConstAppResult a
        nat EvaluationFailure              = ConstAppFailure
        nat (EvaluationSuccess (Left err)) = ConstAppError $ UnreadableBuiltinConstAppError value err
        nat (EvaluationSuccess (Right x )) = ConstAppSuccess x

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: Monad m => TypeScheme a r -> a -> [Value Name ()] -> EvaluateConstAppDef m
applyTypeSchemed = go where
    go
        :: Monad m
        => TypeScheme a r
        -> a
        -> [Value Name ()]
        -> EvaluateConstAppDef m
    go (TypeSchemeResult _)        y args =
        liftConstAppResult $ case args of
            [] -> makeConstAppResult y                               -- Computed the result.
            _  -> ConstAppError $ ExcessArgumentsConstAppError args  -- Too many arguments.
    go (TypeSchemeAllType _ schK)  f args =
        go (schK Proxy) f args
    go (TypeSchemeArrow _ schB)    f args = case args of
        []          -> liftConstAppResult ConstAppStuck   -- Not enough arguments to compute.
        arg : args' -> do                                 -- Peel off one argument.
            -- Coerce the argument to a Haskell value.
            x <- extractBuiltin arg
            -- Apply the function to the coerced argument and proceed recursively.
            go schB (f x) args'

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyTypedBuiltinName
    :: Monad m => TypedBuiltinName a r -> a -> [Value Name ()] -> EvaluateConstAppDef m
applyTypedBuiltinName (TypedBuiltinName _ schema) = applyTypeSchemed schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyBuiltinName
    :: Monad m => PLC.BuiltinName -> [Value Name ()] -> EvaluateConstAppDef m
applyBuiltinName PLC.AddInteger           =
    applyTypedBuiltinName typedAddInteger           (+)
applyBuiltinName PLC.SubtractInteger      =
    applyTypedBuiltinName typedSubtractInteger      (-)
applyBuiltinName PLC.MultiplyInteger      =
    applyTypedBuiltinName typedMultiplyInteger      (*)
applyBuiltinName PLC.DivideInteger        =
    applyTypedBuiltinName typedDivideInteger        (nonZeroArg div)
applyBuiltinName PLC.QuotientInteger      =
    applyTypedBuiltinName typedQuotientInteger      (nonZeroArg quot)
applyBuiltinName PLC.RemainderInteger     =
    applyTypedBuiltinName typedRemainderInteger     (nonZeroArg rem)
applyBuiltinName PLC.ModInteger           =
    applyTypedBuiltinName typedModInteger           (nonZeroArg mod)
applyBuiltinName PLC.LessThanInteger      =
    applyTypedBuiltinName typedLessThanInteger      (<)
applyBuiltinName PLC.LessThanEqInteger    =
    applyTypedBuiltinName typedLessThanEqInteger    (<=)
applyBuiltinName PLC.GreaterThanInteger   =
    applyTypedBuiltinName typedGreaterThanInteger   (>)
applyBuiltinName PLC.GreaterThanEqInteger =
    applyTypedBuiltinName typedGreaterThanEqInteger (>=)
applyBuiltinName PLC.EqInteger            =
    applyTypedBuiltinName typedEqInteger            (==)
applyBuiltinName PLC.Concatenate          =
    applyTypedBuiltinName typedConcatenate          (<>)
applyBuiltinName PLC.TakeByteString       =
    applyTypedBuiltinName typedTakeByteString       (BSL.take . fromIntegral)
applyBuiltinName PLC.DropByteString       =
    applyTypedBuiltinName typedDropByteString       (BSL.drop . fromIntegral)
applyBuiltinName PLC.SHA2                 =
    applyTypedBuiltinName typedSHA2                 Hash.sha2
applyBuiltinName PLC.SHA3                 =
    applyTypedBuiltinName typedSHA3                 Hash.sha3
applyBuiltinName PLC.VerifySignature      =
    applyTypedBuiltinName typedVerifySignature      verifySignature
applyBuiltinName PLC.EqByteString         =
    applyTypedBuiltinName typedEqByteString         (==)
applyBuiltinName PLC.LtByteString         =
    applyTypedBuiltinName typedLtByteString         (<)
applyBuiltinName PLC.GtByteString         =
    applyTypedBuiltinName typedGtByteString         (>)

-- | Apply a 'BuiltinName' to a list of 'Value's and evaluate the resulting computation usign the
-- given evaluator.
runApplyBuiltinName
    :: Monad m => Evaluator Term m -> PLC.BuiltinName -> [Value Name ()] -> m ConstAppResultDef
runApplyBuiltinName eval name = runEvaluateConstApp eval . applyBuiltinName name
