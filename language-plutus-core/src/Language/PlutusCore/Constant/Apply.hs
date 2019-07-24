-- | Computing constant application.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Apply
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

import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type        (BuiltinName (..))
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Inner
import           Crypto
import qualified Data.ByteString.Lazy                  as BSL
import qualified Data.ByteString.Lazy.Hash             as Hash
import           Data.GADT.Compare
import           Data.Proxy
import           Data.Text                             (Text)

-- | The type of constant applications errors.
data ConstAppError uni
    = ExcessArgumentsConstAppError [Value TyName Name uni ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | NonConstantConstAppError (Value TyName Name uni ())
    | UnreadableBuiltinConstAppError (Value TyName Name uni ()) Text
      -- ^ Could not construct denotation for a built-in.
    deriving (Show, Eq)

-- | The type of constant applications results.
data ConstAppResult uni a
    = ConstAppSuccess a
      -- ^ Successfully computed a value.
    | ConstAppFailure
      -- ^ Not enough gas.
    | ConstAppStuck
      -- ^ Not enough arguments.
    | ConstAppError (ConstAppError uni)
      -- ^ An internal error occurred during evaluation.
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance Applicative (ConstAppResult uni) where
    pure = ConstAppSuccess

    ConstAppSuccess f <*> a = fmap f a
    ConstAppFailure   <*> _ = ConstAppFailure
    ConstAppStuck     <*> _ = ConstAppStuck
    ConstAppError err <*> _ = ConstAppError err

instance Monad (ConstAppResult uni) where
    ConstAppSuccess x >>= f = f x
    ConstAppFailure   >>= _ = ConstAppFailure
    ConstAppStuck     >>= _ = ConstAppStuck
    ConstAppError err >>= _ = ConstAppError err

type ConstAppResultDef uni = ConstAppResult uni (Term TyName Name uni ())

instance PrettyBy config (Term TyName Name uni ()) => PrettyBy config (ConstAppError uni) where
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

instance ( PrettyBy config (Value TyName Name uni ())
         , PrettyBy config a
         ) => PrettyBy config (ConstAppResult uni a) where
    prettyBy config (ConstAppSuccess res) = prettyBy config res
    prettyBy _      ConstAppFailure       = "Constant application failure"
    prettyBy _      ConstAppStuck         = "Stuck constant applcation"
    prettyBy config (ConstAppError err)   = prettyBy config err

-- | Constant application computation runs in a monad @m@, requires an evaluator and
-- returns a 'ConstAppResult'.
type EvaluateConstApp uni m = EvaluateT uni (InnerT (ConstAppResult uni)) m

-- -- | Constant application computation runs in a monad @m@, requires an evaluator and
-- -- returns a 'ConstAppResult'.
-- type EvaluateConstApp uni m = InnerT (ConstAppResult uni) m

-- | Default constant application computation that in case of 'ConstAppSuccess' returns
-- a 'Value'.
type EvaluateConstAppDef uni m = EvaluateConstApp uni m (Value TyName Name uni ())

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

-- | Evaluate a constant application computation using the given evaluator.
runEvaluateConstApp :: Evaluator Term uni m -> EvaluateConstApp uni m a -> m (ConstAppResult uni a)
runEvaluateConstApp eval = unInnerT . runEvaluateT eval

-- | Lift the result of a constant application to a constant application computation.
liftConstAppResult :: Monad m => ConstAppResult uni a -> EvaluateConstApp uni m a
-- Could it be @yield . yield@?
liftConstAppResult = EvaluateT . lift . yield

-- | Same as 'makeBuiltin', but returns a 'ConstAppResult'.
-- makeConstAppResult :: uni `Includes` a => a -> ConstAppResultDef uni
-- makeConstAppResult = pure . Constant () . SomeOf knownUni
makeConstAppResult :: KnownType a uni => a -> ConstAppResultDef uni
makeConstAppResult = pure . makeKnown

-- | Convert a PLC constant (unwrapped from 'Value') into the corresponding Haskell value.
-- Checks that the constant is of a given built-in type.
extractBuiltin
    :: forall m uni a. (Monad m, KnownType a uni)
    => Value TyName Name uni () -> EvaluateConstApp uni m a
-- -- TODO: this code makes perfect sense and is what we're going to use in future,
-- -- but currently it's commented out, because we emulate the old machinery using the new one.
-- extractBuiltin value@(Constant _ (SomeOf uni x)) = case geq uni $ knownUni @uni @a of
--     -- TODO: add an 'IllTypedApplication' error or something like that.
--     -- TODO: change errors in general.
--     Nothing   -> liftConstAppResult $ ConstAppError $ UnreadableBuiltinConstAppError value "blah-blah"
--     Just Refl -> pure x
extractBuiltin value                             =
    thoist (InnerT . fmap nat . runReflectT) $ readKnownM value where
        nat :: forall b. EvaluationResult (Either Text b) -> ConstAppResult uni b
        nat EvaluationFailure              = ConstAppFailure
        nat (EvaluationSuccess (Left err)) = ConstAppError $ UnreadableBuiltinConstAppError value err
        nat (EvaluationSuccess (Right x )) = ConstAppSuccess x

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: (Monad m, GEq uni)
    => TypeScheme uni a r -> a -> [Value TyName Name uni ()] -> EvaluateConstAppDef uni m
applyTypeSchemed = go where
    go
        :: (Monad m, GEq uni)
        => TypeScheme uni a r
        -> a
        -> [Value TyName Name uni ()]
        -> EvaluateConstAppDef uni m
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
    :: (Monad m, GEq uni)
    => TypedBuiltinName uni a r
    -> a
    -> [Value TyName Name uni ()]
    -> EvaluateConstAppDef uni m
applyTypedBuiltinName (TypedBuiltinName _ schema) = applyTypeSchemed schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyBuiltinName
    :: (Monad m, Evaluable uni)
    => BuiltinName -> [Value TyName Name uni ()] -> EvaluateConstAppDef uni m
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
    :: (Monad m, Evaluable uni)
    => Evaluator Term uni m
    -> BuiltinName
    -> [Value TyName Name uni ()]
    -> m (ConstAppResultDef uni)
runApplyBuiltinName eval name = runEvaluateConstApp eval . applyBuiltinName name
