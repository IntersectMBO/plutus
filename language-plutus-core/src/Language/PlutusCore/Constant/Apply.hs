{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
-- | Computing constant application.

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
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

-- import           Language.PlutusCore.Constant.Dynamic.Instances ()
-- import           Language.PlutusCore.Constant.Name
-- import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Constant.Universe
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
import           Data.Proxy
import           Data.Text                             (Text)
import           Data.GADT.Compare

-- | The type of constant applications errors.
data ConstAppError con
    = ExcessArgumentsConstAppError [Value TyName Name con ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | NonConstantConstAppError (Value TyName Name con ())
    | UnreadableBuiltinConstAppError (Value TyName Name con ()) Text
      -- ^ Could not construct denotation for a built-in.
    deriving (Show, Eq)

-- | The type of constant applications results.
data ConstAppResult con a
    = ConstAppSuccess a
      -- ^ Successfully computed a value.
    | ConstAppFailure
      -- ^ Not enough gas.
    | ConstAppStuck
      -- ^ Not enough arguments.
    | ConstAppError (ConstAppError con)
      -- ^ An internal error occurred during evaluation.
    deriving (Show, Eq, Functor, Foldable, Traversable)

instance Applicative (ConstAppResult con) where
    pure = ConstAppSuccess

    ConstAppSuccess f <*> a = fmap f a
    ConstAppFailure   <*> _ = ConstAppFailure
    ConstAppStuck     <*> _ = ConstAppStuck
    ConstAppError err <*> _ = ConstAppError err

instance Monad (ConstAppResult con) where
    ConstAppSuccess x >>= f = f x
    ConstAppFailure   >>= _ = ConstAppFailure
    ConstAppStuck     >>= _ = ConstAppStuck
    ConstAppError err >>= _ = ConstAppError err

type ConstAppResultDef uni = ConstAppResult (ValueIn uni) (Term TyName Name (ValueIn uni) ())

instance PrettyBy config (Term TyName Name con ()) => PrettyBy config (ConstAppError con) where
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

instance ( PrettyBy config (Value TyName Name con ())
         , PrettyBy config a
         ) => PrettyBy config (ConstAppResult con a) where
    prettyBy config (ConstAppSuccess res) = prettyBy config res
    prettyBy _      ConstAppFailure       = "Constant application failure"
    prettyBy _      ConstAppStuck         = "Stuck constant applcation"
    prettyBy config (ConstAppError err)   = prettyBy config err

-- | Constant application computation runs in a monad @m@, requires an evaluator and
-- returns a 'ConstAppResult'.
type EvaluateConstApp uni m = EvaluateT uni (InnerT (ConstAppResult (ValueIn uni))) m

-- -- | Constant application computation runs in a monad @m@, requires an evaluator and
-- -- returns a 'ConstAppResult'.
-- type EvaluateConstApp uni m = InnerT (ConstAppResult (ValueIn uni)) m

-- | Default constant application computation that in case of 'ConstAppSuccess' returns
-- a 'Value'.
type EvaluateConstAppDef uni m = EvaluateConstApp uni m (Value TyName Name (ValueIn uni) ())

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

-- | Evaluate a constant application computation using the given evaluator.
runEvaluateConstApp
    :: Evaluator uni Term m -> EvaluateConstApp uni m a -> m (ConstAppResult (ValueIn uni) a)
runEvaluateConstApp eval = unInnerT . runEvaluateT eval

-- | Lift the result of a constant application to a constant application computation.
liftConstAppResult :: Monad m => ConstAppResult (ValueIn uni) a -> EvaluateConstApp uni m a
-- Could it be @yield . yield@?
liftConstAppResult = EvaluateT . lift . yield

-- | Same as 'makeBuiltin', but returns a 'ConstAppResult'.
makeConstAppResult :: uni `Includes` a => a -> ConstAppResultDef uni
makeConstAppResult = pure . Constant () . ValueIn knownUni

-- | Convert a PLC constant (unwrapped from 'Value') into the corresponding Haskell value.
-- Checks that the constant is of a given built-in type.
extractBuiltin
    :: forall m uni a. (Monad m, GEq uni, uni `Includes` a)
    => Value TyName Name (ValueIn uni) () -> EvaluateConstApp uni m a
extractBuiltin value@(Constant _ (ValueIn uni x)) = case geq uni $ knownUni @uni @a of
    -- TODO: add an 'IllTypedApplication' error or something like that.
    -- TODO: change errors in general.
    Nothing   -> liftConstAppResult $ ConstAppError $ UnreadableBuiltinConstAppError value "blah-blah"
    Just Refl -> pure x
extractBuiltin value                              =
    thoist (InnerT . fmap nat . runReflectT) $ unliftDeepM value where
        nat :: forall b. EvaluationResult (Either Text b) -> ConstAppResult (ValueIn uni) b
        nat EvaluationFailure              = ConstAppFailure
        nat (EvaluationSuccess (Left err)) = ConstAppError $ UnreadableBuiltinConstAppError value err
        nat (EvaluationSuccess (Right x )) = ConstAppSuccess x

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: (Monad m, GEq uni)
    => TypeScheme uni a r -> a -> [Value TyName Name (ValueIn uni) ()] -> EvaluateConstAppDef uni m
applyTypeSchemed = go where
    go
        :: (Monad m, GEq uni)
        => TypeScheme uni a r
        -> a
        -> [Value TyName Name (ValueIn uni) ()]
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
    -> [Value TyName Name (ValueIn uni) ()]
    -> EvaluateConstAppDef uni m
applyTypedBuiltinName (TypedBuiltinName _ schema) = applyTypeSchemed schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyBuiltinName
    :: (Monad m, GEq uni, uni `Includes` Integer, uni `Includes` BSL.ByteString)
    => BuiltinName -> [Value TyName Name (ValueIn uni) ()] -> EvaluateConstAppDef uni m
applyBuiltinName TakeByteString       =
    applyTypedBuiltinName typedTakeByteString       (BSL.take . fromIntegral)
applyBuiltinName _ = undefined
-- applyBuiltinName AddInteger           =
--     applyTypedBuiltinName typedAddInteger           (+)
-- applyBuiltinName SubtractInteger      =
--     applyTypedBuiltinName typedSubtractInteger      (-)
-- applyBuiltinName MultiplyInteger      =
--     applyTypedBuiltinName typedMultiplyInteger      (*)
-- applyBuiltinName DivideInteger        =
--     applyTypedBuiltinName typedDivideInteger        (nonZeroArg div)
-- applyBuiltinName QuotientInteger      =
--     applyTypedBuiltinName typedQuotientInteger      (nonZeroArg quot)
-- applyBuiltinName RemainderInteger     =
--     applyTypedBuiltinName typedRemainderInteger     (nonZeroArg rem)
-- applyBuiltinName ModInteger           =
--     applyTypedBuiltinName typedModInteger           (nonZeroArg mod)
-- applyBuiltinName LessThanInteger      =
--     applyTypedBuiltinName typedLessThanInteger      (<)
-- applyBuiltinName LessThanEqInteger    =
--     applyTypedBuiltinName typedLessThanEqInteger    (<=)
-- applyBuiltinName GreaterThanInteger   =
--     applyTypedBuiltinName typedGreaterThanInteger   (>)
-- applyBuiltinName GreaterThanEqInteger =
--     applyTypedBuiltinName typedGreaterThanEqInteger (>=)
-- applyBuiltinName EqInteger            =
--     applyTypedBuiltinName typedEqInteger            (==)
-- applyBuiltinName Concatenate          =
--     applyTypedBuiltinName typedConcatenate          (<>)
-- applyBuiltinName TakeByteString       =
--     applyTypedBuiltinName typedTakeByteString       (BSL.take . fromIntegral)
-- applyBuiltinName DropByteString       =
--     applyTypedBuiltinName typedDropByteString       (BSL.drop . fromIntegral)
-- applyBuiltinName SHA2                 =
--     applyTypedBuiltinName typedSHA2                 Hash.sha2
-- applyBuiltinName SHA3                 =
--     applyTypedBuiltinName typedSHA3                 Hash.sha3
-- applyBuiltinName VerifySignature      =
--     applyTypedBuiltinName typedVerifySignature      verifySignature
-- applyBuiltinName EqByteString         =
--     applyTypedBuiltinName typedEqByteString         (==)
-- applyBuiltinName LtByteString         =
--     applyTypedBuiltinName typedLtByteString         (<)
-- applyBuiltinName GtByteString         =
--     applyTypedBuiltinName typedGtByteString         (>)

-- | Apply a 'BuiltinName' to a list of 'Value's and evaluate the resulting computation usign the
-- given evaluator.
runApplyBuiltinName
    :: (Monad m, GEq uni, uni `Includes` Integer, uni `Includes` BSL.ByteString)
    => Evaluator uni Term m
    -> BuiltinName
    -> [Value TyName Name (ValueIn uni) ()]
    -> m (ConstAppResultDef uni)
runApplyBuiltinName eval name = runEvaluateConstApp eval . applyBuiltinName name
