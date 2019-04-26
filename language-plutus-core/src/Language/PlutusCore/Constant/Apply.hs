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
    , ConstAppResult (..)
    , ConstAppResultDef
    , EvaluateConstApp
    , EvaluateConstAppDef
    , makeConstAppResult
    , runEvaluateConstApp
    , applyTypeSchemed
    , applyBuiltinName
    , runApplyBuiltinName
    ) where

import           Language.PlutusCore.Constant.Dynamic.Instances ()
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type                 (BuiltinName (..))
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Inner
import           Crypto
import qualified Data.ByteString.Lazy                           as BSL
import qualified Data.ByteString.Lazy.Hash                      as Hash
import           Data.Text                                      (Text)

-- | The type of constant applications errors.
data ConstAppError
    = IllTypedConstAppError BuiltinStatic (Constant ())
      -- ^ A mismatch between the type of an argument function expects and its actual type.
    | ExcessArgumentsConstAppError [Value TyName Name ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | NonConstantConstAppError (Value TyName Name ())
    | UnreadableBuiltinConstAppError (Value TyName Name ()) Text
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

type ConstAppResultDef = ConstAppResult (Value TyName Name ())

instance ( PrettyBy config (Constant ())
         , PrettyBy config (Value TyName Name ())
         ) => PrettyBy config ConstAppError where
    prettyBy config (IllTypedConstAppError expType con)      = fold
        [ "Ill-typed constant application:", "\n"
        , "expected type: ", pretty expType, "\n"
        , "actual constant: ", prettyBy config con
        ]
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

instance ( PrettyBy config (Constant ())
         , PrettyBy config (Value TyName Name ())
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
type EvaluateConstAppDef m = EvaluateConstApp m (Value TyName Name ())

-- | Evaluate a constant application computation using the given evaluator.
runEvaluateConstApp :: Evaluator Term m -> EvaluateConstApp m a -> m (ConstAppResult a)
runEvaluateConstApp eval = unInnerT . runEvaluateT eval

-- | Lift the result of a constant application to a constant application computation.
liftConstAppResult :: Monad m => ConstAppResult a -> EvaluateConstApp m a
-- Could it be @yield . yield@?
liftConstAppResult = EvaluateT . lift . yield

-- | Same as 'makeBuiltin', but returns a 'ConstAppResult'.
makeConstAppResult :: TypedBuiltinValue a -> ConstAppResultDef
makeConstAppResult = maybe ConstAppFailure ConstAppSuccess . makeBuiltin

-- | Convert a PLC constant into the corresponding Haskell value.
-- Checks that the constant is of a given type.
extractStaticBuiltin
    :: TypedBuiltinStatic a -> Constant () -> ConstAppResult a
extractStaticBuiltin TypedBuiltinStaticInt (BuiltinInt () int) = ConstAppSuccess int
extractStaticBuiltin TypedBuiltinStaticBS  (BuiltinBS  () bs ) = ConstAppSuccess bs
extractStaticBuiltin tbs                   constant            =
    ConstAppError $ IllTypedConstAppError (eraseTypedBuiltinStatic tbs) constant

-- | Convert a PLC constant (unwrapped from 'Value') into the corresponding Haskell value.
-- Checks that the constant is of a given built-in type.
extractBuiltin
    :: Monad m
    => TypedBuiltin a
    -> Value TyName Name ()
    -> EvaluateConstApp m a
extractBuiltin (TypedBuiltinStatic tbs) value =
    liftConstAppResult $ case value of
        Constant () constant -> extractStaticBuiltin tbs constant
        _                    -> ConstAppError $ NonConstantConstAppError value
extractBuiltin TypedBuiltinDyn                   value =
    thoist (InnerT . fmap nat . runReflectT) $ readDynamicBuiltinM value where
        nat :: EvaluationResult (Either Text a) -> ConstAppResult a
        nat EvaluationFailure              = ConstAppFailure
        nat (EvaluationSuccess (Left err)) = ConstAppError $ UnreadableBuiltinConstAppError value err
        nat (EvaluationSuccess (Right x )) = ConstAppSuccess x

-- | Convert a PLC constant (unwrapped from 'Value') into the corresponding Haskell value.
-- Checks that the constant is of a given type.
extractSchemed
    :: Monad m
    => TypeScheme a r
    -> Value TyName Name ()
    -> EvaluateConstApp m a
extractSchemed (TypeSchemeBuiltin a)   value = extractBuiltin a value
extractSchemed (TypeSchemeArrow _ _)   _     = error "Not implemented."
extractSchemed (TypeSchemeAllType _ _) _     = error "Not implemented."

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: Monad m => TypeScheme a r -> a -> [Value TyName Name ()] -> EvaluateConstAppDef m
applyTypeSchemed = go where
    go
        :: Monad m
        => TypeScheme a r
        -> a
        -> [Value TyName Name ()]
        -> EvaluateConstAppDef m
    go (TypeSchemeBuiltin tb)      y args =  -- Computed the result.
        liftConstAppResult $ case args of
            -- This is where all the size checks prescribed by the specification happen.
            -- We instantiate the size variable of a final 'TypedBuiltin' to its value and call
            -- 'makeConstAppResult' which performs the final size check before converting
            -- a Haskell value to the corresponding PLC one.
            [] -> makeConstAppResult $ TypedBuiltinValue tb y
            _  -> ConstAppError $ ExcessArgumentsConstAppError args  -- Too many arguments.
    go (TypeSchemeAllType _ schK)  f args =
        go (schK TypedBuiltinDyn) f args
    go (TypeSchemeArrow schA schB) f args = case args of
        []          -> liftConstAppResult ConstAppStuck  -- Not enough arguments to compute.
        arg : args' -> do                                -- Peel off one argument.
            -- Coerce the argument to a Haskell value.
            x <- extractSchemed schA arg
            -- Apply the function to the coerced argument and proceed recursively.
            go schB (f x) args'

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyTypedBuiltinName
    :: Monad m => TypedBuiltinName a r -> a -> [Value TyName Name ()] -> EvaluateConstAppDef m
applyTypedBuiltinName (TypedBuiltinName _ schema) = applyTypeSchemed schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyBuiltinName
    :: Monad m => BuiltinName -> [Value TyName Name ()] -> EvaluateConstAppDef m
applyBuiltinName AddInteger           = applyTypedBuiltinName typedAddInteger           (+)
applyBuiltinName SubtractInteger      = applyTypedBuiltinName typedSubtractInteger      (-)
applyBuiltinName MultiplyInteger      = applyTypedBuiltinName typedMultiplyInteger      (*)
applyBuiltinName DivideInteger        = applyTypedBuiltinName typedDivideInteger        div
applyBuiltinName QuotientInteger      = applyTypedBuiltinName typedQuotientInteger      quot
applyBuiltinName RemainderInteger     = applyTypedBuiltinName typedRemainderInteger     rem
applyBuiltinName ModInteger           = applyTypedBuiltinName typedModInteger           mod
applyBuiltinName LessThanInteger      = applyTypedBuiltinName typedLessThanInteger      (<)
applyBuiltinName LessThanEqInteger    = applyTypedBuiltinName typedLessThanEqInteger    (<=)
applyBuiltinName GreaterThanInteger   = applyTypedBuiltinName typedGreaterThanInteger   (>)
applyBuiltinName GreaterThanEqInteger = applyTypedBuiltinName typedGreaterThanEqInteger (>=)
applyBuiltinName EqInteger            = applyTypedBuiltinName typedEqInteger            (==)
applyBuiltinName IntToByteString      = applyTypedBuiltinName typedIntToByteString      undefined
applyBuiltinName Concatenate          = applyTypedBuiltinName typedConcatenate          (<>)
applyBuiltinName TakeByteString       = applyTypedBuiltinName typedTakeByteString
                                                                  (BSL.take . fromIntegral)
applyBuiltinName DropByteString       = applyTypedBuiltinName typedDropByteString
                                                                  (BSL.drop . fromIntegral)
applyBuiltinName SHA2                 = applyTypedBuiltinName typedSHA2                 Hash.sha2
applyBuiltinName SHA3                 = applyTypedBuiltinName typedSHA3                 Hash.sha3
applyBuiltinName VerifySignature      = applyTypedBuiltinName typedVerifySignature      verifySignature
applyBuiltinName EqByteString         = applyTypedBuiltinName typedEqByteString         (==)

-- | Apply a 'BuiltinName' to a list of 'Value's and evaluate the resulting computation usign the
-- given evaluator.
runApplyBuiltinName
    :: Monad m => Evaluator Term m -> BuiltinName -> [Value TyName Name ()] -> m ConstAppResultDef
runApplyBuiltinName eval name = runEvaluateConstApp eval . applyBuiltinName name
