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
    , makeConstAppResult
    , applyTypeSchemed
    , applyBuiltinName
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

import           Control.Monad.Except
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

-- | Same as 'makeBuiltin', but returns a 'ConstAppResult'.
makeConstAppResult :: TypedBuiltinValue a -> ConstAppResultDef
makeConstAppResult = maybe ConstAppFailure ConstAppSuccess . makeBuiltin

-- | Convert a PLC constant into the corresponding Haskell value.
-- Checks that the constant is of a given type.
extractStaticBuiltin
    :: TypedBuiltinStatic a -> Constant () -> ConstAppResult a
extractStaticBuiltin TypedBuiltinStaticInt (BuiltinInt () int) = ConstAppSuccess int
extractStaticBuiltin TypedBuiltinStaticBS  (BuiltinBS  () bs ) = ConstAppSuccess bs
extractStaticBuiltin tbs                  constant            = ConstAppError $ IllTypedConstAppError (eraseTypedBuiltinStatic tbs) constant

-- | Convert a PLC constant (unwrapped from 'Value') into the corresponding Haskell value.
-- Checks that the constant is of a given built-in type.
extractBuiltin
    :: Monad m
    => TypedBuiltin a
    -> Value TyName Name ()
    -> Evaluate m (ConstAppResult a)
extractBuiltin (TypedBuiltinStatic tbs) value =
    return $ case value of
        Constant () constant -> extractStaticBuiltin tbs constant
        _                    -> ConstAppError $ NonConstantConstAppError value
extractBuiltin TypedBuiltinDyn                   value =
    readDynamicBuiltinM value <&> \conv -> case runExceptT conv of
        EvaluationFailure            -> ConstAppFailure
        EvaluationSuccess (Left err) -> ConstAppError $ UnreadableBuiltinConstAppError value err
        EvaluationSuccess (Right x ) -> ConstAppSuccess x

-- | Convert a PLC constant (unwrapped from 'Value') into the corresponding Haskell value.
-- Checks that the constant is of a given type.
extractSchemed
    :: Monad m
    => TypeScheme a r
    -> Value TyName Name ()
    -> Evaluate m (ConstAppResult a)
extractSchemed (TypeSchemeBuiltin a)   value = extractBuiltin a value
extractSchemed (TypeSchemeArrow _ _)   _     = error "Not implemented."
extractSchemed (TypeSchemeAllType _ _) _     = error "Not implemented."

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: Monad m
    => TypeScheme a r -> a -> [Value TyName Name ()] -> Evaluate m ConstAppResultDef
applyTypeSchemed = go where
    go
        :: Monad m
        => TypeScheme a r
        -> a
        -> [Value TyName Name ()]
        -> Evaluate m ConstAppResultDef
    go (TypeSchemeBuiltin tb)      y args = case args of  -- Computed the result.
        [] -> return . makeConstAppResult $ TypedBuiltinValue tb y
        _  -> return . ConstAppError $ ExcessArgumentsConstAppError args     -- Too many arguments.
    go (TypeSchemeAllType _ schK)  f args =
        go (schK TypedBuiltinDyn) f args
    go (TypeSchemeArrow schA schB) f args = case args of
        []          -> return ConstAppStuck             -- Not enough arguments to compute.
        arg : args' -> do                               -- Peel off one argument.
            -- Coerce the argument to a Haskell value.
            res <- extractSchemed schA arg
            forBind res $ \x ->
                -- Apply the function to the coerced argument and proceed recursively.
                go schB (f x) args'

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyTypedBuiltinName
    :: Monad m
    => TypedBuiltinName a r -> a -> [Value TyName Name ()] -> Evaluate m ConstAppResultDef
applyTypedBuiltinName (TypedBuiltinName _ schema) = applyTypeSchemed schema

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyBuiltinName
    :: Monad m
    => BuiltinName -> [Value TyName Name ()] -> Evaluate m ConstAppResultDef
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
