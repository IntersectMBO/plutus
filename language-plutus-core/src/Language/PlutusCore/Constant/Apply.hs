{-# LANGUAGE TypeApplications      #-}
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
    , nonZeroArg
    , makeBuiltin
    , applyTypeSchemed
    , applyBuiltinName
    ) where

import           Language.PlutusCore.Constant.DefaultUni
import           Language.PlutusCore.Constant.Name
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type          (BuiltinName (..))
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Crypto
import qualified Data.ByteString.Lazy                    as BSL
import qualified Data.ByteString.Lazy.Hash               as Hash
import           Data.GADT.Compare
import           Data.Text                               (Text)

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

-- | Turn a function into another function that returns 'EvaluationFailure' when its second argument
-- is 0 or calls the original function otherwise and wraps the result in 'EvaluationSuccess'.
-- Useful for correctly handling `div`, `mod`, etc.
nonZeroArg :: (Integer -> Integer -> Integer) -> Integer -> Integer -> EvaluationResult Integer
nonZeroArg _ _ 0 = EvaluationFailure
nonZeroArg f x y = EvaluationSuccess $ f x y

makeBuiltin :: TypeGround uni a -> a -> ConstAppResultDef uni
makeBuiltin (TypeGroundValue  uni) x                     = pure . Constant () $ SomeOf uni x
makeBuiltin (TypeGroundResult _  ) EvaluationFailure     = ConstAppFailure
makeBuiltin (TypeGroundResult uni) (EvaluationSuccess x) = pure . Constant () $ SomeOf uni x
makeBuiltin (TypeGroundTerm inj _) (OpaqueTerm term)     = pure $ substConstantsTerm inj term

unliftConstant
    :: forall uni a. GEq uni => uni a -> Value TyName Name uni () -> ConstAppResult uni a
unliftConstant uni value@(Constant () (SomeOf uni' x)) = case geq uni uni' of
    -- TODO: add an 'IllTypedApplication' error or something like that.
    -- TODO: change errors in general.
    Nothing   -> ConstAppError $ UnreadableBuiltinConstAppError value "blah-blah"
    Just Refl -> pure x
unliftConstant _   _                                   = error "blah-blah"

-- | Convert a PLC constant (unwrapped from 'Value') into the corresponding Haskell value.
-- Checks that the constant is of a given built-in type.
readBuiltin
    :: forall uni a. GEq uni
    => TypeGround uni a -> Value TyName Name uni () -> ConstAppResult uni a
readBuiltin (TypeGroundTerm  _ ej) value   = pure . OpaqueTerm $ substConstantsTerm ej value
readBuiltin (TypeGroundResult _  ) Error{} = pure EvaluationFailure
readBuiltin (TypeGroundResult uni) value   = EvaluationSuccess <$> unliftConstant uni value
readBuiltin (TypeGroundValue  uni) value   = unliftConstant uni value

-- | Apply a function with a known 'TypeScheme' to a list of 'Constant's (unwrapped from 'Value's).
-- Checks that the constants are of expected types.
applyTypeSchemed
    :: GEq uni
    => TypeScheme uni as r -> FoldType as r -> [Value TyName Name uni ()] -> ConstAppResultDef uni
applyTypeSchemed = go where
    go
        :: GEq uni
        => TypeScheme uni as r
        -> FoldType as r
        -> [Value TyName Name uni ()]
        -> ConstAppResultDef uni
    go (TypeSchemeResult gr)       y args =
        case args of
            [] -> makeBuiltin gr y                            -- Computed the result.
            _  -> ConstAppError $ ExcessArgumentsConstAppError args  -- Too many arguments.
    go (TypeSchemeAllType _ schK)  f args =
        go (schK $ TypeGroundTerm id id) f args
    go (TypeSchemeArrow gr schB)   f args = case args of
        []          -> ConstAppStuck                      -- Not enough arguments to compute.
        arg : args' -> do                                 -- Peel off one argument.
            -- Coerce the argument to a Haskell value.
            x <- readBuiltin gr arg
            -- Apply the function to the coerced argument and proceed recursively.
            go schB (f x) args'

-- | Apply a 'TypedBuiltinName' to a list of 'Constant's (unwrapped from 'Value's)
-- Checks that the constants are of expected types.
applyTypedBuiltinName
    :: GEq uni
    => TypedBuiltinName uni as r
    -> FoldType as r
    -> [Value TyName Name uni ()]
    -> ConstAppResultDef uni
applyTypedBuiltinName (TypedBuiltinName _ schema) = applyTypeSchemed schema

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
-- Checks that the values are of expected types.
applyBuiltinName
    :: (GEq uni, HasDefaultUni uni)
    => BuiltinName -> [Value TyName Name uni ()] -> ConstAppResultDef uni
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
