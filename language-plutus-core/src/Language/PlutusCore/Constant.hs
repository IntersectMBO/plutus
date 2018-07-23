{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Constant ( ConstantApplicationResult(..)
                                    , ConstantApplicationError(..)
                                    , ConstantApplicationException(..)
                                    , IteratedApplication(..)
                                    , viewPrimIteratedApplication
                                    , applyBuiltinName
                                    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Type

import           Data.List
import           Control.Monad

data ConstantApplicationResult = ConstantApplicationSuccess (Constant ())
                               | ConstantApplicationFailure

data ConstantApplicationError = SizeMismatchApplicationError (Constant ()) (Constant ())
                              | IllTypedApplicationError (Constant ())
                              | ExcessArgumentsApplicationError [Constant ()]

-- | An attempt to apply a constant to inapproriate arguments results in this exception.
data ConstantApplicationException = ConstantApplicationException
    { _constantApplicationExceptionError :: ConstantApplicationError
    , _constantApplicationExceptionHead  :: BuiltinName
    , _constantApplicationExceptionSpine :: [Constant ()]
    }

instance Show ConstantApplicationException where
    show = undefined
    -- show (ConstantApplicationException err) = Text.unpack err

instance Exception ConstantApplicationException

-- | A term (called "head") applied to a list of arguments (called "spine").
data IteratedApplication head arg = IteratedApplication
    { _iteratedApplicationHead  :: head
    , _iteratedApplicationSpine :: [arg]
    }

type TermIteratedApplication tyname name a =
    IteratedApplication (Term tyname name a) (Term tyname name a)

type PrimIteratedApplication =
    IteratedApplication BuiltinName (Constant ())

-- | View a `Constant` as a `BuiltinName`.
viewBuiltinName :: Constant a -> Maybe BuiltinName
viewBuiltinName (BuiltinName _ name) = Just name
viewBuiltinName _                    = Nothing

-- | View a `Term` as a `Constant`.
viewConstant :: Term tyname name a -> Maybe (Constant a)
viewConstant (Constant _ constant) = Just constant
viewConstant _                     = Nothing

-- | View a `Term` as an `IteratedApplication`.
viewTermIteratedApplication :: Term tyname name a -> Maybe (TermIteratedApplication tyname name a)
viewTermIteratedApplication term@Apply{} = Just $ go [] term where
    go args (Apply _ fun arg) = go (undefined arg : args) fun
    go args  fun              = IteratedApplication fun args
viewTermIteratedApplication _            = Nothing

-- | View a `Term` as an iterated application of a `BuiltinName` to a list of `Constants`.
viewPrimIteratedApplication :: Term tyname name () -> Maybe PrimIteratedApplication
viewPrimIteratedApplication term = do
    IteratedApplication termHead termSpine <- viewTermIteratedApplication term
    headName <- viewConstant termHead >>= viewBuiltinName
    spine <- traverse viewConstant termSpine
    Just $ IteratedApplication headName spine

type Size = Natural

checkBoundsInt :: Size -> Integer -> Bool
checkBoundsInt s i = -2 ^ p <= i && i < 2 ^ p where
  p = 8 * fromIntegral s - 1 :: Int

-- TODO: this begs to be more general and type-safe.
applyBuiltinSizeIntInt
    :: BuiltinName -> (Integer -> Integer -> Integer) -> [Constant ()] -> Maybe ConstantApplicationResult
applyBuiltinSizeIntInt name op args = do
    let throwAppExc err = throw $ ConstantApplicationException err name args
    (a1, args') <- uncons args
    case a1 of
        BuiltinInt _ n i -> do
            (a2, args'') <- uncons args'
            case a2 of
                BuiltinInt _ m j -> do
                    when (n /= m) . throwAppExc $ SizeMismatchApplicationError a1 a2
                    when (not $ null args'') . throwAppExc $ ExcessArgumentsApplicationError args''
                    let k = i `op` j
                    Just $ if checkBoundsInt n k
                        then ConstantApplicationSuccess $ BuiltinInt () n k
                        else ConstantApplicationFailure
                _                -> throwAppExc $ IllTypedApplicationError a2
        _                -> throwAppExc $ IllTypedApplicationError a1

-- | Apply a `BuiltinName` to a list of arguments.
-- If the `BuiltinName` is saturated, return `Just` applied to the result of the computation.
-- Otherwise return `Nothing`.
-- Throw the `ConstantApplicationException` exception when something goes wrong.
applyBuiltinName :: BuiltinName -> [Constant ()] -> Maybe ConstantApplicationResult
applyBuiltinName AddInteger           = applyBuiltinSizeIntInt AddInteger       (+)
applyBuiltinName SubtractInteger      = applyBuiltinSizeIntInt SubtractInteger  (-)
applyBuiltinName MultiplyInteger      = applyBuiltinSizeIntInt MultiplyInteger  (*)
applyBuiltinName DivideInteger        = applyBuiltinSizeIntInt DivideInteger    (div)
applyBuiltinName RemainderInteger     = applyBuiltinSizeIntInt RemainderInteger (mod)
applyBuiltinName LessThanInteger      = undefined
applyBuiltinName LessThanEqInteger    = undefined
applyBuiltinName GreaterThanInteger   = undefined
applyBuiltinName GreaterThanEqInteger = undefined
applyBuiltinName EqInteger            = undefined
applyBuiltinName IntToByteString      = undefined
applyBuiltinName Concatenate          = undefined
applyBuiltinName TakeByteString       = undefined
applyBuiltinName DropByteString       = undefined
applyBuiltinName ResizeByteString     = undefined
applyBuiltinName SHA2                 = undefined
applyBuiltinName SHA3                 = undefined
applyBuiltinName VerifySignature      = undefined
applyBuiltinName EqByteString         = undefined
applyBuiltinName TxHash               = undefined
applyBuiltinName BlockNum             = undefined
applyBuiltinName BlockTime            = undefined
