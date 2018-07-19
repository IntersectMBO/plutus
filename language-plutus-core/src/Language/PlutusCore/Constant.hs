{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Constant ( ConstantApplicationException(..)
                                    , reduceConstantApplication
                                    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Type
import           Data.Text (Text)
import qualified Data.Text as Text

-- | An attempt to apply a constant to inapproriate arguments results in this exception.
data ConstantApplicationException = ConstantApplicationException Text

instance Show ConstantApplicationException where
    show (ConstantApplicationException err) = Text.unpack err

instance Exception ConstantApplicationException

-- | A term (called "head") applied to a list of arguments (called "spine").
data IteratedApplication tyname name a = IteratedApplication
    { _iteratedApplicationHead  :: Term tyname name a
    , _iteratedApplicationSpine :: [Term tyname name a]
    }

-- | View a `Term` as an `IteratedApplication`.
viewIteratedApplication :: Term tyname name a -> Maybe (IteratedApplication tyname name a)
viewIteratedApplication term@Apply{} = Just $ go [] term where
    go args (Apply _ fun arg) = go (undefined arg : args) fun
    go args  fun              = IteratedApplication fun args
viewIteratedApplication _            = Nothing

-- | View a `Term` as a `Constant`.
viewConstant :: Term tyname name a -> Maybe (Constant a)
viewConstant (Constant _ constant) = Just constant
viewConstant _                     = Nothing

-- | View a `Constant` as a `BuiltinName`.
viewBuiltinName :: Constant a -> Maybe BuiltinName
viewBuiltinName (BuiltinName _ name) = Just name
viewBuiltinName _                    = Nothing

-- TODO: this is a stub.
applyBuiltinSizeIntInt
    :: (Integer -> Integer -> Integer) -> [Constant ()] -> Maybe (Constant ())
applyBuiltinSizeIntInt op [BuiltinSize _ s, BuiltinInt _ n i, BuiltinInt _ m j] =
    Just . BuiltinInt () m $ op i j

-- | Apply a `BuiltinName` to a list of arguments.
-- If the `BuiltinName` is saturated, return `Just` applied to the result of the computation.
-- Otherwise return `Nothing`.
-- Throw the `ConstantApplicationException` exception if there is any type mismatch
-- between the `BuiltinName` and the arguments.
applyBuiltinName :: BuiltinName -> [Constant ()] -> Maybe (Constant ())
applyBuiltinName AddInteger           = applyBuiltinSizeIntInt (+)
applyBuiltinName SubtractInteger      = undefined
applyBuiltinName MultiplyInteger      = undefined
applyBuiltinName DivideInteger        = undefined
applyBuiltinName RemainderInteger     = undefined
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

-- | View a `Term` as an iterated application of a `BuiltinName` to a list of `Constants`.
-- If succesful, return `Just` applied to either this same term or
-- the result of the computation depending on whether `BuiltinName` is saturated or not.
reduceConstantApplication :: Term tyname name () -> Maybe (Term tyname name ())
reduceConstantApplication term = do
    IteratedApplication termHead termSpine <- viewIteratedApplication term
    headName <- viewConstant termHead >>= viewBuiltinName
    spine <- traverse viewConstant termSpine
    Just . maybe term (Constant ()) $ applyBuiltinName headName spine
