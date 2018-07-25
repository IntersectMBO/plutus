{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}
module Language.PlutusCore.Constant.Apply
    ( ConstAppError(..)
    , ConstAppResult(..)
    , applyBuiltinName
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Constant.Prelude
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed

import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

-- | The type of constant applications errors.
data ConstAppError
    = SizeMismatchConstAppError Size (Constant ())
    | forall a. IllTypedConstAppError (TypedBuiltinSized a) (Constant ())
    | ExcessArgumentsConstAppErr [Constant ()]

data ConstAppResult
    = ConstAppSuccess (Term TyName Name ())
    | ConstAppFailure
    | ConstAppStuck
    | ConstAppError ConstAppError

newtype SizeValues = SizeValues (IntMap Size)

checkBuiltinSize :: Maybe Size -> Size -> Constant () -> b -> Either ConstAppError (b, Size)
checkBuiltinSize (Just size) size' constant _ | size /= size' =
    Left $ SizeMismatchConstAppError size constant
checkBuiltinSize  _          size' _        y = Right (y, size')

applyToSizedBuiltin
    :: TypedBuiltinSized a -> Maybe Size -> (a -> b) -> Constant () -> Either ConstAppError (b, Size)
applyToSizedBuiltin TypedBuiltinInt  maySize f constant@(BuiltinInt  () size' int) =
    checkBuiltinSize maySize size' constant (f int)
applyToSizedBuiltin TypedBuiltinBS   maySize f constant@(BuiltinBS   () size' bs ) =
    checkBuiltinSize maySize size' constant (f bs)
applyToSizedBuiltin TypedBuiltinSize maySize f constant@(BuiltinSize () size'    ) =
    checkBuiltinSize maySize size' constant (f size')
applyToSizedBuiltin typedBuiltin     _       _ constant                            =
    Left $ IllTypedConstAppError typedBuiltin constant

applyToBuiltin
    :: TypedBuiltin a -> SizeValues -> (a -> b) -> Constant () -> Either ConstAppError (b, SizeValues)
applyToBuiltin (TypedBuiltinSized (SizeVar sizeIndex) typedBuiltin) (SizeValues sizes) f constant =
    unPairT . fmap SizeValues $ IntMap.alterF upd sizeIndex sizes where
        upd maySize = fmap Just . PairT $ applyToSizedBuiltin typedBuiltin maySize f constant
applyToBuiltin TypedBuiltinBool _ f constant = undefined

applySchemed
    :: TypeSchema a -> SizeValues -> (a -> b) -> Constant () -> Either ConstAppError (b, SizeValues)
applySchemed (TypeSchemaBuiltin a) sizeValues = applyToBuiltin a sizeValues
applySchemed (TypeSchemaArrow a b) sizeValues = undefined
applySchemed (TypeSchemaForall  k) sizeValues = undefined

wrapSizedConstant
    :: TypedBuiltinSized a -> Size -> a -> Maybe (Term TyName Name ())
wrapSizedConstant TypedBuiltinInt  size int   = makeBuiltinInt  size int
wrapSizedConstant TypedBuiltinBS   size bs    = makeBuiltinBS   size bs
wrapSizedConstant TypedBuiltinSize size size' = makeBuiltinSize size size'

wrapConstant
    :: TypedBuiltin a -> SizeValues -> a -> Maybe (Term TyName Name ())
wrapConstant (TypedBuiltinSized (SizeVar sizeIndex) typedSizedBuiltin) (SizeValues sizes) =
    wrapSizedConstant typedSizedBuiltin $ sizes IntMap.! sizeIndex
wrapConstant TypedBuiltinBool                                           _                 =
    makeBuiltinBool

applyTypedBuiltinName
    :: TypedBuiltinName a -> a -> [Constant ()] -> ConstAppResult
applyTypedBuiltinName (TypedBuiltinName _ schema) = go schema (SizeVar 0) (SizeValues mempty) where
    go :: TypeSchema a -> SizeVar -> SizeValues -> a -> [Constant ()] -> ConstAppResult
    go (TypeSchemaBuiltin builtin)       _       sizeValues y args = case args of
       [] -> case wrapConstant builtin sizeValues y of
           Just wc -> ConstAppSuccess wc
           Nothing -> ConstAppFailure
       _  -> ConstAppError $ ExcessArgumentsConstAppErr args
    go (TypeSchemaArrow schemaA schemaB) sizeVar sizeValues f args = case args of
        []        -> ConstAppStuck
        x : args' -> case applySchemed schemaA sizeValues f x of
            Left err               -> ConstAppError err
            Right (y, sizeValues') -> go schemaB sizeVar sizeValues' y args'
    go (TypeSchemaForall k)              sizeVar sizeValues f args =
        go (k sizeVar) (succ sizeVar) sizeValues f args

-- | Apply a `BuiltinName` to a list of arguments.
-- If the `BuiltinName` is saturated, return `Just` applied to the result of the computation.
-- Otherwise return `Nothing`.
-- Throw a `ConstAppException` if something goes wrong.
applyBuiltinName :: BuiltinName -> [Constant ()] -> ConstAppResult
applyBuiltinName AddInteger           = applyTypedBuiltinName typedAddInteger       (+)
applyBuiltinName SubtractInteger      = applyTypedBuiltinName typedSubtractInteger  (-)
applyBuiltinName MultiplyInteger      = applyTypedBuiltinName typedMultiplyInteger  (*)
applyBuiltinName DivideInteger        = applyTypedBuiltinName typedDivideInteger    div
applyBuiltinName RemainderInteger     = applyTypedBuiltinName typedRemainderInteger mod
applyBuiltinName LessThanInteger      = applyTypedBuiltinName typedLessThanInteger      (<)
applyBuiltinName LessThanEqInteger    = applyTypedBuiltinName typedLessThanEqInteger    (<=)
applyBuiltinName GreaterThanInteger   = applyTypedBuiltinName typedGreaterThanInteger   (>)
applyBuiltinName GreaterThanEqInteger = applyTypedBuiltinName typedGreaterThanEqInteger (>=)
applyBuiltinName EqInteger            = applyTypedBuiltinName typedEqInteger            (==)
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
