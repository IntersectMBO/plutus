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
      -- ^ A mismatch between the type of an argument function expects and its actual type.
    | ExcessArgumentsConstAppErr [Constant ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments

-- | The type of constant applications results.
data ConstAppResult
    = ConstAppSuccess (Term TyName Name ())
      -- ^ Successfully computed a value.
    | ConstAppFailure
      -- ^ Not enough fuel.
    | ConstAppStuck
      -- ^ Not enough arguments.
    | ConstAppError ConstAppError
      -- ^ An internal error occurred during evaluation.

-- | An 'IntMap' from size variables to sizes.
newtype SizeValues = SizeValues (IntMap Size)

checkBuiltinSize :: Maybe Size -> Size -> Constant () -> b -> Either ConstAppError (b, Size)
checkBuiltinSize (Just size) size' constant _ | size /= size' =
    Left $ SizeMismatchConstAppError size constant
checkBuiltinSize  _          size' _        y = Right (y, size')

-- | Apply a Haskell function to a PLC built-in indexed by size.
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

-- | Apply a Haskell function to a PLC built-in.
applyToBuiltin
    :: TypedBuiltin a -> SizeValues -> (a -> b) -> Constant () -> Either ConstAppError (b, SizeValues)
applyToBuiltin (TypedBuiltinSized (SizeVar sizeIndex) typedBuiltin) (SizeValues sizes) f constant =
    unPairT . fmap SizeValues $ IntMap.alterF upd sizeIndex sizes where
        upd maySize = fmap Just . PairT $ applyToSizedBuiltin typedBuiltin maySize f constant
applyToBuiltin TypedBuiltinBool _ f constant = undefined

-- | Apply a Haskell function to a PLC constant.
applySchemed
    :: TypeScheme a -> SizeValues -> (a -> b) -> Constant () -> Either ConstAppError (b, SizeValues)
applySchemed (TypeSchemeBuiltin a) sizeValues = applyToBuiltin a sizeValues
applySchemed (TypeSchemeArrow a b) sizeValues = undefined
applySchemed (TypeSchemeForall  k) sizeValues = undefined

-- | Coerce a Haskell value to a PLC constant indexed by size checking all constraints
-- (e.g. an `Integer` is in appropriate bounds) along the way.
wrapSizedConstant
    :: TypedBuiltinSized a -> Size -> a -> Maybe (Term TyName Name ())
wrapSizedConstant TypedBuiltinInt  size int   = makeBuiltinInt  size int
wrapSizedConstant TypedBuiltinBS   size bs    = makeBuiltinBS   size bs
wrapSizedConstant TypedBuiltinSize size size' = makeBuiltinSize size size'

-- | Coerce a Haskell value to a PLC term checking all constraints
-- (e.g. an `Integer` is in appropriate bounds) along the way.
wrapConstant
    :: TypedBuiltin a -> SizeValues -> a -> Maybe (Term TyName Name ())
wrapConstant (TypedBuiltinSized (SizeVar sizeIndex) typedSizedBuiltin) (SizeValues sizes) =
    wrapSizedConstant typedSizedBuiltin $ sizes IntMap.! sizeIndex
wrapConstant TypedBuiltinBool                                           _                 =
    Just . makeBuiltinBool

-- | Apply a 'TypedBuiltinName' to a list of constant arguments.
applyTypedBuiltinName
    :: TypedBuiltinName a -> a -> [Constant ()] -> ConstAppResult
applyTypedBuiltinName (TypedBuiltinName _ schema) = go schema (SizeVar 0) (SizeValues mempty) where
    go :: TypeScheme a -> SizeVar -> SizeValues -> a -> [Constant ()] -> ConstAppResult
    go (TypeSchemeBuiltin builtin)       _       sizeValues y args = case args of  -- Computed the result.
       [] -> case wrapConstant builtin sizeValues y of                             -- Coerce the result to a PLC term.
           Just wc -> ConstAppSuccess wc                                           -- Return the coerced result.
           Nothing -> ConstAppFailure                                              -- Report a failure.
       _  -> ConstAppError $ ExcessArgumentsConstAppErr args
    go (TypeSchemeArrow schemaA schemaB) sizeVar sizeValues f args = case args of
        []        -> ConstAppStuck                                            -- Not enough arguments to compute.
        x : args' -> case applySchemed schemaA sizeValues f x of              -- Apply the function to an argument.
            Left err               -> ConstAppError err                       -- The application resulted in an error.
            Right (y, sizeValues') -> go schemaB sizeVar sizeValues' y args'  -- The application is fine, proceed recursively.
    go (TypeSchemeForall k)              sizeVar sizeValues f args =
        go (k sizeVar) (succ sizeVar) sizeValues f args  -- Instantiate the `forall` with a fresh var and proceed recursively.

-- | Apply a 'BuiltinName' to a list of arguments.
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
