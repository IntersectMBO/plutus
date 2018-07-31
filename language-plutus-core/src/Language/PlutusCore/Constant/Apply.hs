{-# LANGUAGE StandaloneDeriving #-}
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
    | IllTypedConstAppError BuiltinSized (Constant ())
      -- ^ A mismatch between the type of an argument function expects and its actual type.
    | ExcessArgumentsConstAppError [Value TyName Name ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments
    | SizedValueConstAppError (Value TyName Name ())
    | NotImplementedConstAppError
    deriving (Show, Eq)

-- | The type of constant applications results.
data ConstAppResult
    = ConstAppSuccess (Value TyName Name ())
      -- ^ Successfully computed a value.
    | ConstAppFailure
      -- ^ Not enough fuel.
    | ConstAppStuck
      -- ^ Not enough arguments.
    | ConstAppError ConstAppError
      -- ^ An internal error occurred during evaluation.
    deriving (Show, Eq)

-- | An 'IntMap' from size variables to sizes.
newtype SizeValues = SizeValues (IntMap Size)

-- instance Eq ConstAppError where

dechurchBool :: ((() -> Bool) -> (() -> Bool) -> Bool) -> Bool
dechurchBool if' = if' (const True) (const False)

checkBuiltinSize :: Maybe Size -> Size -> Constant () -> b -> Either ConstAppError (b, Size)
checkBuiltinSize (Just size) size' constant _ | size /= size' =
    Left $ SizeMismatchConstAppError size constant
checkBuiltinSize  _          size' _        y = Right (y, size')

extractSizedBuiltin
    :: TypedBuiltinSized a -> Maybe Size -> Constant () -> Either ConstAppError (a, Size)
extractSizedBuiltin TypedBuiltinSizedInt  maySize constant@(BuiltinInt  () size' int) =
    checkBuiltinSize maySize size' constant int
extractSizedBuiltin TypedBuiltinSizedBS   maySize constant@(BuiltinBS   () size' bs ) =
    checkBuiltinSize maySize size' constant bs
extractSizedBuiltin TypedBuiltinSizedSize maySize constant@(BuiltinSize () size'    ) =
    checkBuiltinSize maySize size' constant size'
extractSizedBuiltin typedBuiltinSized     _       constant                            =
    Left $ IllTypedConstAppError (eraseTypedBuiltinSized typedBuiltinSized) constant

extractBuiltin
    :: TypedBuiltin a -> SizeValues -> Value TyName Name () -> Either ConstAppError (a, SizeValues)
extractBuiltin (TypedBuiltinSized (SizeVar sizeIndex) typedBuiltinSized) (SizeValues sizes) value =
    case value of
        Constant () constant -> unPairT . fmap SizeValues $ IntMap.alterF upd sizeIndex sizes where
            upd maySize = fmap Just . PairT $ extractSizedBuiltin typedBuiltinSized maySize constant
        _                    -> Left $ SizedValueConstAppError value
extractBuiltin TypedBuiltinBool                                     _                  _     =
    -- Plan: evaluate the 'value' to a dynamically typed Church-encoded 'Bool'
    -- specialized to 'Bool' and coerce it to an actual 'Bool'.
    Left NotImplementedConstAppError

-- | Coerce a PLC value to a Haskell value.
extractSchemed
    :: TypeScheme a -> SizeValues -> Value TyName Name () -> Either ConstAppError (a, SizeValues)
extractSchemed (TypeSchemeBuiltin a) sizeValues value = extractBuiltin a sizeValues value
extractSchemed (TypeSchemeArrow _ _) _          _     = Left NotImplementedConstAppError
extractSchemed (TypeSchemeForall  _) _          _     = Left NotImplementedConstAppError

-- | Apply a Haskell function to a PLC value.
applySchemed
    :: TypeScheme a
    -> SizeValues
    -> (a -> b)
    -> Value TyName Name ()
    -> Either ConstAppError (b, SizeValues)
applySchemed schema sizeValues f value =
    first f <$> extractSchemed schema sizeValues value

-- | Coerce a Haskell value to a PLC constant indexed by size checking all constraints
-- (e.g. an `Integer` is in appropriate bounds) along the way.
wrapSizedConstant
    :: TypedBuiltinSized a -> Size -> a -> Maybe (Constant ())
wrapSizedConstant TypedBuiltinSizedInt  size int   = makeBuiltinInt  size int
wrapSizedConstant TypedBuiltinSizedBS   size bs    = makeBuiltinBS   size bs
wrapSizedConstant TypedBuiltinSizedSize size size' = makeBuiltinSize size size'

-- | Coerce a Haskell value to a PLC term checking all constraints
-- (e.g. an `Integer` is in appropriate bounds) along the way.
wrapConstant
    :: TypedBuiltin a -> SizeValues -> a -> Maybe (Value TyName Name ())
wrapConstant (TypedBuiltinSized (SizeVar sizeIndex) typedSizedBuiltin) (SizeValues sizes) x =
    Constant () <$> wrapSizedConstant typedSizedBuiltin (sizes IntMap.! sizeIndex) x
wrapConstant TypedBuiltinBool                                           _                 b =
    Just $ makeDupBuiltinBool b

-- | Apply a 'TypedBuiltinName' to a list of constant arguments.
applyTypedBuiltinName :: TypedBuiltinName a -> a -> [Value TyName Name ()] -> ConstAppResult
applyTypedBuiltinName (TypedBuiltinName _ schema) = go schema (SizeVar 0) (SizeValues mempty) where
    go :: TypeScheme a -> SizeVar -> SizeValues -> a -> [Value TyName Name ()] -> ConstAppResult
    go (TypeSchemeBuiltin builtin)       _       sizeValues y args = case args of  -- Computed the result.
       [] -> case wrapConstant builtin sizeValues y of                             -- Coerce the result to a PLC term.
           Just wc -> ConstAppSuccess wc                                           -- Return the coerced result.
           Nothing -> ConstAppFailure                                              -- Report a failure.
       _  -> ConstAppError $ ExcessArgumentsConstAppError args
    go (TypeSchemeArrow schemaA schemaB) sizeVar sizeValues f args = case args of
        []        -> ConstAppStuck                                            -- Not enough arguments to compute.
        x : args' -> case applySchemed schemaA sizeValues f x of              -- Apply the function to an argument.
            Left err               -> ConstAppError err                       -- The application resulted in an error.
            Right (y, sizeValues') -> go schemaB sizeVar sizeValues' y args'  -- The application is fine, proceed recursively.
    go (TypeSchemeForall k)              sizeVar sizeValues f args =
        go (k sizeVar) (succ sizeVar) sizeValues f args  -- Instantiate the `forall` with a fresh var and proceed recursively.

-- | Apply a 'BuiltinName' to a list of arguments.
applyBuiltinName :: BuiltinName -> [Value TyName Name ()] -> ConstAppResult
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
applyBuiltinName ResizeInteger        = applyTypedBuiltinName typedResizeInteger        (const id)
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
