{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}
module Language.PlutusCore.Constant.Apply
    ( ConstAppError(..)
    , ConstAppResult(..)
    , makeConstantApp
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

newtype SizeVar = SizeVar Int

-- | An 'IntMap' from size variables to sizes.
newtype SizeValues = SizeValues (IntMap Size)

instance Enum SizeVar where
    toEnum = SizeVar
    fromEnum (SizeVar sizeIndex) = sizeIndex

makeConstantApp :: TypedBuiltin Size a -> a -> ConstAppResult
makeConstantApp builtin x = case makeConstant builtin x of
    Nothing -> ConstAppFailure
    Just wc -> ConstAppSuccess wc

sizeAt :: SizeVar -> SizeValues -> Size
sizeAt (SizeVar sizeIndex) (SizeValues sizes) = sizes IntMap.! sizeIndex

checkBuiltinSize :: Maybe Size -> Size -> Constant () -> b -> Either ConstAppError (b, Size)
checkBuiltinSize (Just size) size' constant _ | size /= size' =
    Left $ SizeMismatchConstAppError size constant
checkBuiltinSize  _          size' _        y = Right (y, size')

expandSizeVars :: SizeValues -> TypedBuiltin SizeVar a -> TypedBuiltin Size a
expandSizeVars = fmapSizeTypedBuiltin . flip sizeAt

extractSizedBuiltin
    :: TypedBuiltinSized a -> Maybe Size -> Constant () -> Either ConstAppError (a, Size)
extractSizedBuiltin TypedBuiltinSizedInt  maySize constant@(BuiltinInt  () size' int) =
    checkBuiltinSize maySize size' constant int
extractSizedBuiltin TypedBuiltinSizedBS   maySize constant@(BuiltinBS   () size' bs ) =
    checkBuiltinSize maySize size' constant bs
extractSizedBuiltin TypedBuiltinSizedSize maySize constant@(BuiltinSize () size'    ) =
    checkBuiltinSize maySize size' constant size'
extractSizedBuiltin tbs            _       constant                            =
    Left $ IllTypedConstAppError (eraseTypedBuiltinSized tbs) constant

extractBuiltin
    :: TypedBuiltin SizeVar a
    -> SizeValues
    -> Value TyName Name ()
    -> Either ConstAppError (a, SizeValues)
extractBuiltin (TypedBuiltinSized (SizeVar sizeIndex) tbs) (SizeValues sizes) value = case value of
    Constant () constant -> unPairT . fmap SizeValues $ IntMap.alterF upd sizeIndex sizes where
        upd maySize = fmap Just . PairT $ extractSizedBuiltin tbs maySize constant
    _                    -> Left $ SizedValueConstAppError value
extractBuiltin TypedBuiltinBool                            _                  _     =
    -- Plan: evaluate the 'value' to a dynamically typed Church-encoded 'Bool'
    -- specialized to 'Bool' and coerce it to an actual 'Bool'.
    Left NotImplementedConstAppError

-- | Coerce a PLC value to a Haskell value.
extractSchemed
    :: TypeScheme SizeVar a -> SizeValues -> Value TyName Name () -> Either ConstAppError (a, SizeValues)
extractSchemed (TypeSchemeBuiltin a) sizeValues value = extractBuiltin a sizeValues value
extractSchemed (TypeSchemeArrow _ _) _          _     = Left NotImplementedConstAppError
extractSchemed (TypeSchemeAllSize _) _          _     = Left NotImplementedConstAppError

-- | Apply a 'TypedBuiltinName' to a list of constant arguments.
applyTypedBuiltinName :: TypedBuiltinName a -> a -> [Value TyName Name ()] -> ConstAppResult
applyTypedBuiltinName (TypedBuiltinName _ schema) = go schema (SizeVar 0) (SizeValues mempty) where
    go :: TypeScheme SizeVar a -> SizeVar -> SizeValues -> a -> [Value TyName Name ()] -> ConstAppResult
    go (TypeSchemeBuiltin builtin) _       sizeValues y args = case args of  -- Computed the result
        [] -> makeConstantApp (expandSizeVars sizeValues builtin) y
        _  -> ConstAppError $ ExcessArgumentsConstAppError args
    go (TypeSchemeArrow schA schB) sizeVar sizeValues f args = case args of
        []          -> ConstAppStuck                         -- Not enough arguments to compute.
        arg : args' ->                                       -- Peel off one argument.
            case extractSchemed schA sizeValues arg of       -- Coerce the argument to a Haskell value.
                Left err               -> ConstAppError err  -- The coercion resulted in an error.
                Right (x, sizeValues') ->
                    go schB sizeVar sizeValues' (f x) args'  -- Apply the function to the coerced argument, proceed recursively.
    go (TypeSchemeAllSize schK)    sizeVar sizeValues f args =
        go (schK sizeVar) (succ sizeVar) sizeValues f args  -- Instantiate the `forall` with a fresh var and proceed recursively.

-- | Apply a 'BuiltinName' to a list of arguments.
applyBuiltinName :: BuiltinName -> [Value TyName Name ()] -> ConstAppResult
applyBuiltinName AddInteger           = applyTypedBuiltinName typedAddInteger           (+)
applyBuiltinName SubtractInteger      = applyTypedBuiltinName typedSubtractInteger      (-)
applyBuiltinName MultiplyInteger      = applyTypedBuiltinName typedMultiplyInteger      (*)
applyBuiltinName DivideInteger        = applyTypedBuiltinName typedDivideInteger        div
applyBuiltinName RemainderInteger     = applyTypedBuiltinName typedRemainderInteger     mod
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
