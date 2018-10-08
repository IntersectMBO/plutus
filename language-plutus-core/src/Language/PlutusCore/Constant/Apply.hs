-- | Computing constant application.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Apply
    ( ConstAppError(..)
    , ConstAppResult(..)
    , makeConstAppResult
    , applyBuiltinName
    ) where

import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Lexer.Type     (BuiltinName (..))
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           PlutusPrelude

import qualified Data.ByteString.Lazy               as BSL
import           Data.IntMap.Strict                 (IntMap)
import qualified Data.IntMap.Strict                 as IntMap

-- | The type of constant applications errors.
data ConstAppError
    = SizeMismatchConstAppError Size (Constant ())
      -- ^ A mismatch between expected and actual sizes.
    | IllTypedConstAppError BuiltinSized (Constant ())
      -- ^ A mismatch between the type of an argument function expects and its actual type.
    | ExcessArgumentsConstAppError [Value TyName Name ()]
      -- ^ A constant is applied to more arguments than needed in order to reduce.
      -- Note that this error occurs even if an expression is well-typed, because
      -- constant application is supposed to be computed as soon as there are enough arguments.
    | SizedNonConstantConstAppError (Value TyName Name ())
      -- ^ An argument of a sized type is not a constant.
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

instance ( PrettyBy config (Constant ())
         , PrettyBy config (Value TyName Name ())
         ) => PrettyBy config ConstAppError where
    prettyBy config (SizeMismatchConstAppError expSize con) = fold
        [ "Size mismatch error:", "\n"
        , "expected size: ", pretty expSize, "\n"
        , "actual constant: ", prettyBy config con
        ]
    prettyBy config (IllTypedConstAppError expType con)     = fold
        [ "Ill-typed constant application:", "\n"
        , "expected type: ", pretty expType, "\n"
        , "actual constant: ", prettyBy config con
        ]
    prettyBy config (ExcessArgumentsConstAppError args)     = fold
        [ "A constant applied to too many arguments:", "\n"
        , "Excess ones are: ", prettyBy config args
        ]
    prettyBy config (SizedNonConstantConstAppError arg)     = fold
        [ "A non-constant argument of a sized type: "
        , prettyBy config arg
        ]

instance ( PrettyBy config (Constant ())
         , PrettyBy config (Value TyName Name ())
         ) => PrettyBy config ConstAppResult where
    prettyBy config (ConstAppSuccess res) = prettyBy config res
    prettyBy _      ConstAppFailure       = "Constant application failure"
    prettyBy _      ConstAppStuck         = "Stuck constant applcation"
    prettyBy config (ConstAppError err)   = prettyBy config err

instance Enum SizeVar where
    toEnum = SizeVar
    fromEnum (SizeVar sizeIndex) = sizeIndex

-- | Same as 'makeBuiltin', but returns a 'ConstAppResult'.
makeConstAppResult :: TypedBuiltinValue Size a -> Quote ConstAppResult
makeConstAppResult = fmap (maybe ConstAppFailure ConstAppSuccess) . makeBuiltin

sizeAt :: SizeVar -> SizeValues -> Size
sizeAt (SizeVar sizeIndex) (SizeValues sizes) = sizes IntMap.! sizeIndex

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
extractSizedBuiltin tbs                   _       constant                            =
    Left $ IllTypedConstAppError (eraseTypedBuiltinSized tbs) constant

expandSizeVars :: SizeValues -> TypedBuiltin SizeVar a -> TypedBuiltin Size a
expandSizeVars = mapSizeTypedBuiltin . flip sizeAt

extractBuiltin
    :: TypedBuiltin SizeVar a
    -> SizeValues
    -> Value TyName Name ()
    -> Either ConstAppError (a, SizeValues)
extractBuiltin (TypedBuiltinSized sizeEntry tbs) (SizeValues sizes) value = case value of
    Constant () constant -> case sizeEntry of
        SizeValue size                ->
            (SizeValues sizes <$) <$> extractSizedBuiltin tbs (Just size) constant
        SizeBound (SizeVar sizeIndex) ->
            unPairT . fmap SizeValues $ IntMap.alterF upd sizeIndex sizes where
                upd maySize = fmap Just . PairT $ extractSizedBuiltin tbs maySize constant
    _                    -> Left $ SizedNonConstantConstAppError value
extractBuiltin TypedBuiltinBool                  _                  _     =
    -- Plan: evaluate the 'value' to a dynamically typed Church-encoded 'Bool'
    -- specialized to 'Bool' and coerce it to an actual 'Bool'.
    error "Not implemented."

-- | Coerce a PLC value to a Haskell value.
extractSchemed
    :: TypeScheme SizeVar a r -> SizeValues -> Value TyName Name () -> Either ConstAppError (a, SizeValues)
extractSchemed (TypeSchemeBuiltin a) sizeValues value = extractBuiltin a sizeValues value
extractSchemed (TypeSchemeArrow _ _) _          _     = error "Not implemented."
extractSchemed (TypeSchemeAllSize _) _          _     = error "Not implemented."

-- | Apply a 'TypedBuiltinName' to a list of 'Value's.
applyTypedBuiltinName
    :: TypedBuiltinName a r -> a -> [Value TyName Name ()] -> Quote ConstAppResult
applyTypedBuiltinName (TypedBuiltinName _ schema) = go schema (SizeVar 0) (SizeValues mempty) where
    go
        :: TypeScheme SizeVar a r
        -> SizeVar -> SizeValues
        -> a
        -> [Value TyName Name ()]
        -> Quote ConstAppResult
    go (TypeSchemeBuiltin tb)      _       sizeValues y args = case args of  -- Computed the result.
        [] -> makeConstAppResult $ TypedBuiltinValue (expandSizeVars sizeValues tb) y
        _  -> return . ConstAppError $ ExcessArgumentsConstAppError args
    go (TypeSchemeArrow schA schB) sizeVar sizeValues f args = case args of
        []          -> return ConstAppStuck                  -- Not enough arguments to compute.
        arg : args' ->                                       -- Peel off one argument.
            case extractSchemed schA sizeValues arg of       -- Coerce the argument to a Haskell value.
                Left err               ->
                    return $ ConstAppError err               -- The coercion resulted in an error.
                Right (x, sizeValues') ->
                    go schB sizeVar sizeValues' (f x) args'  -- Apply the function to the coerced argument
                                                             -- and proceed recursively.
    go (TypeSchemeAllSize schK)    sizeVar sizeValues f args =
        go (schK sizeVar) (succ sizeVar) sizeValues f args  -- Instantiate the `forall` with a fresh var
                                                            -- and proceed recursively.

-- | Apply a 'BuiltinName' to a list of 'Value's.
applyBuiltinName :: BuiltinName -> [Value TyName Name ()] -> Quote ConstAppResult
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
applyBuiltinName IntToByteString      = applyTypedBuiltinName typedIntToByteString      undefined
applyBuiltinName Concatenate          = applyTypedBuiltinName typedConcatenate          (<>)
applyBuiltinName TakeByteString       = applyTypedBuiltinName typedTakeByteString       (BSL.take . fromIntegral)
applyBuiltinName DropByteString       = applyTypedBuiltinName typedDropByteString       (BSL.drop . fromIntegral)
applyBuiltinName ResizeByteString     = applyTypedBuiltinName typedResizeByteString     (const id)
applyBuiltinName SHA2                 = applyTypedBuiltinName typedSHA2                 undefined
applyBuiltinName SHA3                 = applyTypedBuiltinName typedSHA3                 undefined
applyBuiltinName VerifySignature      = applyTypedBuiltinName typedVerifySignature      undefined
applyBuiltinName EqByteString         = applyTypedBuiltinName typedEqByteString         (==)
applyBuiltinName TxHash               = applyTypedBuiltinName typedTxHash               undefined
applyBuiltinName BlockNum             = undefined
