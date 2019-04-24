{-# LANGUAGE RankNTypes #-}

module Language.PlutusCore.Constant.Name
    ( withTypedBuiltinName
    , typedAddInteger
    , typedSubtractInteger
    , typedMultiplyInteger
    , typedDivideInteger
    , typedQuotientInteger
    , typedModInteger
    , typedRemainderInteger
    , typedLessThanInteger
    , typedLessThanEqInteger
    , typedGreaterThanInteger
    , typedGreaterThanEqInteger
    , typedEqInteger
    , typedIntToByteString
    , typedConcatenate
    , typedTakeByteString
    , typedDropByteString
    , typedSHA2
    , typedSHA3
    , typedVerifySignature
    , typedEqByteString
    ) where

import           Language.PlutusCore.Constant.Dynamic.Instances ()
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type

import qualified Data.ByteString.Lazy.Char8                     as BSL

-- | Apply a continuation to the typed version of a 'BuiltinName'.
withTypedBuiltinName :: BuiltinName -> (forall a r. TypedBuiltinName a r -> c) -> c
withTypedBuiltinName AddInteger           k = k typedAddInteger
withTypedBuiltinName SubtractInteger      k = k typedSubtractInteger
withTypedBuiltinName MultiplyInteger      k = k typedMultiplyInteger
withTypedBuiltinName DivideInteger        k = k typedDivideInteger
withTypedBuiltinName QuotientInteger      k = k typedQuotientInteger
withTypedBuiltinName RemainderInteger     k = k typedRemainderInteger
withTypedBuiltinName ModInteger           k = k typedModInteger
withTypedBuiltinName LessThanInteger      k = k typedLessThanInteger
withTypedBuiltinName LessThanEqInteger    k = k typedLessThanEqInteger
withTypedBuiltinName GreaterThanInteger   k = k typedGreaterThanInteger
withTypedBuiltinName GreaterThanEqInteger k = k typedGreaterThanEqInteger
withTypedBuiltinName EqInteger            k = k typedEqInteger
withTypedBuiltinName IntToByteString      k = k typedIntToByteString
withTypedBuiltinName Concatenate          k = k typedConcatenate
withTypedBuiltinName TakeByteString       k = k typedTakeByteString
withTypedBuiltinName DropByteString       k = k typedDropByteString
withTypedBuiltinName SHA2                 k = k typedSHA2
withTypedBuiltinName SHA3                 k = k typedSHA3
withTypedBuiltinName VerifySignature      k = k typedVerifySignature
withTypedBuiltinName EqByteString         k = k typedEqByteString

sizeIntIntInt :: TypeScheme (Integer -> Integer -> Integer) Integer
sizeIntIntInt =
    TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedInt) `TypeSchemeArrow`
    TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedInt) `TypeSchemeArrow`
    TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedInt)

sizeIntIntBool :: TypeScheme (Integer -> Integer -> Bool) Bool
sizeIntIntBool =
    TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedInt) `TypeSchemeArrow`
    TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedInt) `TypeSchemeArrow`
    TypeSchemeBuiltin TypedBuiltinDyn

-- | Typed 'AddInteger'.
typedAddInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedAddInteger = TypedBuiltinName AddInteger sizeIntIntInt

-- | Typed 'SubtractInteger'.
typedSubtractInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedSubtractInteger = TypedBuiltinName SubtractInteger sizeIntIntInt

-- | Typed 'MultiplyInteger'.
typedMultiplyInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedMultiplyInteger = TypedBuiltinName MultiplyInteger sizeIntIntInt

-- | Typed 'DivideInteger'.
typedDivideInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedDivideInteger = TypedBuiltinName DivideInteger sizeIntIntInt

-- | Typed 'QuotientInteger'
typedQuotientInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedQuotientInteger = TypedBuiltinName QuotientInteger sizeIntIntInt

-- | Typed 'RemainderInteger'.
typedRemainderInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedRemainderInteger = TypedBuiltinName RemainderInteger sizeIntIntInt

-- | Typed 'ModInteger'
typedModInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedModInteger = TypedBuiltinName ModInteger sizeIntIntInt

-- | Typed 'LessThanInteger'.
typedLessThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedLessThanInteger = TypedBuiltinName LessThanInteger sizeIntIntBool

-- | Typed 'LessThanEqInteger'.
typedLessThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedLessThanEqInteger = TypedBuiltinName LessThanEqInteger sizeIntIntBool

-- | Typed 'GreaterThanInteger'.
typedGreaterThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedGreaterThanInteger = TypedBuiltinName GreaterThanInteger sizeIntIntBool

-- | Typed 'GreaterThanEqInteger'.
typedGreaterThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedGreaterThanEqInteger = TypedBuiltinName GreaterThanEqInteger sizeIntIntBool

-- | Typed 'EqInteger'.
typedEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedEqInteger = TypedBuiltinName EqInteger sizeIntIntBool

-- | Typed 'IntToByteString'.
typedIntToByteString :: TypedBuiltinName (Integer -> BSL.ByteString) BSL.ByteString
typedIntToByteString =
    TypedBuiltinName IntToByteString $
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS)

-- | Typed 'Concatenate'.
typedConcatenate :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedConcatenate =
    TypedBuiltinName Concatenate $
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS)

-- | Typed 'TakeByteString'.
typedTakeByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedTakeByteString =
    TypedBuiltinName TakeByteString $
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS)

-- | Typed 'DropByteString'.
typedDropByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedDropByteString =
    TypedBuiltinName DropByteString $
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS)

-- | Typed 'SHA2'.
typedSHA2 :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedSHA2 =
    TypedBuiltinName SHA2 $
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS)

-- | Typed 'SHA3'.
typedSHA3 :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedSHA3 =
    TypedBuiltinName SHA3 $
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS)

-- | Typed 'VerifySignature'.
typedVerifySignature :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString -> EvaluationResult Bool) (EvaluationResult Bool)
typedVerifySignature =
    TypedBuiltinName VerifySignature $
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin TypedBuiltinDyn

-- | Typed 'EqByteString'.
typedEqByteString :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> Bool) Bool
typedEqByteString =
    TypedBuiltinName EqByteString $
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized TypedBuiltinSizedBS) `TypeSchemeArrow`
        TypeSchemeBuiltin TypedBuiltinDyn
