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
    , typedConcatenate
    , typedTakeByteString
    , typedDropByteString
    , typedSHA2
    , typedSHA3
    , typedVerifySignature
    , typedEqByteString
    , typedLtByteString
    , typedGtByteString
    ) where

import           Language.PlutusCore.Constant.Dynamic.Instances     ()
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Result

import qualified Data.ByteString.Lazy.Char8                         as BSL
import           Data.Proxy

-- | Apply a continuation to the typed version of a 'BuiltinName'.
withTypedBuiltinName :: BuiltinName -> (forall a exA r. TypedBuiltinName a exA r -> c) -> c
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
withTypedBuiltinName Concatenate          k = k typedConcatenate
withTypedBuiltinName TakeByteString       k = k typedTakeByteString
withTypedBuiltinName DropByteString       k = k typedDropByteString
withTypedBuiltinName SHA2                 k = k typedSHA2
withTypedBuiltinName SHA3                 k = k typedSHA3
withTypedBuiltinName VerifySignature      k = k typedVerifySignature
withTypedBuiltinName EqByteString         k = k typedEqByteString
withTypedBuiltinName LtByteString         k = k typedLtByteString
withTypedBuiltinName GtByteString         k = k typedGtByteString

intIntInt :: TypeScheme (Integer -> Integer -> Integer) (Integer -> Integer -> ExBudget) Integer
intIntInt = Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

intIntResInt :: TypeScheme (Integer -> Integer -> EvaluationResult Integer) (Integer -> Integer -> ExBudget) (EvaluationResult Integer)
intIntResInt = Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

intIntDyn :: KnownType a => TypeScheme (Integer -> Integer -> a) (Integer -> Integer -> ExBudget) a
intIntDyn = Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'AddInteger'.
typedAddInteger :: TypedBuiltinName (Integer -> Integer -> Integer) (Integer -> Integer -> ExBudget) Integer
typedAddInteger = TypedBuiltinName AddInteger intIntInt

-- | Typed 'SubtractInteger'.
typedSubtractInteger :: TypedBuiltinName (Integer -> Integer -> Integer) (Integer -> Integer -> ExBudget) Integer
typedSubtractInteger = TypedBuiltinName SubtractInteger intIntInt

-- | Typed 'MultiplyInteger'.
typedMultiplyInteger :: TypedBuiltinName (Integer -> Integer -> Integer) (Integer -> Integer -> ExBudget) Integer
typedMultiplyInteger = TypedBuiltinName MultiplyInteger intIntInt

-- | Typed 'DivideInteger'.
typedDivideInteger
    :: TypedBuiltinName (Integer -> Integer -> EvaluationResult Integer) (Integer -> Integer -> ExBudget) (EvaluationResult Integer)
typedDivideInteger = TypedBuiltinName DivideInteger intIntResInt

-- | Typed 'QuotientInteger'
typedQuotientInteger
    :: TypedBuiltinName (Integer -> Integer -> EvaluationResult Integer) (Integer -> Integer -> ExBudget) (EvaluationResult Integer)
typedQuotientInteger = TypedBuiltinName QuotientInteger intIntResInt

-- | Typed 'RemainderInteger'.
typedRemainderInteger
    :: TypedBuiltinName (Integer -> Integer -> EvaluationResult Integer) (Integer -> Integer -> ExBudget) (EvaluationResult Integer)
typedRemainderInteger = TypedBuiltinName RemainderInteger intIntResInt

-- | Typed 'ModInteger'
typedModInteger
    :: TypedBuiltinName (Integer -> Integer -> EvaluationResult Integer) (Integer -> Integer -> ExBudget) (EvaluationResult Integer)
typedModInteger = TypedBuiltinName ModInteger intIntResInt

-- | Typed 'LessThanInteger'.
typedLessThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool) (Integer -> Integer -> ExBudget) Bool
typedLessThanInteger = TypedBuiltinName LessThanInteger intIntDyn

-- | Typed 'LessThanEqInteger'.
typedLessThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) (Integer -> Integer -> ExBudget) Bool
typedLessThanEqInteger = TypedBuiltinName LessThanEqInteger intIntDyn

-- | Typed 'GreaterThanInteger'.
typedGreaterThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool) (Integer -> Integer -> ExBudget) Bool
typedGreaterThanInteger = TypedBuiltinName GreaterThanInteger intIntDyn

-- | Typed 'GreaterThanEqInteger'.
typedGreaterThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) (Integer -> Integer -> ExBudget) Bool
typedGreaterThanEqInteger = TypedBuiltinName GreaterThanEqInteger intIntDyn

-- | Typed 'EqInteger'.
typedEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) (Integer -> Integer -> ExBudget) Bool
typedEqInteger = TypedBuiltinName EqInteger intIntDyn

-- | Typed 'Concatenate'.
typedConcatenate :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString) (BSL.ByteString -> BSL.ByteString -> ExBudget) BSL.ByteString
typedConcatenate =
    TypedBuiltinName Concatenate $
        Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'TakeByteString'.
typedTakeByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) (Integer -> BSL.ByteString -> ExBudget) BSL.ByteString
typedTakeByteString =
    TypedBuiltinName TakeByteString $
        Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'DropByteString'.
typedDropByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) (Integer -> BSL.ByteString -> ExBudget) BSL.ByteString
typedDropByteString =
    TypedBuiltinName DropByteString $
        Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'SHA2'.
typedSHA2 :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString) (BSL.ByteString -> ExBudget) BSL.ByteString
typedSHA2 =
    TypedBuiltinName SHA2 $
        Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'SHA3'.
typedSHA3 :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString) (BSL.ByteString -> ExBudget) BSL.ByteString
typedSHA3 =
    TypedBuiltinName SHA3 $
        Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'VerifySignature'.
typedVerifySignature :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString -> EvaluationResult Bool) (BSL.ByteString -> BSL.ByteString -> BSL.ByteString -> ExBudget) (EvaluationResult Bool)
typedVerifySignature =
    TypedBuiltinName VerifySignature $
        Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'EqByteString'.
typedEqByteString :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> Bool) (BSL.ByteString -> BSL.ByteString -> ExBudget) Bool
typedEqByteString =
    TypedBuiltinName EqByteString $
        Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'LtByteString'.
typedLtByteString :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> Bool) (BSL.ByteString -> BSL.ByteString -> ExBudget) Bool
typedLtByteString =
    TypedBuiltinName LtByteString $
        Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'GtByteString'.
typedGtByteString :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> Bool) (BSL.ByteString -> BSL.ByteString -> ExBudget) Bool
typedGtByteString =
    TypedBuiltinName GtByteString $
        Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy
