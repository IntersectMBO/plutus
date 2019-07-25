{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeOperators #-}

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

import           Language.PlutusCore.Constant.Dynamic.Instances ()
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type

import qualified Data.ByteString.Lazy.Char8                     as BSL
import           Data.Proxy

-- | Apply a continuation to the typed version of a 'BuiltinName'.
withTypedBuiltinName
    :: Evaluable uni => BuiltinName -> (forall a r. TypedBuiltinName uni a r -> c) -> c
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

oneArg
    :: (KnownType a uni, KnownType b uni)
    => TypeScheme uni '[a] b
oneArg =
    Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

twoArgs
    :: (KnownType a uni, KnownType b uni, KnownType c uni)
    => TypeScheme uni '[a, b] c
twoArgs =
    Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

threeArgs
    :: (KnownType a uni, KnownType b uni, KnownType c uni, KnownType d uni)
    => TypeScheme uni '[a, b, c] d
threeArgs =
    Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'AddInteger'.
typedAddInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] Integer
typedAddInteger = TypedBuiltinName AddInteger twoArgs

-- | Typed 'SubtractInteger'.
typedSubtractInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] Integer
typedSubtractInteger = TypedBuiltinName SubtractInteger twoArgs

-- | Typed 'MultiplyInteger'.
typedMultiplyInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] Integer
typedMultiplyInteger = TypedBuiltinName MultiplyInteger twoArgs

-- | Typed 'DivideInteger'.
typedDivideInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedDivideInteger = TypedBuiltinName DivideInteger twoArgs

-- | Typed 'QuotientInteger'
typedQuotientInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedQuotientInteger = TypedBuiltinName QuotientInteger twoArgs

-- | Typed 'RemainderInteger'.
typedRemainderInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedRemainderInteger = TypedBuiltinName RemainderInteger twoArgs

-- | Typed 'ModInteger'
typedModInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedModInteger = TypedBuiltinName ModInteger twoArgs

-- | Typed 'LessThanInteger'.
typedLessThanInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] Bool
typedLessThanInteger = TypedBuiltinName LessThanInteger twoArgs

-- | Typed 'LessThanEqInteger'.
typedLessThanEqInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] Bool
typedLessThanEqInteger = TypedBuiltinName LessThanEqInteger twoArgs

-- | Typed 'GreaterThanInteger'.
typedGreaterThanInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] Bool
typedGreaterThanInteger = TypedBuiltinName GreaterThanInteger twoArgs

-- | Typed 'GreaterThanEqInteger'.
typedGreaterThanEqInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] Bool
typedGreaterThanEqInteger = TypedBuiltinName GreaterThanEqInteger twoArgs

-- | Typed 'EqInteger'.
typedEqInteger
    :: Evaluable uni => TypedBuiltinName uni '[Integer, Integer] Bool
typedEqInteger = TypedBuiltinName EqInteger twoArgs

-- | Typed 'Concatenate'.
typedConcatenate
    :: Evaluable uni => TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] BSL.ByteString
typedConcatenate = TypedBuiltinName Concatenate twoArgs

-- | Typed 'TakeByteString'.
typedTakeByteString
    :: Evaluable uni => TypedBuiltinName uni '[Integer, BSL.ByteString] BSL.ByteString
typedTakeByteString = TypedBuiltinName TakeByteString twoArgs

-- | Typed 'DropByteString'.
typedDropByteString
    :: Evaluable uni => TypedBuiltinName uni '[Integer, BSL.ByteString] BSL.ByteString
typedDropByteString = TypedBuiltinName DropByteString twoArgs

-- | Typed 'SHA2'.
typedSHA2
    :: Evaluable uni => TypedBuiltinName uni '[BSL.ByteString] BSL.ByteString
typedSHA2 = TypedBuiltinName SHA2 oneArg

-- | Typed 'SHA3'.
typedSHA3
    :: Evaluable uni => TypedBuiltinName uni '[BSL.ByteString] BSL.ByteString
typedSHA3 = TypedBuiltinName SHA3 oneArg

-- | Typed 'VerifySignature'.
typedVerifySignature
    :: Evaluable uni => TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString, BSL.ByteString] (EvaluationResult Bool)
typedVerifySignature = TypedBuiltinName VerifySignature threeArgs

-- | Typed 'EqByteString'.
typedEqByteString
    :: Evaluable uni => TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] Bool
typedEqByteString = TypedBuiltinName EqByteString twoArgs

-- | Typed 'LtByteString'.
typedLtByteString
    :: Evaluable uni => TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] Bool
typedLtByteString = TypedBuiltinName LtByteString twoArgs

-- | Typed 'GtByteString'.
typedGtByteString
    :: Evaluable uni => TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] Bool
typedGtByteString = TypedBuiltinName GtByteString twoArgs
