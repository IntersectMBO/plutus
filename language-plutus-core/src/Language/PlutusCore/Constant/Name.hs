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

-- import           Language.PlutusCore.Constant.Dynamic.Instances ()
import           Language.PlutusCore.Constant.DefaultUni
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type

import qualified Data.ByteString.Lazy.Char8            as BSL

-- | Apply a continuation to the typed version of a 'BuiltinName'.
withTypedBuiltinName
    :: HasDefaultUni uni => BuiltinName -> (forall a r. TypedBuiltinName uni a r -> c) -> c
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

-- oneArg
--     :: (KnownType a uni, KnownType b uni)
--     => TypeScheme uni '[a] b
-- oneArg =
--     Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- twoArgs
--     :: (KnownType a uni, KnownType b uni, KnownType c uni)
--     => TypeScheme uni '[a, b] c
-- twoArgs =
--     Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- threeArgs
--     :: (KnownType a uni, KnownType b uni, KnownType c uni, KnownType d uni)
--     => TypeScheme uni '[a, b, c] d
-- threeArgs =
--     Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- | Typed 'AddInteger'.
typedAddInteger
    :: TypedBuiltinName uni '[Integer, Integer] Integer
typedAddInteger = TypedBuiltinName AddInteger undefined

-- | Typed 'SubtractInteger'.
typedSubtractInteger
    :: TypedBuiltinName uni '[Integer, Integer] Integer
typedSubtractInteger = TypedBuiltinName SubtractInteger undefined

-- | Typed 'MultiplyInteger'.
typedMultiplyInteger
    :: TypedBuiltinName uni '[Integer, Integer] Integer
typedMultiplyInteger = TypedBuiltinName MultiplyInteger undefined

-- | Typed 'DivideInteger'.
typedDivideInteger
    :: uni `Includes` Integer
    => TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedDivideInteger =
    TypedBuiltinName DivideInteger $
        TypeGroundValue knownUni `TypeSchemeArrow`
        TypeGroundValue knownUni `TypeSchemeArrow`
        TypeSchemeResult (TypeGroundResult knownUni)

-- | Typed 'QuotientInteger'
typedQuotientInteger
    :: TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedQuotientInteger = TypedBuiltinName QuotientInteger undefined

-- | Typed 'RemainderInteger'.
typedRemainderInteger
    :: TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedRemainderInteger = TypedBuiltinName RemainderInteger undefined

-- | Typed 'ModInteger'
typedModInteger
    :: TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedModInteger = TypedBuiltinName ModInteger undefined

-- | Typed 'LessThanInteger'.
typedLessThanInteger
    :: TypedBuiltinName uni '[Integer, Integer] Bool
typedLessThanInteger = TypedBuiltinName LessThanInteger undefined

-- | Typed 'LessThanEqInteger'.
typedLessThanEqInteger
    :: TypedBuiltinName uni '[Integer, Integer] Bool
typedLessThanEqInteger = TypedBuiltinName LessThanEqInteger undefined

-- | Typed 'GreaterThanInteger'.
typedGreaterThanInteger
    :: TypedBuiltinName uni '[Integer, Integer] Bool
typedGreaterThanInteger = TypedBuiltinName GreaterThanInteger undefined

-- | Typed 'GreaterThanEqInteger'.
typedGreaterThanEqInteger
    :: TypedBuiltinName uni '[Integer, Integer] Bool
typedGreaterThanEqInteger = TypedBuiltinName GreaterThanEqInteger undefined

-- | Typed 'EqInteger'.
typedEqInteger
    :: TypedBuiltinName uni '[Integer, Integer] Bool
typedEqInteger = TypedBuiltinName EqInteger undefined

-- | Typed 'Concatenate'.
typedConcatenate
    :: TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] BSL.ByteString
typedConcatenate = TypedBuiltinName Concatenate undefined

-- | Typed 'TakeByteString'.
typedTakeByteString
    :: TypedBuiltinName uni '[Integer, BSL.ByteString] BSL.ByteString
typedTakeByteString = TypedBuiltinName TakeByteString undefined

-- | Typed 'DropByteString'.
typedDropByteString
    :: TypedBuiltinName uni '[Integer, BSL.ByteString] BSL.ByteString
typedDropByteString = TypedBuiltinName DropByteString undefined

-- | Typed 'SHA2'.
typedSHA2
    :: TypedBuiltinName uni '[BSL.ByteString] BSL.ByteString
typedSHA2 = TypedBuiltinName SHA2 undefined

-- | Typed 'SHA3'.
typedSHA3
    :: TypedBuiltinName uni '[BSL.ByteString] BSL.ByteString
typedSHA3 = TypedBuiltinName SHA3 undefined

-- | Typed 'VerifySignature'.
typedVerifySignature
    :: TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString, BSL.ByteString] (EvaluationResult Bool)
typedVerifySignature = TypedBuiltinName VerifySignature undefined

-- | Typed 'EqByteString'.
typedEqByteString
    :: TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] Bool
typedEqByteString = TypedBuiltinName EqByteString undefined

-- | Typed 'LtByteString'.
typedLtByteString
    :: TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] Bool
typedLtByteString = TypedBuiltinName LtByteString undefined

-- | Typed 'GtByteString'.
typedGtByteString
    :: TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] Bool
typedGtByteString = TypedBuiltinName GtByteString undefined
