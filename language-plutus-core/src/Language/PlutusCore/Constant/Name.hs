{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}

module Language.PlutusCore.Constant.Name
    ( makeTypedBuiltinName
    , withTypedBuiltinName
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
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Universe

import           Data.Proxy

class KnownTypeScheme uni as r where
    knownTypeScheme :: TypeScheme uni as r

instance KnownType uni r => KnownTypeScheme uni '[] r where
    knownTypeScheme = TypeSchemeResult Proxy

instance (KnownType uni a, KnownTypeScheme uni as r) => KnownTypeScheme uni (a ': as) r where
    knownTypeScheme = Proxy `TypeSchemeArrow` knownTypeScheme

makeTypedBuiltinName :: KnownTypeScheme uni as r => BuiltinName -> TypedBuiltinName uni as r
makeTypedBuiltinName name = TypedBuiltinName name knownTypeScheme

-- | Apply a continuation to the typed version of a 'BuiltinName'.
withTypedBuiltinName
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => BuiltinName -> (forall a r. TypedBuiltinName uni a r -> c) -> c
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

-- | Typed 'AddInteger'.
typedAddInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] Integer
typedAddInteger = makeTypedBuiltinName AddInteger

-- | Typed 'SubtractInteger'.
typedSubtractInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] Integer
typedSubtractInteger = makeTypedBuiltinName SubtractInteger

-- | Typed 'MultiplyInteger'.
typedMultiplyInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] Integer
typedMultiplyInteger = makeTypedBuiltinName MultiplyInteger

-- | Typed 'DivideInteger'.
typedDivideInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedDivideInteger = makeTypedBuiltinName DivideInteger

-- | Typed 'QuotientInteger'
typedQuotientInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedQuotientInteger = makeTypedBuiltinName QuotientInteger

-- | Typed 'RemainderInteger'.
typedRemainderInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedRemainderInteger = makeTypedBuiltinName RemainderInteger

-- | Typed 'ModInteger'
typedModInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] (EvaluationResult Integer)
typedModInteger = makeTypedBuiltinName ModInteger

-- | Typed 'LessThanInteger'.
typedLessThanInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] Bool
typedLessThanInteger = makeTypedBuiltinName LessThanInteger

-- | Typed 'LessThanEqInteger'.
typedLessThanEqInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] Bool
typedLessThanEqInteger = makeTypedBuiltinName LessThanEqInteger

-- | Typed 'GreaterThanInteger'.
typedGreaterThanInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] Bool
typedGreaterThanInteger = makeTypedBuiltinName GreaterThanInteger

-- | Typed 'GreaterThanEqInteger'.
typedGreaterThanEqInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] Bool
typedGreaterThanEqInteger = makeTypedBuiltinName GreaterThanEqInteger

-- | Typed 'EqInteger'.
typedEqInteger
    :: (GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName uni '[Integer, Integer] Bool
typedEqInteger = makeTypedBuiltinName EqInteger

-- | Typed 'Concatenate'.
typedConcatenate
    :: (GShow uni, GEq uni, uni `Includes` ByteString16)
    => TypedBuiltinName uni '[ByteString16, ByteString16] ByteString16
typedConcatenate = makeTypedBuiltinName Concatenate

-- | Typed 'TakeByteString'.
typedTakeByteString
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` ByteString16)
    => TypedBuiltinName uni '[Integer, ByteString16] ByteString16
typedTakeByteString = makeTypedBuiltinName TakeByteString

-- | Typed 'DropByteString'.
typedDropByteString
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` ByteString16)
    => TypedBuiltinName uni '[Integer, ByteString16] ByteString16
typedDropByteString = makeTypedBuiltinName DropByteString

-- | Typed 'SHA2'.
typedSHA2
    :: (GShow uni, GEq uni, uni `Includes` ByteString16)
    => TypedBuiltinName uni '[ByteString16] ByteString16
typedSHA2 = makeTypedBuiltinName SHA2

-- | Typed 'SHA3'.
typedSHA3
    :: (GShow uni, GEq uni, uni `Includes` ByteString16)
    => TypedBuiltinName uni '[ByteString16] ByteString16
typedSHA3 = makeTypedBuiltinName SHA3

-- | Typed 'VerifySignature'.
typedVerifySignature
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` ByteString16)
    => TypedBuiltinName uni '[ByteString16, ByteString16, ByteString16] (EvaluationResult Bool)
typedVerifySignature = makeTypedBuiltinName VerifySignature

-- | Typed 'EqByteString'.
typedEqByteString
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` ByteString16)
    => TypedBuiltinName uni '[ByteString16, ByteString16] Bool
typedEqByteString = makeTypedBuiltinName EqByteString

-- | Typed 'LtByteString'.
typedLtByteString
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` ByteString16)
    => TypedBuiltinName uni '[ByteString16, ByteString16] Bool
typedLtByteString = makeTypedBuiltinName LtByteString

-- | Typed 'GtByteString'.
typedGtByteString
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` ByteString16)
    => TypedBuiltinName uni '[ByteString16, ByteString16] Bool
typedGtByteString = makeTypedBuiltinName GtByteString
