{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
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
    , typedIfThenElse
    ) where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Universe

import qualified Data.ByteString.Lazy                  as BSL
import           Data.Proxy

-- | A class that allows to derive a 'TypeScheme' for a builtin.
class KnownTypeScheme uni args res where
    knownTypeScheme :: TypeScheme uni args res

instance KnownType uni r => KnownTypeScheme uni '[] r where
    knownTypeScheme = TypeSchemeResult Proxy

instance (KnownType uni arg, KnownTypeScheme uni args res) =>
            KnownTypeScheme uni (arg ': args) res where
    knownTypeScheme = Proxy `TypeSchemeArrow` knownTypeScheme

-- | Automatically typify a 'BuiltinName'.
makeTypedBuiltinName :: KnownTypeScheme uni args res => BuiltinName -> TypedBuiltinName uni args res
makeTypedBuiltinName name = TypedBuiltinName name knownTypeScheme

-- | Apply a continuation to the typed version of a 'BuiltinName'.
withTypedBuiltinName
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => BuiltinName -> (forall args res. TypedBuiltinName uni args res -> c) -> c
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
withTypedBuiltinName IfThenElse           k = k typedIfThenElse

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
    :: (GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedBuiltinName uni '[Integer, Integer] Bool
typedLessThanInteger = makeTypedBuiltinName LessThanInteger

-- | Typed 'LessThanEqInteger'.
typedLessThanEqInteger
    :: (GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedBuiltinName uni '[Integer, Integer] Bool
typedLessThanEqInteger = makeTypedBuiltinName LessThanEqInteger

-- | Typed 'GreaterThanInteger'.
typedGreaterThanInteger
    :: (GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedBuiltinName uni '[Integer, Integer] Bool
typedGreaterThanInteger = makeTypedBuiltinName GreaterThanInteger

-- | Typed 'GreaterThanEqInteger'.
typedGreaterThanEqInteger
    :: (GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedBuiltinName uni '[Integer, Integer] Bool
typedGreaterThanEqInteger = makeTypedBuiltinName GreaterThanEqInteger

-- | Typed 'EqInteger'.
typedEqInteger
    :: (GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedBuiltinName uni '[Integer, Integer] Bool
typedEqInteger = makeTypedBuiltinName EqInteger

-- | Typed 'Concatenate'.
typedConcatenate
    :: (GShow uni, GEq uni, uni `Includes` BSL.ByteString)
    => TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] BSL.ByteString
typedConcatenate = makeTypedBuiltinName Concatenate

-- | Typed 'TakeByteString'.
typedTakeByteString
    :: (GShow uni, GEq uni, uni `IncludesAll` '[Integer, BSL.ByteString])
    => TypedBuiltinName uni '[Integer, BSL.ByteString] BSL.ByteString
typedTakeByteString = makeTypedBuiltinName TakeByteString

-- | Typed 'DropByteString'.
typedDropByteString
    :: (GShow uni, GEq uni, uni `IncludesAll` '[Integer, BSL.ByteString])
    => TypedBuiltinName uni '[Integer, BSL.ByteString] BSL.ByteString
typedDropByteString = makeTypedBuiltinName DropByteString

-- | Typed 'SHA2'.
typedSHA2
    :: (GShow uni, GEq uni, uni `Includes` BSL.ByteString)
    => TypedBuiltinName uni '[BSL.ByteString] BSL.ByteString
typedSHA2 = makeTypedBuiltinName SHA2

-- | Typed 'SHA3'.
typedSHA3
    :: (GShow uni, GEq uni, uni `Includes` BSL.ByteString)
    => TypedBuiltinName uni '[BSL.ByteString] BSL.ByteString
typedSHA3 = makeTypedBuiltinName SHA3

-- | Typed 'VerifySignature'.
typedVerifySignature
    :: (GShow uni, GEq uni, uni `IncludesAll` '[BSL.ByteString, Bool])
    => TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString, BSL.ByteString] (EvaluationResult Bool)
typedVerifySignature = makeTypedBuiltinName VerifySignature

-- | Typed 'EqByteString'.
typedEqByteString
    :: (GShow uni, GEq uni, uni `IncludesAll` '[BSL.ByteString, Bool])
    => TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] Bool
typedEqByteString = makeTypedBuiltinName EqByteString

-- | Typed 'LtByteString'.
typedLtByteString
    :: (GShow uni, GEq uni, uni `IncludesAll` '[BSL.ByteString, Bool])
    => TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] Bool
typedLtByteString = makeTypedBuiltinName LtByteString

-- | Typed 'GtByteString'.
typedGtByteString
    :: (GShow uni, GEq uni, uni `IncludesAll` '[BSL.ByteString, Bool])
    => TypedBuiltinName uni '[BSL.ByteString, BSL.ByteString] Bool
typedGtByteString = makeTypedBuiltinName GtByteString

-- | Typed 'IfThenElse'.
typedIfThenElse
    :: (GShow uni, GEq uni, uni `IncludesAll` '[BSL.ByteString, Bool])
    => TypedBuiltinName uni '[Bool, OpaqueTerm uni "a" 0, OpaqueTerm uni "a" 0] (OpaqueTerm uni "a" 0)
typedIfThenElse =
    TypedBuiltinName IfThenElse $
        TypeSchemeAllType @"a" @0 Proxy $ \_ -> knownTypeScheme
