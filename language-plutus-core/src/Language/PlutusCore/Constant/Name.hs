{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

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
class KnownTypeScheme term args res where
    knownTypeScheme :: TypeScheme term args res

instance KnownType term r => KnownTypeScheme term '[] r where
    knownTypeScheme = TypeSchemeResult Proxy

instance (KnownType term arg, KnownTypeScheme term args res) =>
            KnownTypeScheme term (arg ': args) res where
    knownTypeScheme = Proxy `TypeSchemeArrow` knownTypeScheme

-- | Automatically typify a 'BuiltinName'.
makeTypedBuiltinName :: KnownTypeScheme term args res => BuiltinName -> TypedBuiltinName term args res
makeTypedBuiltinName name = TypedBuiltinName name knownTypeScheme

-- | Apply a continuation to the typed version of a 'BuiltinName'.
withTypedBuiltinName
    :: (HasConstantIn uni term, GShow uni, GEq uni, DefaultUni <: uni)
    => BuiltinName -> (forall args res. TypedBuiltinName term args res -> c) -> c
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
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName term '[Integer, Integer] Integer
typedAddInteger = makeTypedBuiltinName AddInteger

-- | Typed 'SubtractInteger'.
typedSubtractInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName term '[Integer, Integer] Integer
typedSubtractInteger = makeTypedBuiltinName SubtractInteger

-- | Typed 'MultiplyInteger'.
typedMultiplyInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName term '[Integer, Integer] Integer
typedMultiplyInteger = makeTypedBuiltinName MultiplyInteger

-- | Typed 'DivideInteger'.
typedDivideInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName term '[Integer, Integer] (EvaluationResult Integer)
typedDivideInteger = makeTypedBuiltinName DivideInteger

-- | Typed 'QuotientInteger'
typedQuotientInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName term '[Integer, Integer] (EvaluationResult Integer)
typedQuotientInteger = makeTypedBuiltinName QuotientInteger

-- | Typed 'RemainderInteger'.
typedRemainderInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName term '[Integer, Integer] (EvaluationResult Integer)
typedRemainderInteger = makeTypedBuiltinName RemainderInteger

-- | Typed 'ModInteger'
typedModInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedBuiltinName term '[Integer, Integer] (EvaluationResult Integer)
typedModInteger = makeTypedBuiltinName ModInteger

-- | Typed 'LessThanInteger'.
typedLessThanInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedBuiltinName term '[Integer, Integer] Bool
typedLessThanInteger = makeTypedBuiltinName LessThanInteger

-- | Typed 'LessThanEqInteger'.
typedLessThanEqInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedBuiltinName term '[Integer, Integer] Bool
typedLessThanEqInteger = makeTypedBuiltinName LessThanEqInteger

-- | Typed 'GreaterThanInteger'.
typedGreaterThanInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedBuiltinName term '[Integer, Integer] Bool
typedGreaterThanInteger = makeTypedBuiltinName GreaterThanInteger

-- | Typed 'GreaterThanEqInteger'.
typedGreaterThanEqInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedBuiltinName term '[Integer, Integer] Bool
typedGreaterThanEqInteger = makeTypedBuiltinName GreaterThanEqInteger

-- | Typed 'EqInteger'.
typedEqInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedBuiltinName term '[Integer, Integer] Bool
typedEqInteger = makeTypedBuiltinName EqInteger

-- | Typed 'Concatenate'.
typedConcatenate
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` BSL.ByteString)
    => TypedBuiltinName term '[BSL.ByteString, BSL.ByteString] BSL.ByteString
typedConcatenate = makeTypedBuiltinName Concatenate

-- | Typed 'TakeByteString'.
typedTakeByteString
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, BSL.ByteString])
    => TypedBuiltinName term '[Integer, BSL.ByteString] BSL.ByteString
typedTakeByteString = makeTypedBuiltinName TakeByteString

-- | Typed 'DropByteString'.
typedDropByteString
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, BSL.ByteString])
    => TypedBuiltinName term '[Integer, BSL.ByteString] BSL.ByteString
typedDropByteString = makeTypedBuiltinName DropByteString

-- | Typed 'SHA2'.
typedSHA2
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` BSL.ByteString)
    => TypedBuiltinName term '[BSL.ByteString] BSL.ByteString
typedSHA2 = makeTypedBuiltinName SHA2

-- | Typed 'SHA3'.
typedSHA3
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` BSL.ByteString)
    => TypedBuiltinName term '[BSL.ByteString] BSL.ByteString
typedSHA3 = makeTypedBuiltinName SHA3

-- | Typed 'VerifySignature'.
typedVerifySignature
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[BSL.ByteString, Bool])
    => TypedBuiltinName term '[BSL.ByteString, BSL.ByteString, BSL.ByteString] (EvaluationResult Bool)
typedVerifySignature = makeTypedBuiltinName VerifySignature

-- | Typed 'EqByteString'.
typedEqByteString
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[BSL.ByteString, Bool])
    => TypedBuiltinName term '[BSL.ByteString, BSL.ByteString] Bool
typedEqByteString = makeTypedBuiltinName EqByteString

-- | Typed 'LtByteString'.
typedLtByteString
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[BSL.ByteString, Bool])
    => TypedBuiltinName term '[BSL.ByteString, BSL.ByteString] Bool
typedLtByteString = makeTypedBuiltinName LtByteString

-- | Typed 'GtByteString'.
typedGtByteString
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[BSL.ByteString, Bool])
    => TypedBuiltinName term '[BSL.ByteString, BSL.ByteString] Bool
typedGtByteString = makeTypedBuiltinName GtByteString

-- | Typed 'IfThenElse'.
typedIfThenElse
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[BSL.ByteString, Bool])
    => TypedBuiltinName term '[Bool, Opaque term "a" 0, Opaque term "a" 0] (Opaque term "a" 0)
typedIfThenElse =
    TypedBuiltinName IfThenElse $
        TypeSchemeAllType @"a" @0 Proxy $ \_ -> knownTypeScheme
