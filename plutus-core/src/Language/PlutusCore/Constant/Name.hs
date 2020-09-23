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
    ( makeTypedStaticBuiltinName
    , withTypedStaticBuiltinName
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

import qualified Data.ByteString                       as BS
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
makeTypedStaticBuiltinName :: KnownTypeScheme term args res => StaticBuiltinName -> TypedStaticBuiltinName term args res
makeTypedStaticBuiltinName name = TypedStaticBuiltinName name knownTypeScheme

-- | Apply a continuation to the typed version of a 'BuiltinName'.
withTypedStaticBuiltinName
    :: (HasConstantIn uni term, GShow uni, GEq uni, DefaultUni <: uni)
    => StaticBuiltinName -> (forall args res. TypedStaticBuiltinName term args res -> c) -> c
withTypedStaticBuiltinName AddInteger           k = k typedAddInteger
withTypedStaticBuiltinName SubtractInteger      k = k typedSubtractInteger
withTypedStaticBuiltinName MultiplyInteger      k = k typedMultiplyInteger
withTypedStaticBuiltinName DivideInteger        k = k typedDivideInteger
withTypedStaticBuiltinName QuotientInteger      k = k typedQuotientInteger
withTypedStaticBuiltinName RemainderInteger     k = k typedRemainderInteger
withTypedStaticBuiltinName ModInteger           k = k typedModInteger
withTypedStaticBuiltinName LessThanInteger      k = k typedLessThanInteger
withTypedStaticBuiltinName LessThanEqInteger    k = k typedLessThanEqInteger
withTypedStaticBuiltinName GreaterThanInteger   k = k typedGreaterThanInteger
withTypedStaticBuiltinName GreaterThanEqInteger k = k typedGreaterThanEqInteger
withTypedStaticBuiltinName EqInteger            k = k typedEqInteger
withTypedStaticBuiltinName Concatenate          k = k typedConcatenate
withTypedStaticBuiltinName TakeByteString       k = k typedTakeByteString
withTypedStaticBuiltinName DropByteString       k = k typedDropByteString
withTypedStaticBuiltinName SHA2                 k = k typedSHA2
withTypedStaticBuiltinName SHA3                 k = k typedSHA3
withTypedStaticBuiltinName VerifySignature      k = k typedVerifySignature
withTypedStaticBuiltinName EqByteString         k = k typedEqByteString
withTypedStaticBuiltinName LtByteString         k = k typedLtByteString
withTypedStaticBuiltinName GtByteString         k = k typedGtByteString
withTypedStaticBuiltinName IfThenElse           k = k typedIfThenElse

-- | Typed 'AddInteger'.
typedAddInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedStaticBuiltinName term '[Integer, Integer] Integer
typedAddInteger = makeTypedStaticBuiltinName AddInteger

-- | Typed 'SubtractInteger'.
typedSubtractInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedStaticBuiltinName term '[Integer, Integer] Integer
typedSubtractInteger = makeTypedStaticBuiltinName SubtractInteger

-- | Typed 'MultiplyInteger'.
typedMultiplyInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedStaticBuiltinName term '[Integer, Integer] Integer
typedMultiplyInteger = makeTypedStaticBuiltinName MultiplyInteger

-- | Typed 'DivideInteger'.
typedDivideInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedStaticBuiltinName term '[Integer, Integer] (EvaluationResult Integer)
typedDivideInteger = makeTypedStaticBuiltinName DivideInteger

-- | Typed 'QuotientInteger'
typedQuotientInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedStaticBuiltinName term '[Integer, Integer] (EvaluationResult Integer)
typedQuotientInteger = makeTypedStaticBuiltinName QuotientInteger

-- | Typed 'RemainderInteger'.
typedRemainderInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedStaticBuiltinName term '[Integer, Integer] (EvaluationResult Integer)
typedRemainderInteger = makeTypedStaticBuiltinName RemainderInteger

-- | Typed 'ModInteger'
typedModInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` Integer)
    => TypedStaticBuiltinName term '[Integer, Integer] (EvaluationResult Integer)
typedModInteger = makeTypedStaticBuiltinName ModInteger

-- | Typed 'LessThanInteger'.
typedLessThanInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedStaticBuiltinName term '[Integer, Integer] Bool
typedLessThanInteger = makeTypedStaticBuiltinName LessThanInteger

-- | Typed 'LessThanEqInteger'.
typedLessThanEqInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedStaticBuiltinName term '[Integer, Integer] Bool
typedLessThanEqInteger = makeTypedStaticBuiltinName LessThanEqInteger

-- | Typed 'GreaterThanInteger'.
typedGreaterThanInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedStaticBuiltinName term '[Integer, Integer] Bool
typedGreaterThanInteger = makeTypedStaticBuiltinName GreaterThanInteger

-- | Typed 'GreaterThanEqInteger'.
typedGreaterThanEqInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedStaticBuiltinName term '[Integer, Integer] Bool
typedGreaterThanEqInteger = makeTypedStaticBuiltinName GreaterThanEqInteger

-- | Typed 'EqInteger'.
typedEqInteger
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, Bool])
    => TypedStaticBuiltinName term '[Integer, Integer] Bool
typedEqInteger = makeTypedStaticBuiltinName EqInteger

-- | Typed 'Concatenate'.
typedConcatenate
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` BS.ByteString)
    => TypedStaticBuiltinName term '[BS.ByteString, BS.ByteString] BS.ByteString
typedConcatenate = makeTypedStaticBuiltinName Concatenate

-- | Typed 'TakeByteString'.
typedTakeByteString
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, BS.ByteString])
    => TypedStaticBuiltinName term '[Integer, BS.ByteString] BS.ByteString
typedTakeByteString = makeTypedStaticBuiltinName TakeByteString

-- | Typed 'DropByteString'.
typedDropByteString
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[Integer, BS.ByteString])
    => TypedStaticBuiltinName term '[Integer, BS.ByteString] BS.ByteString
typedDropByteString = makeTypedStaticBuiltinName DropByteString

-- | Typed 'SHA2'.
typedSHA2
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` BS.ByteString)
    => TypedStaticBuiltinName term '[BS.ByteString] BS.ByteString
typedSHA2 = makeTypedStaticBuiltinName SHA2

-- | Typed 'SHA3'.
typedSHA3
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` BS.ByteString)
    => TypedStaticBuiltinName term '[BS.ByteString] BS.ByteString
typedSHA3 = makeTypedStaticBuiltinName SHA3

-- | Typed 'VerifySignature'.
typedVerifySignature
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[BS.ByteString, Bool])
    => TypedStaticBuiltinName term '[BS.ByteString, BS.ByteString, BS.ByteString] (EvaluationResult Bool)
typedVerifySignature = makeTypedStaticBuiltinName VerifySignature

-- | Typed 'EqByteString'.
typedEqByteString
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[BS.ByteString, Bool])
    => TypedStaticBuiltinName term '[BS.ByteString, BS.ByteString] Bool
typedEqByteString = makeTypedStaticBuiltinName EqByteString

-- | Typed 'LtByteString'.
typedLtByteString
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[BS.ByteString, Bool])
    => TypedStaticBuiltinName term '[BS.ByteString, BS.ByteString] Bool
typedLtByteString = makeTypedStaticBuiltinName LtByteString

-- | Typed 'GtByteString'.
typedGtByteString
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[BS.ByteString, Bool])
    => TypedStaticBuiltinName term '[BS.ByteString, BS.ByteString] Bool
typedGtByteString = makeTypedStaticBuiltinName GtByteString

-- | Typed 'IfThenElse'.
typedIfThenElse
    :: ( HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[BS.ByteString, Bool]
       , a ~ Opaque term (TyVarRep "a" 0)
       )
    => TypedStaticBuiltinName term '[Bool, a, a] a
typedIfThenElse =
    TypedStaticBuiltinName IfThenElse $
        TypeSchemeAll @"a" @0 Proxy (Type ()) $ \_ -> knownTypeScheme
