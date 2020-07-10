-- | This module defines tools for associating PLC terms with their corresponding
-- Haskell values.

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE TypeOperators             #-}

module Language.PlutusCore.Generators.Internal.Denotation
    ( Denotation(..)
    , DenotationContextMember(..)
    , DenotationContext(..)
    , denoteVariable
    , denoteTypedBuiltinName
    , insertVariable
    , insertTypedBuiltinName
    , typedBuiltinNames
    ) where

import           Language.PlutusCore.Generators.Internal.Dependent

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import qualified Data.ByteString.Lazy                              as BSL
import qualified Data.ByteString.Lazy.Hash                         as Hash
import           Data.Coerce
import           Data.Dependent.Map                                (DMap)
import qualified Data.Dependent.Map                                as DMap
import           Data.Functor.Compose
import           Data.Proxy

-- | Haskell denotation of a PLC object. An object can be a 'BuiltinName' or a variable for example.
data Denotation uni object res = forall args. Denotation
    { _denotationObject :: object
      -- ^ A PLC object.
    , _denotationToTerm :: object -> Term TyName Name uni ()
      -- ^ How to embed the object into a term.
    , _denotationItself :: FoldArgs args res
      -- ^ The denotation of the object. E.g. the denotation of 'AddInteger' is '(+)'.
    , _denotationScheme :: TypeScheme (Term TyName Name uni ()) args res
      -- ^ The 'TypeScheme' of the object. See 'intIntInt' for example.
    }

-- | A member of a 'DenotationContext'.
-- @object@ is existentially quantified, so the only thing that can be done with it,
-- is turning it into a 'Term' using '_denotationToTerm'.
data DenotationContextMember uni res =
    forall object. DenotationContextMember (Denotation uni object res)

-- | A context of 'DenotationContextMember's.
-- Each row is a mapping from a type to a list of things that can return that type.
-- For example it can contain a mapping from @integer@ to
--   1. a bound variable of type @integer@
--   2. a bound variable of functional type with the result being @integer@
--   3. the 'AddInteger' 'BuiltinName' or any other 'BuiltinName' which returns an @integer@.
newtype DenotationContext uni = DenotationContext
    { unDenotationContext :: DMap (AsKnownType uni) (Compose [] (DenotationContextMember uni))
    }

-- Here the only search that we need to perform is the search for things that return an appropriate
-- @r@, be them variables or functions. Better if we also take types of arguments into account,
-- but it is not required as we can always generate an argument out of thin air in a rank-0 setting
-- (without @Void@).

-- | The resulting type of a 'TypeScheme'.
typeSchemeResult :: TypeScheme (Term TyName Name uni ()) args res -> AsKnownType uni res
typeSchemeResult (TypeSchemeResult _)       = AsKnownType
typeSchemeResult (TypeSchemeArrow _ schB)   = typeSchemeResult schB
typeSchemeResult (TypeSchemeAllType _ schK) = typeSchemeResult $ schK Proxy

-- | Get the 'Denotation' of a variable.
denoteVariable :: KnownType (Term TyName Name uni ()) res => Name -> res -> Denotation uni Name res
denoteVariable name meta = Denotation name (Var ()) meta (TypeSchemeResult Proxy)

-- | Get the 'Denotation' of a 'TypedBuiltinName'.
denoteTypedBuiltinName
    :: TypedBuiltinName (Term TyName Name uni ()) args res
    -> FoldArgs args res
    -> Denotation uni BuiltinName res
denoteTypedBuiltinName (TypedBuiltinName name scheme) meta =
    Denotation name (Builtin () . BuiltinName ()) meta scheme

-- | Insert the 'Denotation' of an object into a 'DenotationContext'.
insertDenotation
    :: (GShow uni, KnownType (Term TyName Name uni ()) res)
    => Denotation uni object res -> DenotationContext uni -> DenotationContext uni
insertDenotation denotation (DenotationContext vs) = DenotationContext $
    DMap.insertWith'
        (\(Compose xs) (Compose ys) -> Compose $ xs ++ ys)
        AsKnownType
        (Compose [DenotationContextMember denotation])
        vs

-- | Insert a variable into a 'DenotationContext'.
insertVariable
    :: (GShow uni, KnownType (Term TyName Name uni ()) a)
    => Name -> a -> DenotationContext uni -> DenotationContext uni
insertVariable name = insertDenotation . denoteVariable name

-- | Insert a 'TypedBuiltinName' into a 'DenotationContext'.
insertTypedBuiltinName
    :: GShow uni
    => TypedBuiltinName (Term TyName Name uni ()) args res
    -> FoldArgs args res
    -> DenotationContext uni
    -> DenotationContext uni
insertTypedBuiltinName tbn@(TypedBuiltinName _ scheme) meta =
    case typeSchemeResult scheme of
        AsKnownType -> insertDenotation (denoteTypedBuiltinName tbn meta)

-- Builtins that may fail are commented out, because we cannot handle them right now.
-- Look for "UNDEFINED BEHAVIOR" in "Language.PlutusCore.Generators.Internal.Dependent".
-- | A 'DenotationContext' that consists of 'TypedBuiltinName's.
typedBuiltinNames
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => DenotationContext uni
typedBuiltinNames
    = insertTypedBuiltinName typedAddInteger           (+)
    . insertTypedBuiltinName typedSubtractInteger      (-)
    . insertTypedBuiltinName typedMultiplyInteger      (*)
--     . insertTypedBuiltinName typedDivideInteger        (nonZeroArg div)
--     . insertTypedBuiltinName typedRemainderInteger     (nonZeroArg rem)
--     . insertTypedBuiltinName typedQuotientInteger      (nonZeroArg quot)
--     . insertTypedBuiltinName typedModInteger           (nonZeroArg mod)
    . insertTypedBuiltinName typedLessThanInteger      (<)
    . insertTypedBuiltinName typedLessThanEqInteger    (<=)
    . insertTypedBuiltinName typedGreaterThanInteger   (>)
    . insertTypedBuiltinName typedGreaterThanEqInteger (>=)
    . insertTypedBuiltinName typedEqInteger            (==)
    . insertTypedBuiltinName typedConcatenate          (coerce BSL.append)
    . insertTypedBuiltinName typedTakeByteString       (coerce BSL.take . integerToInt64)
    . insertTypedBuiltinName typedDropByteString       (coerce BSL.drop . integerToInt64)
    . insertTypedBuiltinName typedSHA2                 (coerce Hash.sha2)
    . insertTypedBuiltinName typedSHA3                 (coerce Hash.sha3)
--     . insertTypedBuiltinName typedVerifySignature      verifySignature
    . insertTypedBuiltinName typedEqByteString         (==)
    $ DenotationContext mempty
