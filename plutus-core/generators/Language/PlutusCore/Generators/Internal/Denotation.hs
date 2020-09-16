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
    , denoteTypedStaticBuiltinName
    , insertVariable
    , insertTypedStaticBuiltinName
    , typedBuiltinNames
    ) where

import           Language.PlutusCore.Generators.Internal.Dependent

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc                         (staticBuiltinNameAsTerm)
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
data Denotation term object res = forall args. Denotation
    { _denotationObject :: object
      -- ^ A PLC object.
    , _denotationToTerm :: object -> term
      -- ^ How to embed the object into a term.
    , _denotationItself :: FoldArgs args res
      -- ^ The denotation of the object. E.g. the denotation of 'AddInteger' is '(+)'.
    , _denotationScheme :: TypeScheme term args res
      -- ^ The 'TypeScheme' of the object. See 'intIntInt' for example.
    }

-- | A member of a 'DenotationContext'.
-- @object@ is existentially quantified, so the only thing that can be done with it,
-- is turning it into a 'Term' using '_denotationToTerm'.
data DenotationContextMember term res =
    forall object. DenotationContextMember (Denotation term object res)

-- | A context of 'DenotationContextMember's.
-- Each row is a mapping from a type to a list of things that can return that type.
-- For example it can contain a mapping from @integer@ to
--   1. a bound variable of type @integer@
--   2. a bound variable of functional type with the result being @integer@
--   3. the 'AddInteger' 'BuiltinName' or any other 'BuiltinName' which returns an @integer@.
newtype DenotationContext term = DenotationContext
    { unDenotationContext :: DMap (AsKnownType term) (Compose [] (DenotationContextMember term))
    }

-- Here the only search that we need to perform is the search for things that return an appropriate
-- @r@, be them variables or functions. Better if we also take types of arguments into account,
-- but it is not required as we can always generate an argument out of thin air in a rank-0 setting
-- (without @Void@).

-- | The resulting type of a 'TypeScheme'.
typeSchemeResult :: TypeScheme term args res -> AsKnownType term res
typeSchemeResult (TypeSchemeResult _)     = AsKnownType
typeSchemeResult (TypeSchemeArrow _ schB) = typeSchemeResult schB
typeSchemeResult (TypeSchemeAll _ _ schK) = typeSchemeResult $ schK Proxy

-- | Get the 'Denotation' of a variable.
denoteVariable
    :: KnownType (Term TyName Name uni fun ()) res
    => Name -> res -> Denotation (Term TyName Name uni fun ()) Name res
denoteVariable name meta = Denotation name (Var ()) meta (TypeSchemeResult Proxy)

-- | Get the 'Denotation' of a 'TypedStaticBuiltinName'.
denoteTypedStaticBuiltinName
    :: TypedStaticBuiltinName term args res
    -> (StaticBuiltinName -> term)
    -> FoldArgs args res
    -> Denotation term StaticBuiltinName res
denoteTypedStaticBuiltinName (TypedStaticBuiltinName name scheme) embed meta =
    Denotation name embed meta scheme

-- | Insert the 'Denotation' of an object into a 'DenotationContext'.
insertDenotation
    :: (GShow (UniOf term), KnownType term res)
    => Denotation term object res -> DenotationContext term -> DenotationContext term
insertDenotation denotation (DenotationContext vs) = DenotationContext $
    DMap.insertWith'
        (\(Compose xs) (Compose ys) -> Compose $ xs ++ ys)
        AsKnownType
        (Compose [DenotationContextMember denotation])
        vs

-- | Insert a variable into a 'DenotationContext'.
insertVariable
    :: (GShow uni, KnownType (Term TyName Name uni fun ()) a)
    => Name
    -> a
    -> DenotationContext (Term TyName Name uni fun ())
    -> DenotationContext (Term TyName Name uni fun ())
insertVariable name = insertDenotation . denoteVariable name

-- | Insert a 'TypedBuiltinName' into a 'DenotationContext'.
insertTypedStaticBuiltinName
    :: GShow uni
    => TypedStaticBuiltinName (Term TyName Name uni fun ()) args res
    -> FoldArgs args res
    -> DenotationContext (Term TyName Name uni fun ())
    -> DenotationContext (Term TyName Name uni fun ())
insertTypedStaticBuiltinName tbn@(TypedStaticBuiltinName _ scheme) meta =
    case typeSchemeResult scheme of
        AsKnownType ->
            insertDenotation $ denoteTypedStaticBuiltinName tbn staticBuiltinNameAsTerm meta

-- Builtins that may fail are commented out, because we cannot handle them right now.
-- Look for "UNDEFINED BEHAVIOR" in "Language.PlutusCore.Generators.Internal.Dependent".
-- | A 'DenotationContext' that consists of 'TypedStaticBuiltinName's.
typedBuiltinNames
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => DenotationContext (Term TyName Name uni fun ())
typedBuiltinNames
    = insertTypedStaticBuiltinName typedAddInteger           (+)
    . insertTypedStaticBuiltinName typedSubtractInteger      (-)
    . insertTypedStaticBuiltinName typedMultiplyInteger      (*)
--     . insertTypedStaticBuiltinName typedDivideInteger        (nonZeroArg div)
--     . insertTypedStaticBuiltinName typedRemainderInteger     (nonZeroArg rem)
--     . insertTypedStaticBuiltinName typedQuotientInteger      (nonZeroArg quot)
--     . insertTypedStaticBuiltinName typedModInteger           (nonZeroArg mod)
    . insertTypedStaticBuiltinName typedLessThanInteger      (<)
    . insertTypedStaticBuiltinName typedLessThanEqInteger    (<=)
    . insertTypedStaticBuiltinName typedGreaterThanInteger   (>)
    . insertTypedStaticBuiltinName typedGreaterThanEqInteger (>=)
    . insertTypedStaticBuiltinName typedEqInteger            (==)
    . insertTypedStaticBuiltinName typedConcatenate          (coerce BSL.append)
    . insertTypedStaticBuiltinName typedTakeByteString       (coerce BSL.take . integerToInt64)
    . insertTypedStaticBuiltinName typedDropByteString       (coerce BSL.drop . integerToInt64)
    . insertTypedStaticBuiltinName typedSHA2                 (coerce Hash.sha2)
    . insertTypedStaticBuiltinName typedSHA3                 (coerce Hash.sha3)
--     . insertTypedStaticBuiltinName typedVerifySignature      verifySignature
    . insertTypedStaticBuiltinName typedEqByteString         (==)
    $ DenotationContext mempty
