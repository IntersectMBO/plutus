-- | This module defines tools for associating PLC terms with their corresponding
-- Haskell values.

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
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

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import qualified Data.ByteString.Lazy         as BSL
import           Data.Dependent.Map           (DMap)
import qualified Data.Dependent.Map           as DMap
import           Data.Functor.Compose

-- | Haskell denotation of a PLC object. An object can be a 'BuiltinName' or a variable for example.
data Denotation object size r = forall a. Denotation
    { _denotationObject :: object                         -- ^ A PLC object.
    , _denotationToTerm :: object -> Term TyName Name ()  -- ^ How to embed the object into a term.
    , _denotationItself :: a                              -- ^ The denotation of the object.
                                                          -- E.g. the denotation of 'AddInteger' is '(+)'.
    , _denotationScheme :: TypeScheme size a r            -- ^ The 'TypeScheme' of the object.
                                                          -- See 'sizeIntIntInt' for example.
    }

-- | A member of a 'DenotationContext'.
-- @object@ is existentially quantified, so the only thing that can be done with it,
-- is turning it into a 'Term' using '_denotationToTerm'.
data DenotationContextMember r =
    forall object. DenotationContextMember (Denotation object Size r)

-- | A context of 'DenotationContextMember's.
-- Each row is a mapping from a type to a list of things that can return that type.
-- For example it can contain a mapping from @integer@ to
--   1. a bound variable of type @integer@
--   2. a bound variable of functional type with the result being @integer@
--   3. the 'AddInteger' 'BuiltinName' or any other 'BuiltinName' which returns an @integer@.
newtype DenotationContext = DenotationContext
    { unDenotationContext :: DMap (TypedBuiltin ()) (Compose [] DenotationContextMember)
    }

-- Here the only search that we need to perform is the search for things that return an appropriate @r@,
-- be them variables or functions. Better if we also take types of arguments into account, but it is
-- not required as we can always generate an argument out of thin air in a rank-0 setting (without @Void@).

-- | Get the 'Denotation' of a variable.
denoteVariable :: Name () -> TypedBuiltin size r -> r -> Denotation (Name ()) size r
denoteVariable name tb meta = Denotation name (Var ()) meta (TypeSchemeBuiltin tb)

-- | Get the 'Denotation' of a 'TypedBuiltinName'.
denoteTypedBuiltinName :: TypedBuiltinName a r -> a -> Denotation BuiltinName size r
denoteTypedBuiltinName (TypedBuiltinName name scheme) meta =
    Denotation name (Builtin () . BuiltinName ()) meta scheme

-- | Insert the 'Denotation' of an object into a 'DenotationContext'.
insertDenotation :: TypedBuiltin () r -> Denotation object Size r -> DenotationContext -> DenotationContext
insertDenotation tb denotation (DenotationContext vs) = DenotationContext $
    DMap.insertWith'
        (\(Compose xs) (Compose ys) -> Compose $ xs ++ ys)
        tb
        (Compose [DenotationContextMember denotation])
        vs

-- | Insert a variable into a 'DenotationContext'.
insertVariable :: Name () -> TypedBuiltin Size a -> a -> DenotationContext -> DenotationContext
insertVariable name tb meta =
    insertDenotation (closeTypedBuiltin tb) (denoteVariable name tb meta)

-- | Insert a 'TypedBuiltinName' into a 'DenotationContext'.
insertTypedBuiltinName :: TypedBuiltinName a r -> a -> DenotationContext -> DenotationContext
insertTypedBuiltinName tbn@(TypedBuiltinName _ scheme) meta =
    insertDenotation (typeSchemeResult scheme) (denoteTypedBuiltinName tbn meta)

-- | A 'DenotationContext' that consists of 'TypedBuiltinName's.
typedBuiltinNames :: DenotationContext
typedBuiltinNames
    = insertTypedBuiltinName typedAddInteger           (+)
    . insertTypedBuiltinName typedSubtractInteger      (-)
    . insertTypedBuiltinName typedMultiplyInteger      (*)
    . insertTypedBuiltinName typedDivideInteger        div
    . insertTypedBuiltinName typedRemainderInteger     rem
    . insertTypedBuiltinName typedQuotientInteger      quot
    . insertTypedBuiltinName typedModInteger           mod
    . insertTypedBuiltinName typedLessThanInteger      (<)
    . insertTypedBuiltinName typedLessThanEqInteger    (<=)
    . insertTypedBuiltinName typedGreaterThanInteger   (>)
    . insertTypedBuiltinName typedGreaterThanEqInteger (>=)
    . insertTypedBuiltinName typedEqInteger            (==)
    . insertTypedBuiltinName typedResizeInteger        (const id)
--     . insertTypedBuiltinName typedIntToByteString      undefined
    . insertTypedBuiltinName typedConcatenate          (<>)
    . insertTypedBuiltinName typedTakeByteString       (BSL.take . fromIntegral)
    . insertTypedBuiltinName typedDropByteString       (BSL.drop . fromIntegral)
--     . insertTypedBuiltinName typedSHA2                 undefined
--     . insertTypedBuiltinName typedSHA3                 undefined
--     . insertTypedBuiltinName typedVerifySignature      undefined
    . insertTypedBuiltinName typedResizeByteString     (const id)
    . insertTypedBuiltinName typedEqByteString         (==)
--     . insertTypedBuiltinName typedTxHash               undefined
--     . insertTypedBuiltinName typedBlockNum             undefined
--     . insertTypedBuiltinName typedSizeOfInteger        sizeOfInteger
    $ DenotationContext mempty
