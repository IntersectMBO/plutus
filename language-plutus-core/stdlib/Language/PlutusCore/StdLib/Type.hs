-- | This module defines Haskell data types that simplify construction of PLC types and terms.

{-# LANGUAGE RankNTypes #-}
module Language.PlutusCore.StdLib.Type
    ( HoledType(..)
    , RecursiveType(..)
    , holedTyApp
    , holedToRecursive
    ) where

import           Language.PlutusCore.Type

-- | A type with a hole inside. The reason for having such a thing is that 'Wrap'
-- expects the pattern functor of a recursive type while in type signatures we use
-- actual recursive types. So we need a way to construct recursive types such that from
-- any such type we can easily extract its pattern functor as well as easily use the
-- type itself. 'RecursiveType' below allows to do that (except the pattern functor is
-- already supplied to 'Wrap'), but some types are actually type functions that receive
-- arguments and only then return a recursive type (see 'getBuiltinList' for example).
-- Thus we make a type with a hole where the hole can be filled by either 'TyFix' or
-- 'id', so this type, after all arguments are supplied (see 'holedTyApp'), can be
-- converted to the corresponding 'RecursiveType' (see 'holedToRecursive').
-- See "docs/Holed types.md" for more information.
data HoledType tyname a = HoledType
    { _holedTypeName :: tyname a
    , _holedTypeCont :: (Type tyname a -> Type tyname a) -> Type tyname a
    }

-- | A 'Type' that starts with a 'TyFix' (i.e. a recursive type) packaged along with a
-- specified 'Wrap' that allows to construct elements of this type.
data RecursiveType tyname a = RecursiveType
    { _recursiveWrap :: forall name. Term tyname name a -> Term tyname name a
    , _recursiveType :: Type tyname a
    }

-- | Apply a 'HoledType' to a 'Type'.
holedTyApp :: HoledType tyname () -> Type tyname () -> HoledType tyname ()
holedTyApp (HoledType name cont) arg = HoledType name $ \hole -> TyApp () (cont hole) arg

-- | Convert a 'HoledType' to the corresponding 'RecursiveType'.
holedToRecursive :: HoledType tyname () -> RecursiveType tyname ()
holedToRecursive (HoledType name cont) =
    RecursiveType (Wrap () name $ cont id) (cont $ TyFix () name)
