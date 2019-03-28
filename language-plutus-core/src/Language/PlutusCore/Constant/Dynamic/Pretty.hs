-- | Dynamic built-in types.

{-# LANGUAGE DefaultSignatures #-}

module Language.PlutusCore.Constant.Dynamic.Pretty
    ( PrettyDynamic (..)
    ) where

import           Language.PlutusCore.Lexer.Type
import           PlutusPrelude

import qualified Data.ByteString.Lazy.Char8     as BSL

-- We probably want to just merge this into the 'KnownDynamicBuiltinType' class.
-- However 'PrettyDynamic' is used in places where 'KnownDynamicBuiltinType' is not used.
-- Which is likely just a bad interaction between old code and new code. That's a TODO.

-- | Same as the 'Pretty' class, but is specifically for dynamic built-in types as their
-- pretty-printing can be rather weird (see the @PrettyDynamic BSL.ByteString@ instance for example).
class PrettyDynamic a where
    prettyDynamic :: a -> Doc ann
    default prettyDynamic :: Pretty a => a -> Doc ann
    prettyDynamic = pretty

instance PrettyDynamic Integer
instance PrettyDynamic BSL.ByteString where prettyDynamic = prettyBytes
instance PrettyDynamic ()
instance PrettyDynamic Bool
instance PrettyDynamic Char
