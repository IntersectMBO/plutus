-- | Dynamic built-in types.

{-# LANGUAGE DefaultSignatures #-}

module Language.PlutusCore.Constant.DynamicType
    ( PrettyDynamic (..)
    ) where

import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.Type
import           PlutusPrelude

import qualified Data.ByteString.Lazy.Char8            as BSL

{- Note [Semantics of dynamic built-in types]
We only allow dynamic built-in types that

1. can be represented using static types in PLC. For example Haskell's 'Char' can be represented as
@integer 4@ in PLC. This restriction makes the dynamic built-in types machinery somewhat similar to
type aliases in Haskell (defined via the @type@ keyword). The reason for this restriction is that
storing values of arbitrary types of a host language in the AST of a target language is commonly far
from being trivial, hence we do not support this right now, but we plan to figure out a way to allow
such extensions to the AST
2. are of kind @*@. Dynamic built-in types that are not of kind @*@ can be encoded via recursive
instances. For example:

    instance KnownDynamicBuiltinType dyn => KnownDynamicBuiltinType [dyn] where
        ...

This is due to the fact that we use Haskell classes to assign semantics to dynamic built-in types and
since it's anyway impossible to assign a meaning to an open PLC type, because you'd have to somehow
interpret free variables, we're only interested in closed PLC types and those can be handled by
recursive instances as shown above.

Since type classes are globally coherent by design, we also have global coherence for dynamic built-in
types for free. Any dynamic built-in type means the same thing regardless of the blockchain it's
added to. It may prove to be restrictive, but it's a good property to start with, because less things
can silently stab you in the back.

An @KnownDynamicBuiltinType dyn@ instance provides

1. a way to encode @dyn@ as a PLC type ('getTypeEncoding')
2. a function that encodes values of type @dyn@ as PLC terms ('makeDynamicBuiltin')
3. a function that decodes PLC terms back to Haskell values ('readDynamicBuiltin')

The last two are ought to constitute an isomorphism (modulo 'Quote' and 'Maybe').
-}

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
