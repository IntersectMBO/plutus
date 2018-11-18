-- | Dynamic built-in types.

{-# LANGUAGE DefaultSignatures #-}

module Language.PlutusCore.Constant.DynamicType
    ( KnownDynamicBuiltinType (..)
    , PrettyDynamic (..)
    ) where

import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

import qualified Data.ByteString.Lazy.Char8     as BSL

{- Note [Semantics of dynamic built-in types]
We only allow dynamic built-in types that

1. can be represented using static types in PLC. For example Haskell's 'Char' can be represented as
@integer 4@ in PLC. This restriction makes the dynamic built-in types machinery somewhat similar to
the @newtype@ machinery in Haskell. The reason for this restriction is that storing values of arbitrary
types of a host language in the AST of a target language is commonly far from being trivial, hence we
do not support this right now, but we plan to figure out a way to allow such extensions to the AST
2. are of kind @*@. Dynamic built-in types that are not of kind @*@ can be encoded via recursive
instances. For example:

    instance KnownDynamicBuiltinType dyn => KnownDynamicBuiltinType [dyn] where
        ...

This is due to the fact that we use Haskell classes to assign semantics to dynamic built-in types and
since it's anyway impossible to assign a meaning to an open PLC type, because you'd have to somehow
interpret free variables, we're only interested in closed PLC types and those can be handled by
recursive instances as shown above.

Instance resolution is driven by Haskell types rather than names of PLC types.
An alternative design would be something like

    newtype NamedDynamicBuiltinType (dyn :: Symbol) = NamedDynamicBuiltinType
        { unNamedDynamicBuiltinType :: DynamicBuiltinType
        }

    newtype TypedDynamicBuiltinType dyn sem = TypedDynamicBuiltinType
        { unTypedDynamicBuiltinType :: NamedDynamicBuiltinType dyn
        }

    class KnownDynamicBuiltinType dyn sem | dyn -> sem where
        dynamicBuiltinType :: TypedDynamicBuiltinType dyn sem
        makeDynamicBuiltin :: NamedDynamicBuiltinType dyn -> sem -> Maybe (Value TyName Name ())
        readDynamicBuiltin :: NamedDynamicBuiltinType dyn -> Value TyName Name () -> Maybe sem

Here we say that @dyn@, being a type-level string representing the name of a dynamic built-in type,
drives instance resolution and has exactly one possible semantics. This would allow to define,
for example, the 'Any' and 'All' wrappers (see the "Data.Monoid" module) on the PLC side and
interpret both of them as 'Bool' on the Haskell side. We disallow this however, because PLC-side-driven
resolution is more complicated and doesn't seem to give any advantages over the other approach. If you
have newtype wrappers, just interpret them as newtype wrappers on the Haskell side. Nothing fancy here.

And since type classes are globally coherent by design, we also have global coherence for dynamic
built-in types for free. Any dynamic built-in type means the same thing regardless of the blockchain it's
added to. It may prove to be restrictive, but it's a good property to start with, because less things
can silently stab you in the back.
-}

-- See Note [Semantics of dynamic built-in types].
-- | Haskell types known to exist on the PLC side.
class KnownDynamicBuiltinType dyn where
    -- | The name of @dyn@ used on the PLC side.
    dynamicBuiltinType :: proxy dyn -> DynamicBuiltinType

    -- | Convert a Haskell value to the corresponding PLC value.
    -- 'Nothing' represents a conversion failure.
    makeDynamicBuiltin :: dyn -> Maybe (Value TyName Name ())

    -- | Convert a PLC value to the corresponding Haskell value.
    -- 'Nothing' represents a conversion failure.
    readDynamicBuiltin :: Value TyName Name () -> Maybe dyn

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
