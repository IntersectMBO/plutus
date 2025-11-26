{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusTx.Builtins.HasOpaque where

import Control.DeepSeq (NFData (..))
import PlutusCore.Pretty (Pretty (..))
import PlutusTx.Base (id)
import PlutusTx.Bool (Bool (..))
import PlutusTx.Builtins.Internal
  ( BuiltinArray
  , BuiltinBLS12_381_G1_Element
  , BuiltinBLS12_381_G2_Element
  , BuiltinBLS12_381_MlResult
  , BuiltinByteString (..)
  , BuiltinData
  , BuiltinInteger
  , BuiltinList (..)
  , BuiltinPair
  , BuiltinString (..)
  , BuiltinUnit
  , BuiltinValue
  , caseList'
  , casePair
  , chooseUnit
  , mkCons
  , mkPairData
  , unitval
  )

import Codec.Serialise (Serialise)
import Data.ByteArray qualified as BA
import Data.ByteString.Base16 qualified as Base16
import Data.Hashable (Hashable (..))
import Data.Kind qualified as GHC
import Data.String (IsString (..))
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Prelude qualified as Haskell
#if MIN_VERSION_base(4,20,0)
import Prelude (type (~))
#endif

-- plutus-tx-plugin has a special case for this function,
-- replacing its unfolding with something else.
stringToBuiltinByteString :: Haskell.String -> BuiltinByteString
stringToBuiltinByteString str = BuiltinByteString (fromString str)
{-# OPAQUE stringToBuiltinByteString #-}

-- plutus-tx-plugin has a special case for this function,
-- replacing its unfolding with something else.
stringToBuiltinString :: Haskell.String -> BuiltinString
stringToBuiltinString str = BuiltinString (Text.pack str)
{-# OPAQUE stringToBuiltinString #-}

instance IsString BuiltinByteString where
  -- Try and make sure the dictionary selector goes away, it's simpler to match on
  -- the application of 'stringToBuiltinByteString'
  fromString = stringToBuiltinByteString
  {-# INLINE fromString #-}

-- We can't put this in `Builtins.hs`, since that force `O0` deliberately, which prevents
-- the unfoldings from going in. So we just stick it here. Fiddly.
instance IsString BuiltinString where
  -- Try and make sure the dictionary selector goes away, it's simpler to match on
  -- the application of 'stringToBuiltinString'
  fromString = stringToBuiltinString
  {-# INLINE fromString #-}

{- Note [IsString instances and UTF-8 encoded string literals]

GHC Core encodes string literals in UTF-8 by default.
Plugin handles GHC Core expressions representing such literals specially:
in compile type it undoes the UTF-8 encoding when string literal is used to construct
a value of type 'BuiltinByteString' and preserves the UTF-8 encoding to construct 'BuiltinString'.

Sometimes we need to construct 'BuiltinByteString' values preserving the UTF-8 encoding, e.g. when
constructing a 'TokenName' value from a 'BuiltinByteString' value. In such cases we can use
'BuiltinByteStringUtf8' newtype:

  TokenName (unBuiltinByteStringUtf8 "привет")

-}
newtype BuiltinByteStringUtf8 = BuiltinByteStringUtf8
  { unBuiltinByteStringUtf8 :: BuiltinByteString
  }
  deriving newtype
    ( Haskell.Eq
    , Haskell.Ord
    , Haskell.Show
    , Haskell.Semigroup
    , Haskell.Monoid
    , Hashable
    , Serialise
    , NFData
    , BA.ByteArrayAccess
    , BA.ByteArray
    , Pretty
    )

instance IsString BuiltinByteStringUtf8 where
  fromString s = BuiltinByteStringUtf8 (stringToBuiltinByteStringUtf8 s)
  {-# INLINE fromString #-}

-- plutus-tx-plugin has a special case for this function,
-- replacing its unfolding with something else.
stringToBuiltinByteStringUtf8 :: Haskell.String -> BuiltinByteString
stringToBuiltinByteStringUtf8 str = BuiltinByteString (Text.encodeUtf8 (Text.pack str))
{-# OPAQUE stringToBuiltinByteStringUtf8 #-}

newtype BuiltinByteStringHex = BuiltinByteStringHex
  { unBuiltinByteStringHex :: BuiltinByteString
  }
  deriving newtype
    ( Haskell.Eq
    , Haskell.Ord
    , Haskell.Show
    , Haskell.Semigroup
    , Haskell.Monoid
    , Hashable
    , Serialise
    , NFData
    , BA.ByteArrayAccess
    , BA.ByteArray
    , Pretty
    )

instance IsString BuiltinByteStringHex where
  fromString s = BuiltinByteStringHex (stringToBuiltinByteStringHex s)
  {-# INLINE fromString #-}

-- plutus-tx-plugin has a special case for this function,
-- replacing its unfolding with something else.
stringToBuiltinByteStringHex :: Haskell.String -> BuiltinByteString
stringToBuiltinByteStringHex str =
  BuiltinByteString (Base16.decodeLenient (fromString str))
{-# OPAQUE stringToBuiltinByteStringHex #-}

{- Note [Built-in types and their Haskell counterparts]
'HasToBuiltin' allows us to convert a value of a built-in type such as 'ByteString' to its Plutus
Tx counterpart, 'BuiltinByteString' in this case. The idea is the same for all built-in types: just
take the Haskell version and make it the Plutus Tx one.

'HasToOpaque' is different, we use it for converting values of only those built-in types that exist
in the Plutus Tx realm, within the Plutus Tx realm. I.e. we cannot convert a 'ByteString', since
'ByteString's don't exist in Plutus Tx, only 'BuiltinByteString's do.

Consider, say, the built-in pair type. In Plutus Tx, we have an (opaque) type for this. It's opaque
because you can't actually pattern match on it, instead you can only in fact use the specific
functions that are available as builtins.

We _also_ have the normal Haskell pair type. This is very different: you can pattern match on it,
and you can use whatever user-defined functions you like on it.

Users would really like to use the latter, and not the former. So we often want to _wrap_ our
built-in functions with little adapters that convert between the opaque "version" of a
type and the "normal Haskell" "version" of a type.

This is what the 'HasToOpaque' and 'HasFromOpaque' classes do. They let us write wrappers for
builtins relatively consistently by just calling 'toOpaque' on their arguments and 'fromOpaque' on
the result. They shouldn't probably be used otherwise.

Ideally, we would not have instances for types which don't have a different Haskell representation
type, such as 'Integer'. 'Integer' in Plutus Tx user code _is_ the opaque built-in type, we don't
expose a different one. So there's no conversion to do. However, this interacts badly with the
instances for polymorphic built-in types, which also convert the type _inside_ them. (This is
necessary to avoid doing multiple traversals of the type, e.g. we don't want to turn a built-in list
into a Haskell list, and then traverse it again to conver the contents). Then we _need_ instances
for all built-in types, so we provide a @default@ implementation for both 'toOpaque' and
'fromOpaque' that simply returns the argument back and use it for those types that don't require any
conversions.

Summarizing, 'toBuiltin'/'fromBuiltin' should be used to cross the boundary between Plutus Tx and
Haskell, while 'toOpaque'/'fromOpaque' should be used within Plutus Tx to convert values to/from
their @Builtin*@ representation, which we need because neither pattern matching nor standard library
functions are available for values of @Builtin*@ types that we get from built-in functions.
-}

{- Note [HasFromOpaque/HasToOpaque instances for polymorphic builtin types]
For various technical reasons
(see Note [Representable built-in functions over polymorphic built-in types])
it's not always easy to provide polymorphic constructors for built-in types, but we can usually
provide destructors.

What this means in practice is that we can write a generic 'HasFromOpaque' instance for pairs that
makes use of polymorphic @fst@/@snd@ builtins, but we can't write a polymorphic 'ToOpaque' instance
because we'd need a polymorphic version of the '(,)' constructor.

Instead we write monomorphic instances corresponding to monomorphic constructor builtins that we add
for specific purposes.
-}

{- Note [Fundeps versus type families in HasFromOpaque/HasToOpaque]
We could use a type family here to get the builtin representation of a type. After all, it's
entirely determined by the Haskell type.

However, this is harder for the plugin to deal with. It's okay to have a type variable for the
representation type that needs to be instantiated later, but it's *not* okay to have an irreducible
type application on a type variable. So fundeps are much nicer here.
-}

-- See Note [Built-in types and their Haskell counterparts].
-- See Note [HasFromOpaque/HasToOpaque instances for polymorphic builtin types].
-- See Note [Fundeps versus type families in HasFromOpaque/HasToOpaque].

{-| A class for converting values of transparent Haskell-defined built-in types (such as '()',
'Bool', '[]' etc) to their opaque Plutus Tx counterparts. Instances for built-in types that are
not transparent are provided as well, simply as identities, since those types are already opaque. -}
type HasToOpaque :: GHC.Type -> GHC.Type -> GHC.Constraint
class HasToOpaque a arep | a -> arep where
  toOpaque :: a -> arep
  default toOpaque :: a ~ arep => a -> arep
  toOpaque = id
  {-# INLINEABLE toOpaque #-}

-- See Note [Built-in types and their Haskell counterparts].
-- See Note [HasFromOpaque/HasToOpaque instances for polymorphic builtin types].
-- See Note [Fundeps versus type families in HasFromOpaque/HasToOpaque].

{-| A class for converting values of opaque Plutus Tx types to their transparent Haskell-defined
counterparts (a.k.a. pattern-matchable) built-in types (such as '()', 'Bool', '[]' etc). If no
transparent counterpart exists, then the implementation is identity. -}
type HasFromOpaque :: GHC.Type -> GHC.Type -> GHC.Constraint
class HasFromOpaque arep a | arep -> a where
  fromOpaque :: arep -> a
  default fromOpaque :: a ~ arep => arep -> a
  fromOpaque = id
  {-# INLINEABLE fromOpaque #-}

instance HasToOpaque BuiltinInteger BuiltinInteger
instance HasFromOpaque BuiltinInteger BuiltinInteger

instance HasToOpaque BuiltinByteString BuiltinByteString
instance HasFromOpaque BuiltinByteString BuiltinByteString

instance HasToOpaque BuiltinString BuiltinString
instance HasFromOpaque BuiltinString BuiltinString

{- Note [Strict conversions to/from unit]
Converting to/from unit *should* be straightforward: just `const ()`.
\*But* GHC is very good at optimizing this, and we sometimes use unit
where side effects matter, e.g. as the result of `trace`. So GHC will
tend to turn `fromOpaque (trace s)` into `()`, which is wrong.

So we want our conversions to/from unit to be strict in Haskell. This
means we need to case pointlessly on the argument, which means we need
case on unit (`chooseUnit`) as a builtin. But then it all works okay.
-}

-- See Note [Strict conversions to/from unit].
instance HasToOpaque () BuiltinUnit where
  toOpaque x = case x of () -> unitval
  {-# INLINEABLE toOpaque #-}
instance HasFromOpaque BuiltinUnit () where
  fromOpaque u = chooseUnit u ()
  {-# INLINEABLE fromOpaque #-}

instance HasToOpaque Bool Bool
instance HasFromOpaque Bool Bool

{-| The empty list of elements of the given type that gets spotted by the plugin (grep for
'mkNilOpaque' in the plugin code) and replaced by the actual empty list constant for types that
are supported (a subset of built-in types). -}
mkNilOpaque :: BuiltinList a
mkNilOpaque = BuiltinList []
{-# OPAQUE mkNilOpaque #-}

{-| 'MkNil' class restricts types that can have empty list value of. This is necessary because
UPLC does not have polymorphic empty array value and type of empty array needs to be given explicitly.

Adding a new builtin type to 'MkNil' requires making necessary changes on
'PlutusTx.Compiler.Expr.compileMkNil' as well. -}
class MkNil arep where
  mkNil :: BuiltinList arep
  mkNil = mkNilOpaque
  {-# INLINEABLE mkNil #-}

instance MkNil BuiltinInteger
instance MkNil BuiltinByteString
instance MkNil Bool
instance MkNil BuiltinData
instance MkNil BuiltinValue
instance MkNil BuiltinBLS12_381_G1_Element
instance MkNil BuiltinBLS12_381_G2_Element
instance MkNil a => MkNil (BuiltinList a)
instance MkNil a => MkNil (BuiltinArray a)
instance (MkNil a, MkNil b) => MkNil (BuiltinPair a b)

instance (HasToOpaque a arep, MkNil arep) => HasToOpaque [a] (BuiltinList arep) where
  toOpaque = goList
    where
      goList :: [a] -> BuiltinList arep
      goList [] = mkNil
      goList (d : ds) = mkCons (toOpaque d) (goList ds)
  {-# INLINEABLE toOpaque #-}
instance HasFromOpaque arep a => HasFromOpaque (BuiltinList arep) [a] where
  fromOpaque = go
    where
      -- The combination of both INLINABLE and a type signature seems to stop this getting
      -- lifted to the top level, which means it gets a proper unfolding, which means that
      -- specialization can work, which can actually help quite a bit here.
      go :: BuiltinList arep -> [a]
      go = caseList' [] (\x xs -> fromOpaque x : go xs)
      {-# INLINEABLE go #-}
  {-# INLINEABLE fromOpaque #-}

instance HasToOpaque (BuiltinData, BuiltinData) (BuiltinPair BuiltinData BuiltinData) where
  toOpaque (d1, d2) = mkPairData (toOpaque d1) (toOpaque d2)
  {-# INLINEABLE toOpaque #-}
instance
  (HasFromOpaque arep a, HasFromOpaque brep b)
  => HasFromOpaque (BuiltinPair arep brep) (a, b)
  where
  fromOpaque p = casePair p (\l r -> (fromOpaque l, fromOpaque r))
  {-# INLINEABLE fromOpaque #-}

instance HasToOpaque BuiltinData BuiltinData
instance HasFromOpaque BuiltinData BuiltinData
instance HasToOpaque BuiltinValue BuiltinValue
instance HasFromOpaque BuiltinValue BuiltinValue

instance HasToOpaque BuiltinBLS12_381_G1_Element BuiltinBLS12_381_G1_Element
instance HasFromOpaque BuiltinBLS12_381_G1_Element BuiltinBLS12_381_G1_Element

instance HasToOpaque BuiltinBLS12_381_G2_Element BuiltinBLS12_381_G2_Element
instance HasFromOpaque BuiltinBLS12_381_G2_Element BuiltinBLS12_381_G2_Element

instance HasToOpaque BuiltinBLS12_381_MlResult BuiltinBLS12_381_MlResult
instance HasFromOpaque BuiltinBLS12_381_MlResult BuiltinBLS12_381_MlResult
