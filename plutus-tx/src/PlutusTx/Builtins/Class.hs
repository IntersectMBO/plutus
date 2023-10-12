-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusTx.Builtins.Class where

import Data.ByteString (ByteString)
import PlutusTx.Builtins.Internal

import Data.String (IsString (..))
import Data.Text (Text, pack)

import GHC.Magic qualified as Magic
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1 (Element)
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2 (Element)
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing (MlResult)
import PlutusTx.Base (const, id, ($))
import PlutusTx.Bool (Bool (..))
import PlutusTx.Integer (Integer)
import Prelude qualified as Haskell (String)

-- See Note [Builtin types and their Haskell versions]
{-|
A class witnessing the ability to convert from the builtin representation to the Haskell representation.
-}
class FromBuiltin arep a | arep -> a where
    fromBuiltin :: arep -> a

-- See Note [Builtin types and their Haskell versions]
{-|
A class witnessing the ability to convert from the Haskell representation to the builtin representation.
-}
class ToBuiltin a arep | a -> arep where
    toBuiltin :: a -> arep

instance FromBuiltin BuiltinInteger Integer where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = id
instance ToBuiltin Integer BuiltinInteger where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = id

instance FromBuiltin BuiltinBool Bool where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin b = ifThenElse b True False
instance ToBuiltin Bool BuiltinBool where
    {-# INLINABLE toBuiltin #-}
    toBuiltin b = if b then true else false

instance FromBuiltin BuiltinUnit () where
    -- See Note [Strict conversions to/from unit]
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin u = chooseUnit u ()
instance ToBuiltin () BuiltinUnit where
    -- See Note [Strict conversions to/from unit]
    {-# INLINABLE toBuiltin #-}
    toBuiltin x = case x of () -> unitval

instance FromBuiltin BuiltinByteString ByteString where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinByteString b) = b
instance ToBuiltin ByteString BuiltinByteString where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinByteString

-- We can't put this in `Builtins.hs`, since that force `O0` deliberately, which prevents
-- the unfoldings from going in. So we just stick it here. Fiddly.
instance IsString BuiltinString where
    -- Try and make sure the dictionary selector goes away, it's simpler to match on
    -- the application of 'stringToBuiltinString'
    {-# INLINE fromString #-}
    -- See Note [noinline hack]
    fromString = Magic.noinline stringToBuiltinString

{-# INLINABLE stringToBuiltinString #-}
stringToBuiltinString :: Haskell.String -> BuiltinString
-- To explain why the obfuscatedId is here
-- See Note [noinline hack]
stringToBuiltinString str = obfuscatedId (BuiltinString $ pack str)

{-# NOINLINE obfuscatedId #-}
obfuscatedId :: a -> a
obfuscatedId a = a

instance FromBuiltin BuiltinString Text where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinString t) = t
instance ToBuiltin Text BuiltinString where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinString

{- Same noinline hack as with `String` type. -}
instance IsString BuiltinByteString where
    -- Try and make sure the dictionary selector goes away, it's simpler to match on
    -- the application of 'stringToBuiltinByteString'
    {-# INLINE fromString #-}
    -- See Note [noinline hack]
    fromString = Magic.noinline stringToBuiltinByteString

{-# INLINABLE stringToBuiltinByteString #-}
stringToBuiltinByteString :: Haskell.String -> BuiltinByteString
stringToBuiltinByteString str = encodeUtf8 $ stringToBuiltinString str

instance (FromBuiltin arep a, FromBuiltin brep b) => FromBuiltin (BuiltinPair arep brep) (a,b) where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin p = (fromBuiltin $ fst p, fromBuiltin $ snd p)
instance ToBuiltin (BuiltinData, BuiltinData) (BuiltinPair BuiltinData BuiltinData) where
    {-# INLINABLE toBuiltin #-}
    toBuiltin (d1, d2) = mkPairData d1 d2

instance FromBuiltin arep a => FromBuiltin (BuiltinList arep) [a] where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = go
      where
          -- The combination of both INLINABLE and a type signature seems to stop this getting lifted to the top
          -- level, which means it gets a proper unfolding, which means that specialization can work, which can
          -- actually help quite a bit here.
          {-# INLINABLE go #-}
          go :: BuiltinList arep -> [a]
          -- Note that we are using builtin chooseList here so this is *strict* application! So we need to do
          -- the manual laziness ourselves.
          go l = chooseList l (const []) (\_ -> fromBuiltin (head l):go (tail l)) unitval

instance ToBuiltin [BuiltinData] (BuiltinList BuiltinData) where
    {-# INLINABLE toBuiltin #-}
    toBuiltin []     = mkNilData unitval
    toBuiltin (d:ds) = mkCons d (toBuiltin ds)

instance ToBuiltin [(BuiltinData, BuiltinData)] (BuiltinList (BuiltinPair BuiltinData BuiltinData)) where
    {-# INLINABLE toBuiltin #-}
    toBuiltin []     = mkNilPairData unitval
    toBuiltin (d:ds) = mkCons (toBuiltin d) (toBuiltin ds)

instance FromBuiltin BuiltinData BuiltinData where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = id
instance ToBuiltin BuiltinData BuiltinData where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = id

instance FromBuiltin BuiltinBLS12_381_G1_Element BLS12_381.G1.Element where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinBLS12_381_G1_Element a) = a
instance ToBuiltin BLS12_381.G1.Element BuiltinBLS12_381_G1_Element where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinBLS12_381_G1_Element

instance FromBuiltin BuiltinBLS12_381_G2_Element BLS12_381.G2.Element where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinBLS12_381_G2_Element a) = a
instance ToBuiltin BLS12_381.G2.Element BuiltinBLS12_381_G2_Element where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinBLS12_381_G2_Element

instance FromBuiltin BuiltinBLS12_381_MlResult BLS12_381.Pairing.MlResult where
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinBLS12_381_MlResult a) = a
instance ToBuiltin BLS12_381.Pairing.MlResult BuiltinBLS12_381_MlResult where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinBLS12_381_MlResult

{- Note [Builtin types and their Haskell versions]
Consider the bulitin pair type. In Plutus Tx, we have an (opaque) type for
this. It's opaque because you can't actually pattern match on it, instead you can
only in fact use the specific functions that are available as builtins.

We _also_ have the normal Haskell pair type. This is very different: you can
pattern match on it, and you can use whatever user-defined functions you like on it.

Users would really like to use the latter, and not the former. So we often want
to _wrap_ our builtin functions with little adapters that convert between the
"opaque builtin" "version" of a type and the "normal Haskell" "version" of a type.

This is what the ToBuiltin and FromBuiltin classes do. They let us write wrappers
for builtins relatively consistently by just calling toBuiltin on their arguments
and fromBuiltin on the result. They shouldn't really be used otherwise.

To keep the consistency we define dummy instances that are just the identity function
for types that don't have a separate "normall Haskell" version. For example:
integer. Integer in Plutus Tx user code _is_ the opaque builtin type, we don't
expose a different one. Essentially: if it's a datatype then there's a substantive
conversion.
-}

{- Note [Fundeps versus type families in To/FromBuiltin]
We could use a type family here to get the builtin representation of a type. After all, it's
entirely determined by the Haskell type.

However, this is harder for the plugin to deal with. It's okay to have a type variable
for the representation type that needs to be instantiated later, but it's *not* okay to
have an irreducible type application on a type variable. So fundeps are much nicer here.
-}

{- Note [Strict conversions to/from unit]
Converting to/from unit *should* be straightforward: just ``const ()`.`
*But* GHC is very good at optimizing this, and we sometimes use unit
where side effects matter, e.g. as the result of `trace`. So GHC will
tend to turn `fromBuiltin (trace s)` into `()`, which is wrong.

So we want our conversions to/from unit to be strict in Haskell. This
means we need to case pointlessly on the argument, which means we need
case on unit (`chooseUnit`) as a builtin. But then it all works okay.
-}

{- Note [noinline hack]
For some functions we have two conflicting desires:
- We want to have the unfolding available for the plugin.
- We don't want the function to *actually* get inlined before the plugin runs, since we rely
on being able to see the original function for some reason.

'INLINABLE' achieves the first, but may cause the function to be inlined too soon.

We can solve this at specific call sites by using the 'noinline' magic function from
GHC. This stops GHC from inlining it. As a bonus, it also won't be inlined if
that function is compiled later into the body of another function.

We do therefore need to handle 'noinline' in the plugin, as it itself does not have
an unfolding.

Another annoying quirk: even if you have 'noinline'd a function call, if the body is
a single variable, it will still inline! This is the case for the obvious definition
of 'stringToBuiltinString' (since the newtype constructor vanishes), so we have to add
some obfuscation to the body to prevent it inlining.
-}

{- Note [From/ToBuiltin instances for polymorphic builtin types]
For various technical reasons
(see Note [Representable built-in functions over polymorphic built-in types])
it's not always easy to provide polymorphic constructors for builtin types, but
we can usually provide destructors.

What this means in practice is that we can write a generic FromBuiltin instance
for pairs that makes use of polymorphic fst/snd builtins, but we can't write
a polymorphic ToBuiltin instance because we'd need a polymorphic version of (,).

Instead we write monomorphic instances corresponding to monomorphic constructor
builtins that we add for specific purposes.
-}
