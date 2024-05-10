{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies             #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Builtins.IsBuiltin where

import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1 (Element)
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2 (Element)
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing (MlResult)
import PlutusCore.Data (Data)
import PlutusTx.Base (id, ($))
import PlutusTx.Bool (Bool (..))
import PlutusTx.Builtins.Internal
import PlutusTx.Integer (Integer)

import Data.ByteString (ByteString)
import Data.Kind qualified as GHC
import Data.String (IsString (..))
import Data.Text (Text, pack)
import GHC.Magic qualified as Magic
import Prelude qualified as Haskell (String)

obfuscatedId :: a -> a
obfuscatedId a = a
{-# NOINLINE obfuscatedId #-}

stringToBuiltinByteString :: Haskell.String -> BuiltinByteString
stringToBuiltinByteString str = encodeUtf8 $ stringToBuiltinString str
{-# INLINABLE stringToBuiltinByteString #-}

stringToBuiltinString :: Haskell.String -> BuiltinString
-- To explain why the obfuscatedId is here
-- See Note [noinline hack]
stringToBuiltinString str = obfuscatedId (BuiltinString $ pack str)
{-# INLINABLE stringToBuiltinString #-}

{- Same noinline hack as with `String` type. -}
instance IsString BuiltinByteString where
    -- Try and make sure the dictionary selector goes away, it's simpler to match on
    -- the application of 'stringToBuiltinByteString'
    -- See Note [noinline hack]
    {-# INLINE fromString #-}
    fromString = Magic.noinline stringToBuiltinByteString

-- We can't put this in `Builtins.hs`, since that force `O0` deliberately, which prevents
-- the unfoldings from going in. So we just stick it here. Fiddly.
instance IsString BuiltinString where
    -- Try and make sure the dictionary selector goes away, it's simpler to match on
    -- the application of 'stringToBuiltinString'
    -- See Note [noinline hack]
    {-# INLINE fromString #-}
    fromString = Magic.noinline stringToBuiltinString

type HasFromBuiltin :: GHC.Type -> GHC.Constraint
class HasFromBuiltin a where
    type FromBuiltin a
    fromBuiltin :: a -> FromBuiltin a

type HasToBuiltin :: GHC.Type -> GHC.Constraint
class HasToBuiltin a where
    toBuiltin :: FromBuiltin a -> a

instance HasFromBuiltin BuiltinInteger where
    type FromBuiltin BuiltinInteger = Integer
    fromBuiltin = id
    {-# INLINABLE fromBuiltin #-}
instance HasToBuiltin BuiltinInteger where
    toBuiltin = id
    {-# INLINABLE toBuiltin #-}

instance HasFromBuiltin BuiltinByteString where
    type FromBuiltin BuiltinByteString = ByteString
    fromBuiltin (BuiltinByteString b) = b
    {-# INLINABLE fromBuiltin #-}
instance HasToBuiltin BuiltinByteString where
    toBuiltin = BuiltinByteString
    {-# INLINABLE toBuiltin #-}

instance HasFromBuiltin BuiltinString where
    type FromBuiltin BuiltinString = Text
    fromBuiltin (BuiltinString t) = t
    {-# INLINABLE fromBuiltin #-}
instance HasToBuiltin BuiltinString where
    toBuiltin = BuiltinString
    {-# INLINABLE toBuiltin #-}

instance HasFromBuiltin BuiltinUnit where
    type FromBuiltin BuiltinUnit = ()
    fromBuiltin u = chooseUnit u ()
    {-# INLINABLE fromBuiltin #-}
instance HasToBuiltin BuiltinUnit where
    toBuiltin x = case x of () -> unitval
    {-# INLINABLE toBuiltin #-}

instance HasFromBuiltin BuiltinBool where
    type FromBuiltin BuiltinBool = Bool
    fromBuiltin b = ifThenElse b True False
    {-# INLINABLE fromBuiltin #-}
instance HasToBuiltin BuiltinBool where
    toBuiltin b = if b then true else false
    {-# INLINABLE toBuiltin #-}

instance HasFromBuiltin a => HasFromBuiltin (BuiltinList a) where
    type FromBuiltin (BuiltinList a) = [FromBuiltin a]

    fromBuiltin = go
      where
          -- The combination of both INLINABLE and a type signature seems to stop this getting
          -- lifted to the top level, which means it gets a proper unfolding, which means that
          -- specialization can work, which can actually help quite a bit here.
          go :: BuiltinList a -> [FromBuiltin a]
          -- Note that we are using builtin chooseList here so this is *strict* application! So we
          -- need to do the manual laziness ourselves.
          go l = chooseList l (\_ -> []) (\_ -> fromBuiltin (head l) : go (tail l)) unitval
          {-# INLINABLE go #-}
    {-# INLINABLE fromBuiltin #-}

instance HasToBuiltin (BuiltinList BuiltinData) where
    toBuiltin = goList where
        goList :: [Data] -> BuiltinList BuiltinData
        goList []     = mkNilData unitval
        goList (d:ds) = mkCons (toBuiltin d) (goList ds)
    {-# INLINE toBuiltin #-}

instance HasToBuiltin (BuiltinList (BuiltinPair BuiltinData BuiltinData)) where
    toBuiltin = goList where
        goList :: [(Data, Data)] -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
        goList []     = mkNilPairData unitval
        goList (d:ds) = mkCons (toBuiltin d) (goList ds)
    {-# INLINE toBuiltin #-}

instance (HasFromBuiltin a, HasFromBuiltin b) => HasFromBuiltin (BuiltinPair a b) where
    type FromBuiltin (BuiltinPair a b) = (FromBuiltin a, FromBuiltin b)
    fromBuiltin p = (fromBuiltin $ fst p, fromBuiltin $ snd p)
    {-# INLINABLE fromBuiltin #-}
instance HasToBuiltin (BuiltinPair BuiltinData BuiltinData) where
    toBuiltin (d1, d2) = mkPairData (toBuiltin d1) (toBuiltin d2)
    {-# INLINABLE toBuiltin #-}

instance HasFromBuiltin BuiltinData where
    type FromBuiltin BuiltinData = Data
    fromBuiltin (BuiltinData t) = t
    {-# INLINABLE fromBuiltin #-}
instance HasToBuiltin BuiltinData where
    toBuiltin = BuiltinData
    {-# INLINABLE toBuiltin #-}

instance HasFromBuiltin BuiltinBLS12_381_G1_Element where
    type FromBuiltin BuiltinBLS12_381_G1_Element = BLS12_381.G1.Element
    fromBuiltin (BuiltinBLS12_381_G1_Element a) = a
    {-# INLINABLE fromBuiltin #-}
instance HasToBuiltin BuiltinBLS12_381_G1_Element where
    toBuiltin = BuiltinBLS12_381_G1_Element
    {-# INLINABLE toBuiltin #-}

instance HasFromBuiltin BuiltinBLS12_381_G2_Element where
    type FromBuiltin BuiltinBLS12_381_G2_Element = BLS12_381.G2.Element
    fromBuiltin (BuiltinBLS12_381_G2_Element a) = a
    {-# INLINABLE fromBuiltin #-}
instance HasToBuiltin BuiltinBLS12_381_G2_Element where
    toBuiltin = BuiltinBLS12_381_G2_Element
    {-# INLINABLE toBuiltin #-}

instance HasFromBuiltin BuiltinBLS12_381_MlResult where
    type FromBuiltin BuiltinBLS12_381_MlResult = BLS12_381.Pairing.MlResult
    fromBuiltin (BuiltinBLS12_381_MlResult a) = a
    {-# INLINABLE fromBuiltin #-}
instance HasToBuiltin BuiltinBLS12_381_MlResult where
    toBuiltin = BuiltinBLS12_381_MlResult
    {-# INLINABLE toBuiltin #-}

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
