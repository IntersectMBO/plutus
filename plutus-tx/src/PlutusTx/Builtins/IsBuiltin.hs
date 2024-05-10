{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeSynonymInstances     #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

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

{-# NOINLINE obfuscatedId #-}
obfuscatedId :: a -> a
obfuscatedId a = a

{-# INLINABLE stringToBuiltinByteString #-}
stringToBuiltinByteString :: Haskell.String -> BuiltinByteString
stringToBuiltinByteString str = encodeUtf8 $ stringToBuiltinString str

{-# INLINABLE stringToBuiltinString #-}
stringToBuiltinString :: Haskell.String -> BuiltinString
-- To explain why the obfuscatedId is here
-- See Note [noinline hack]
stringToBuiltinString str = obfuscatedId (BuiltinString $ pack str)

{- Same noinline hack as with `String` type. -}
instance IsString BuiltinByteString where
    -- Try and make sure the dictionary selector goes away, it's simpler to match on
    -- the application of 'stringToBuiltinByteString'
    {-# INLINE fromString #-}
    -- See Note [noinline hack]
    fromString = Magic.noinline stringToBuiltinByteString

-- We can't put this in `Builtins.hs`, since that force `O0` deliberately, which prevents
-- the unfoldings from going in. So we just stick it here. Fiddly.
instance IsString BuiltinString where
    -- Try and make sure the dictionary selector goes away, it's simpler to match on
    -- the application of 'stringToBuiltinString'
    {-# INLINE fromString #-}
    -- See Note [noinline hack]
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
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = id
instance HasToBuiltin BuiltinInteger where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = id

instance HasFromBuiltin BuiltinByteString where
    type FromBuiltin BuiltinByteString = ByteString
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinByteString b) = b
instance HasToBuiltin BuiltinByteString where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinByteString

instance HasFromBuiltin BuiltinString where
    type FromBuiltin BuiltinString = Text
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinString t) = t
instance HasToBuiltin BuiltinString where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinString

instance HasFromBuiltin BuiltinUnit where
    type FromBuiltin BuiltinUnit = ()
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin u = chooseUnit u ()
instance HasToBuiltin BuiltinUnit where
    {-# INLINABLE toBuiltin #-}
    toBuiltin x = case x of () -> unitval

instance HasFromBuiltin BuiltinBool where
    type FromBuiltin BuiltinBool = Bool
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin b = ifThenElse b True False
instance HasToBuiltin BuiltinBool where
    {-# INLINABLE toBuiltin #-}
    toBuiltin b = if b then true else false

instance HasFromBuiltin a => HasFromBuiltin (BuiltinList a) where
    type FromBuiltin (BuiltinList a) = [FromBuiltin a]

    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = go
      where
          -- The combination of both INLINABLE and a type signature seems to stop this getting
          -- lifted to the top level, which means it gets a proper unfolding, which means that
          -- specialization can work, which can actually help quite a bit here.
          {-# INLINABLE go #-}
          go :: BuiltinList a -> [FromBuiltin a]
          -- Note that we are using builtin chooseList here so this is *strict* application! So we
          -- need to do the manual laziness ourselves.
          go l = chooseList l (\_ -> []) (\_ -> fromBuiltin (head l) : go (tail l)) unitval

instance HasToBuiltin (BuiltinList BuiltinData) where
    {-# INLINE toBuiltin #-}
    toBuiltin = goList where
        goList :: [Data] -> BuiltinList BuiltinData
        goList []     = mkNilData unitval
        goList (d:ds) = mkCons (toBuiltin d) (goList ds)

instance HasToBuiltin (BuiltinList (BuiltinPair BuiltinData BuiltinData)) where
    {-# INLINE toBuiltin #-}
    toBuiltin = goList where
        goList :: [(Data, Data)] -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
        goList []     = mkNilPairData unitval
        goList (d:ds) = mkCons (toBuiltin d) (goList ds)

instance (HasFromBuiltin a, HasFromBuiltin b) => HasFromBuiltin (BuiltinPair a b) where
    type FromBuiltin (BuiltinPair a b) = (FromBuiltin a, FromBuiltin b)
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin p = (fromBuiltin $ fst p, fromBuiltin $ snd p)
instance HasToBuiltin (BuiltinPair BuiltinData BuiltinData) where
    {-# INLINABLE toBuiltin #-}
    toBuiltin (d1, d2) = mkPairData (toBuiltin d1) (toBuiltin d2)

instance HasFromBuiltin BuiltinData where
    type FromBuiltin BuiltinData = Data
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinData t) = t
instance HasToBuiltin BuiltinData where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinData

instance HasFromBuiltin BuiltinBLS12_381_G1_Element where
    type FromBuiltin BuiltinBLS12_381_G1_Element = BLS12_381.G1.Element
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinBLS12_381_G1_Element a) = a
instance HasToBuiltin BuiltinBLS12_381_G1_Element where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinBLS12_381_G1_Element

instance HasFromBuiltin BuiltinBLS12_381_G2_Element where
    type FromBuiltin BuiltinBLS12_381_G2_Element = BLS12_381.G2.Element
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinBLS12_381_G2_Element a) = a
instance HasToBuiltin BuiltinBLS12_381_G2_Element where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinBLS12_381_G2_Element

instance HasFromBuiltin BuiltinBLS12_381_MlResult where
    type FromBuiltin BuiltinBLS12_381_MlResult = BLS12_381.Pairing.MlResult
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinBLS12_381_MlResult a) = a
instance HasToBuiltin BuiltinBLS12_381_MlResult where
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinBLS12_381_MlResult
