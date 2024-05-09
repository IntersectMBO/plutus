{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeSynonymInstances     #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusTx.Builtins.IsBuiltin where

import PlutusCore qualified as PLC
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

type IsBuiltin :: GHC.Type -> GHC.Constraint
class PLC.DefaultUni `PLC.Contains` (FromBuiltin a) => IsBuiltin a where
    type FromBuiltin a
    fromBuiltin :: a -> FromBuiltin a
    toBuiltin :: FromBuiltin a -> a

instance IsBuiltin BuiltinInteger where
    type FromBuiltin BuiltinInteger = Integer
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin = id
    {-# INLINABLE toBuiltin #-}
    toBuiltin = id

instance IsBuiltin BuiltinByteString where
    type FromBuiltin BuiltinByteString = ByteString
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinByteString b) = b
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinByteString

instance IsBuiltin BuiltinString where
    type FromBuiltin BuiltinString = Text
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinString t) = t
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinString

instance IsBuiltin BuiltinUnit where
    type FromBuiltin BuiltinUnit = ()
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin u = chooseUnit u ()
    {-# INLINABLE toBuiltin #-}
    toBuiltin x = case x of () -> unitval

instance IsBuiltin BuiltinBool where
    type FromBuiltin BuiltinBool = Bool
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin b = ifThenElse b True False
    {-# INLINABLE toBuiltin #-}
    toBuiltin b = if b then true else false

instance IsBuiltin a => IsBuiltin (BuiltinList a) where
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

    {-# INLINE toBuiltin #-}
    toBuiltin = goList where
        goList :: [FromBuiltin a] -> BuiltinList a
        goList []     = mkNil @(FromBuiltin a) (Magic.inline PLC.knownUni)
        goList (d:ds) = mkCons (toBuiltin d) (goList ds)

instance (IsBuiltin a, IsBuiltin b) => IsBuiltin (BuiltinPair a b) where
    type FromBuiltin (BuiltinPair a b) = (FromBuiltin a, FromBuiltin b)
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin p = (fromBuiltin $ fst p, fromBuiltin $ snd p)
    {-# INLINABLE toBuiltin #-}
    toBuiltin (d1, d2) =
        mkPair
            @(FromBuiltin a)
            @(FromBuiltin b)
            (Magic.inline PLC.knownUni)
            (Magic.inline PLC.knownUni)
            (toBuiltin d1)
            (toBuiltin d2)

instance IsBuiltin BuiltinData where
    type FromBuiltin BuiltinData = Data
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinData t) = t
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinData

instance IsBuiltin BuiltinBLS12_381_G1_Element where
    type FromBuiltin BuiltinBLS12_381_G1_Element = BLS12_381.G1.Element
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinBLS12_381_G1_Element a) = a
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinBLS12_381_G1_Element

instance IsBuiltin BuiltinBLS12_381_G2_Element where
    type FromBuiltin BuiltinBLS12_381_G2_Element = BLS12_381.G2.Element
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinBLS12_381_G2_Element a) = a
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinBLS12_381_G2_Element

instance IsBuiltin BuiltinBLS12_381_MlResult where
    type FromBuiltin BuiltinBLS12_381_MlResult = BLS12_381.Pairing.MlResult
    {-# INLINABLE fromBuiltin #-}
    fromBuiltin (BuiltinBLS12_381_MlResult a) = a
    {-# INLINABLE toBuiltin #-}
    toBuiltin = BuiltinBLS12_381_MlResult
