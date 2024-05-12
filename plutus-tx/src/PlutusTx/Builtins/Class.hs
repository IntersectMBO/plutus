{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}
-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusTx.Builtins.Class (module Export) where

import PlutusTx.Builtins.HasBuiltin as Export

import Prelude qualified as Haskell (String)

import Data.ByteString (ByteString)
import PlutusTx.Builtins.Internal

import Data.String (IsString (..))
import Data.Text (Text, pack)
import GHC.Magic qualified as Magic

import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1 (Element)
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2 (Element)
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing (MlResult)
import PlutusCore.Default qualified as PLC
import PlutusTx.Base (const, id, ($))
import PlutusTx.Bool (Bool (..))
import PlutusTx.Integer (Integer)

-- -- See Note [Builtin types and their Haskell versions]
-- {-|
-- A class witnessing the ability to convert from the builtin representation to the Haskell representation.
-- -}
-- class FromBuiltin arep a | arep -> a where
--     fromBuiltin :: arep -> a

-- -- See Note [Builtin types and their Haskell versions]
-- {-|
-- A class witnessing the ability to convert from the Haskell representation to the builtin representation.
-- -}
-- class ToBuiltin a arep | a -> arep where
--     toBuiltin :: a -> arep

-- instance FromBuiltin BuiltinInteger Integer where
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin = id
-- instance ToBuiltin Integer BuiltinInteger where
--     {-# INLINABLE toBuiltin #-}
--     toBuiltin = id

-- instance FromBuiltin BuiltinBool Bool where
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin b = ifThenElse b True False
-- instance ToBuiltin Bool BuiltinBool where
--     {-# INLINABLE toBuiltin #-}
--     toBuiltin b = if b then true else false

-- instance FromBuiltin BuiltinUnit () where
--     -- See Note [Strict conversions to/from unit]
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin u = chooseUnit u ()
-- instance ToBuiltin () BuiltinUnit where
--     -- See Note [Strict conversions to/from unit]
--     {-# INLINABLE toBuiltin #-}
--     toBuiltin x = case x of () -> unitval

-- instance FromBuiltin BuiltinByteString ByteString where
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin (BuiltinByteString b) = b
-- instance ToBuiltin ByteString BuiltinByteString where
--     {-# INLINABLE toBuiltin #-}
--     toBuiltin = BuiltinByteString

-- -- We can't put this in `Builtins.hs`, since that force `O0` deliberately, which prevents
-- -- the unfoldings from going in. So we just stick it here. Fiddly.
-- instance IsString BuiltinString where
--     -- Try and make sure the dictionary selector goes away, it's simpler to match on
--     -- the application of 'stringToBuiltinString'
--     {-# INLINE fromString #-}
--     -- See Note [noinline hack]
--     fromString = Magic.noinline stringToBuiltinString

-- {-# INLINABLE stringToBuiltinString #-}
-- stringToBuiltinString :: Haskell.String -> BuiltinString
-- -- To explain why the obfuscatedId is here
-- -- See Note [noinline hack]
-- stringToBuiltinString str = obfuscatedId (BuiltinString $ pack str)

-- {-# NOINLINE obfuscatedId #-}
-- obfuscatedId :: a -> a
-- obfuscatedId a = a

-- instance FromBuiltin BuiltinString Text where
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin (BuiltinString t) = t
-- instance ToBuiltin Text BuiltinString where
--     {-# INLINABLE toBuiltin #-}
--     toBuiltin = BuiltinString

-- {- Same noinline hack as with `String` type. -}
-- instance IsString BuiltinByteString where
--     -- Try and make sure the dictionary selector goes away, it's simpler to match on
--     -- the application of 'stringToBuiltinByteString'
--     {-# INLINE fromString #-}
--     -- See Note [noinline hack]
--     fromString = Magic.noinline stringToBuiltinByteString

-- {-# INLINABLE stringToBuiltinByteString #-}
-- stringToBuiltinByteString :: Haskell.String -> BuiltinByteString
-- stringToBuiltinByteString str = encodeUtf8 $ stringToBuiltinString str

-- instance (FromBuiltin arep a, FromBuiltin brep b) => FromBuiltin (BuiltinPair arep brep) (a,b) where
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin p = (fromBuiltin $ fst p, fromBuiltin $ snd p)
-- instance ToBuiltin (BuiltinData, BuiltinData) (BuiltinPair BuiltinData BuiltinData) where
--     {-# INLINABLE toBuiltin #-}
--     toBuiltin (d1, d2) = mkPairData d1 d2

-- instance FromBuiltin arep a => FromBuiltin (BuiltinList arep) [a] where
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin = go
--       where
--           -- The combination of both INLINABLE and a type signature seems to stop this getting lifted to the top
--           -- level, which means it gets a proper unfolding, which means that specialization can work, which can
--           -- actually help quite a bit here.
--           {-# INLINABLE go #-}
--           go :: BuiltinList arep -> [a]
--           -- Note that we are using builtin chooseList here so this is *strict* application! So we need to do
--           -- the manual laziness ourselves.
--           go l = chooseList l (const []) (\_ -> fromBuiltin (head l):go (tail l)) unitval

-- instance (PLC.DefaultUni `PLC.Contains` a, ToBuiltin a arep) =>
--         ToBuiltin [a] (BuiltinList arep) where
--     {-# INLINE toBuiltin #-}
--     toBuiltin = goList where
--         goList :: [a] -> BuiltinList arep
--         goList []     = mkNil @a PLC.knownUni
--         goList (d:ds) = mkCons (toBuiltin d) (goList ds)

-- instance FromBuiltin BuiltinData BuiltinData where
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin = id
-- instance ToBuiltin BuiltinData BuiltinData where
--     {-# INLINABLE toBuiltin #-}
--     toBuiltin = id

-- instance FromBuiltin BuiltinBLS12_381_G1_Element BLS12_381.G1.Element where
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin (BuiltinBLS12_381_G1_Element a) = a
-- instance ToBuiltin BLS12_381.G1.Element BuiltinBLS12_381_G1_Element where
--     {-# INLINABLE toBuiltin #-}
--     toBuiltin = BuiltinBLS12_381_G1_Element

-- instance FromBuiltin BuiltinBLS12_381_G2_Element BLS12_381.G2.Element where
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin (BuiltinBLS12_381_G2_Element a) = a
-- instance ToBuiltin BLS12_381.G2.Element BuiltinBLS12_381_G2_Element where
--     {-# INLINABLE toBuiltin #-}
--     toBuiltin = BuiltinBLS12_381_G2_Element

-- instance FromBuiltin BuiltinBLS12_381_MlResult BLS12_381.Pairing.MlResult where
--     {-# INLINABLE fromBuiltin #-}
--     fromBuiltin (BuiltinBLS12_381_MlResult a) = a
-- instance ToBuiltin BLS12_381.Pairing.MlResult BuiltinBLS12_381_MlResult where
--     {-# INLINABLE toBuiltin #-}
--     toBuiltin = BuiltinBLS12_381_MlResult
