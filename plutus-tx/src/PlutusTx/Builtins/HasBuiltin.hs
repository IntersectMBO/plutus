{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}

module PlutusTx.Builtins.HasBuiltin where

import Prelude

import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1 (Element)
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2 (Element)
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing (MlResult)
import PlutusCore.Data (Data)
import PlutusCore.Default qualified as PLC
import PlutusTx.Builtins.Internal

import Data.ByteString (ByteString)
import Data.Kind qualified as GHC
import Data.Text (Text)

-- Also see Note [Built-in types and their Haskell counterparts].
-- | A class for converting values of Haskell-defined built-in types to their Plutus Tx
-- counterparts.
type HasToBuiltin :: GHC.Type -> GHC.Constraint
class PLC.DefaultUni `PLC.Contains` a => HasToBuiltin a where
    type ToBuiltin a
    toBuiltin :: a -> ToBuiltin a

-- Also see Note [Built-in types and their Haskell counterparts].
-- | A class for converting values of Plutus Tx built-in types to their Haskell-defined
-- counterparts.
type HasFromBuiltin :: GHC.Type -> GHC.Constraint
class HasToBuiltin (FromBuiltin arep) => HasFromBuiltin arep where
    type FromBuiltin arep
    fromBuiltin :: arep -> FromBuiltin arep

instance HasToBuiltin Integer where
    type ToBuiltin Integer = BuiltinInteger
    toBuiltin = id
instance HasFromBuiltin BuiltinInteger where
    type FromBuiltin BuiltinInteger = Integer
    fromBuiltin = id

instance HasToBuiltin ByteString where
    type ToBuiltin ByteString = BuiltinByteString
    toBuiltin = BuiltinByteString
instance HasFromBuiltin BuiltinByteString where
    type FromBuiltin BuiltinByteString = ByteString
    fromBuiltin (BuiltinByteString b) = b

instance HasToBuiltin Text where
    type ToBuiltin Text = BuiltinString
    toBuiltin = BuiltinString
instance HasFromBuiltin BuiltinString where
    type FromBuiltin BuiltinString = Text
    fromBuiltin (BuiltinString t) = t

instance HasToBuiltin () where
    type ToBuiltin () = BuiltinUnit
    toBuiltin = BuiltinUnit
instance HasFromBuiltin BuiltinUnit where
    type FromBuiltin BuiltinUnit = ()
    fromBuiltin (BuiltinUnit u) = u

instance HasToBuiltin Bool where
    type ToBuiltin Bool = BuiltinBool
    toBuiltin = BuiltinBool
instance HasFromBuiltin BuiltinBool where
    type FromBuiltin BuiltinBool = Bool
    fromBuiltin (BuiltinBool b) = b

instance HasToBuiltin a => HasToBuiltin [a] where
    type ToBuiltin [a] = BuiltinList (ToBuiltin a)
    toBuiltin = BuiltinList . map toBuiltin
instance HasFromBuiltin a => HasFromBuiltin (BuiltinList a) where
    type FromBuiltin (BuiltinList a) = [FromBuiltin a]
    fromBuiltin (BuiltinList xs) = map fromBuiltin xs

instance (HasToBuiltin a, HasToBuiltin b) => HasToBuiltin (a, b) where
    type ToBuiltin (a, b) = BuiltinPair (ToBuiltin a) (ToBuiltin b)
    toBuiltin (x, y) = BuiltinPair (toBuiltin x, toBuiltin y)
instance (HasFromBuiltin a, HasFromBuiltin b) => HasFromBuiltin (BuiltinPair a b) where
    type FromBuiltin (BuiltinPair a b) = (FromBuiltin a, FromBuiltin b)
    fromBuiltin (BuiltinPair (x, y)) = (fromBuiltin x, fromBuiltin y)

instance HasToBuiltin Data where
    type ToBuiltin Data = BuiltinData
    toBuiltin = BuiltinData
instance HasFromBuiltin BuiltinData where
    type FromBuiltin BuiltinData = Data
    fromBuiltin (BuiltinData t) = t

instance HasToBuiltin BLS12_381.G1.Element where
    type ToBuiltin BLS12_381.G1.Element = BuiltinBLS12_381_G1_Element
    toBuiltin = BuiltinBLS12_381_G1_Element
instance HasFromBuiltin BuiltinBLS12_381_G1_Element where
    type FromBuiltin BuiltinBLS12_381_G1_Element = BLS12_381.G1.Element
    fromBuiltin (BuiltinBLS12_381_G1_Element a) = a

instance HasToBuiltin BLS12_381.G2.Element where
    type ToBuiltin BLS12_381.G2.Element = BuiltinBLS12_381_G2_Element
    toBuiltin = BuiltinBLS12_381_G2_Element
instance HasFromBuiltin BuiltinBLS12_381_G2_Element where
    type FromBuiltin BuiltinBLS12_381_G2_Element = BLS12_381.G2.Element
    fromBuiltin (BuiltinBLS12_381_G2_Element a) = a

instance HasToBuiltin BLS12_381.Pairing.MlResult where
    type ToBuiltin BLS12_381.Pairing.MlResult = BuiltinBLS12_381_MlResult
    toBuiltin = BuiltinBLS12_381_MlResult
instance HasFromBuiltin BuiltinBLS12_381_MlResult where
    type FromBuiltin BuiltinBLS12_381_MlResult = BLS12_381.Pairing.MlResult
    fromBuiltin (BuiltinBLS12_381_MlResult a) = a
