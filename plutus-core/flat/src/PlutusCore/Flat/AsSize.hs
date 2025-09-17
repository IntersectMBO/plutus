{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{- |
Wrapper type to decode a value to its size in bits.

See also "Flat.AsBin".

In 0.5.X this type was called @SizeOf@.

@since 0.6
-}
module PlutusCore.Flat.AsSize(AsSize(..)) where

import PlutusCore.Flat.Class (Flat (..))
import PlutusCore.Flat.Decoder.Prim (sizeOf)
import PlutusCore.Flat.Decoder.Types (Get)
import PlutusCore.Flat.Types (NumBits)

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import PlutusCore.Flat.Instances.Base
-- >>> import PlutusCore.Flat.Instances.Text
-- >>> import PlutusCore.Flat.Decoder.Types
-- >>> import PlutusCore.Flat.Types
-- >>> import PlutusCore.Flat.Run
-- >>> import Data.Word
-- >>> import qualified Data.Text as T

{- |
Useful to skip unnecessary values and to check encoding sizes.

Examples:

Ignore the second and fourth component of a tuple:

>>> let v = flat ('a',"abc",'z',True) in unflat v :: Decoded (Char,AsSize String,Char,AsSize Bool)
Right ('a',AsSize 28,'z',AsSize 1)

Notice the variable size encoding of Words:

>>> unflat (flat (1::Word16,1::Word64)) :: Decoded (AsSize Word16,AsSize Word64)
Right (AsSize 8,AsSize 8)

Text:

>>> unflat (flat (T.pack "",T.pack "a",T.pack "主",UTF8Text $ T.pack "主",UTF16Text $ T.pack "主",UTF16Text $ T.pack "a")) :: Decoded (AsSize T.Text,AsSize T.Text,AsSize T.Text,AsSize UTF8Text,AsSize UTF16Text,AsSize UTF16Text)
Right (AsSize 16,AsSize 32,AsSize 48,AsSize 48,AsSize 40,AsSize 40)

Various encodings:

>>> unflat (flat (False,[T.pack "",T.pack "a",T.pack "主"],'a')) :: Decoded (AsSize Bool,AsSize [T.Text],AsSize Char)
Right (AsSize 1,AsSize 96,AsSize 8)
-}
newtype AsSize a = AsSize NumBits deriving (Eq,Ord,Show)

instance Flat a => Flat (AsSize a) where
    size :: Flat a => AsSize a -> NumBits -> NumBits
    size = error "unused"

    encode = error "unused"

    decode :: Flat a => Get (AsSize a)
    decode = AsSize <$> sizeOf (decode :: Get a)
