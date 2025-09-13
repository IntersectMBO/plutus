{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{- | Wrapper type to decode a value to its flat serialisation.

See <../test/Big.hs> for an example of use.

See also 'Flat.Decoder.listTDecoder' and "Flat.AsSize" for other ways to handle large decoded values.

In 0.5.X this type was called @Repr@.

@since 0.6
-}
module PlutusCore.Flat.AsBin(AsBin,unbin) where

import Data.ByteString qualified as B
import Foreign (plusPtr)
import PlutusCore.Flat.Bits (bits, fromBools, toBools)
import PlutusCore.Flat.Class (Flat (..))
import PlutusCore.Flat.Decoder.Prim (binOf)
import PlutusCore.Flat.Decoder.Types (Get (Get, runGet), GetResult (GetResult),
                                      S (S, currPtr, usedBits))
import PlutusCore.Flat.Run (unflatRawWithOffset)
import Text.PrettyPrint.HughesPJClass (Doc, Pretty (pPrint), prettyShow, text)

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import PlutusCore.Flat.Instances.Base
-- >>> import PlutusCore.Flat.Instances.Text
-- >>> import PlutusCore.Flat.Decoder.Types
-- >>> import PlutusCore.Flat.Types
-- >>> import PlutusCore.Flat.Run
-- >>> import Data.Word
-- >>> import qualified Data.Text as T
-- >>> import Text.PrettyPrint.HughesPJClass

{- |

When the flat serialisation of a value takes a lot less memory than the value itself, it can be convenient to keep the value in its encoded representation and decode it on demand.

To do so, just decode a value `a` as a `AsBin a`.

Examples:

Encode a list of Ints and then decode it to a list of AsBin Int:

>>> unflat (flat [1::Int .. 3]) :: Decoded ([AsBin Int])
Right [AsBin {repr = "\129A", offsetBits = 1},AsBin {repr = "A ", offsetBits = 2},AsBin {repr = " \193", offsetBits = 3}]

To decode an `AsBin a` to an `a`, use `unbin`:

>>> unbin <$> (unflat (flat 'a') :: Decoded (AsBin Char))
Right 'a'

Keep the values of a list of Ints encoded and decode just one on demand:

>>> let Right l :: Decoded [AsBin Int] = unflat (flat [1..5]) in unbin (l  !! 2)
3

Show exactly how values are encoded:

>>> let Right t :: Decoded (AsBin Bool,AsBin Word8,AsBin Bool) = unflat (flat (False,3:: Word64,True)) in prettyShow t
"(0, _0000001 1, _1)"

Ten bits in total spread over two bytes:

@
0
_0000001 1
         _1
=
00000001 11
@

Tests:

>>> unflat (flat ()) :: Decoded (AsBin ())
Right (AsBin {repr = "", offsetBits = 0})

>>> unflat (flat (False,True)) :: Decoded (Bool,AsBin Bool)
Right (False,AsBin {repr = "A", offsetBits = 1})

>>> unflat (flat (False,False,255 :: Word8)) :: Decoded (Bool,Bool,AsBin Word8)
Right (False,False,AsBin {repr = "?\193", offsetBits = 2})

>>> let Right (b0,b1,rw,b3) :: Decoded (Bool,Bool,AsBin Word8,Bool) = unflat (flat (False,False,255 :: Word8,True)) in (b0,b1,unbin rw,b3)
(False,False,255,True)
-}

data AsBin a = AsBin {
    repr        :: B.ByteString -- ^ Flat encoding of the value (encoding starts after offset bits in the first byte and ends in an unspecified position in the last byte)
    ,offsetBits :: Int -- ^ First byte offset: number of unused most significant bits in the first byte
    } deriving Show

instance Flat a => Pretty (AsBin a) where
    pPrint :: AsBin a -> Doc
    pPrint r = let n = replicate (offsetBits r) in text $ n '_' ++  (drop (offsetBits r) . prettyShow . fromBools . (n False ++) . toBools . bits $ unbin r)

-- | Decode a value
unbin :: Flat a => AsBin a -> a
unbin a =
    case unflatRawWithOffset dec (repr a) (offsetBits a) of
        Right a -> a
        Left e  -> error (show e) -- impossible, as it is a valid encoding
    where
        dec = Get $ \end s -> do
          GetResult s' a <- runGet decode end s
          let s'' = S (currPtr s' `plusPtr` if usedBits s' == 0 then 0 else 1) 0
          return $ GetResult s'' a

instance Flat a => Flat (AsBin a) where
    size = error "unused"

    encode = error "unused"

    decode :: Flat a => Get (AsBin a)
    decode = uncurry AsBin <$> binOf (decode :: Get a)
