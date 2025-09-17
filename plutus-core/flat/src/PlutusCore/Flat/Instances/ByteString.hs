-- | Flat instances for the bytestring library
{-# LANGUAGE NoMonomorphismRestriction #-}

module PlutusCore.Flat.Instances.ByteString
  ()
where

import Data.ByteString qualified as B
import Data.ByteString.Lazy qualified as L
import Data.ByteString.Short qualified as SBS
import PlutusCore.Flat.Class
import PlutusCore.Flat.Decoder
import PlutusCore.Flat.Encoder

-- $setup
-- >>> import PlutusCore.Flat.Instances.Test
-- >>> import PlutusCore.Flat.Instances.Base
-- >>> import qualified Data.ByteString               as B
-- >>> import qualified Data.ByteString.Lazy          as L
-- >>> import qualified Data.ByteString.Short         as SBS

{-|
ByteString, ByteString.Lazy and ByteString.Short are all encoded as Prealigned Arrays:

@
PreAligned a ≡ PreAligned {preFiller :: Filler, preValue :: a}

Filler ≡   FillerBit Filler
          | FillerEnd

Array v = A0
        | A1 v (Array v)
        | A2 v v (Array v)
        ...
        | A255 ... (Array v)
@

That's to say as a byte-aligned sequence of blocks of up to 255 elements, with every block preceded by the count of the elements in the block and a final 0-length block.

>>>  tst (B.pack [11,22,33])
(True,48,[1,3,11,22,33,0])

where:

1= PreAlignment (takes a byte if we are already on a byte boundary)

3= Number of bytes in ByteString

11,22,33= Bytes

0= End of Array

>>>  tst (B.pack [])
(True,16,[1,0])

Pre-alignment ensures that a ByteString always starts at a byte boundary:

>>>  tst ((False,True,False,B.pack [11,22,33]))
(True,51,[65,3,11,22,33,0])

All ByteStrings are encoded in the same way:

>>> all (tst (B.pack [55]) ==) [tst (L.pack [55]),tst (SBS.pack [55])]
True
-}
instance Flat B.ByteString where
  encode = eBytes
  size   = sBytes
  decode = dByteString

{- |
>>>  tst ((False,True,False,L.pack [11,22,33]))
(True,51,[65,3,11,22,33,0])
-}
instance Flat L.ByteString where
  encode = eLazyBytes
  size   = sLazyBytes
  decode = dLazyByteString

{- |
>>>  tst ((False,True,False,SBS.pack [11,22,33]))
(True,51,[65,3,11,22,33,0])
-}
instance Flat SBS.ShortByteString where
  encode = eShortBytes
  size   = sShortBytes
  decode = dShortByteString

