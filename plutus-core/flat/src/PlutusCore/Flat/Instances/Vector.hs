-- | Flat instances for the vector package.
module PlutusCore.Flat.Instances.Vector ()
where

import PlutusCore.Flat.Instances.Mono
import PlutusCore.Flat.Instances.Util

import Data.Vector qualified as V
import Data.Vector.Storable qualified as S
import Data.Vector.Unboxed qualified as U

{-$setup
>>> import PlutusCore.Flat.Instances.Test
>>> import PlutusCore.Flat.Instances.Base()
>>> import qualified Data.Vector                   as V
>>> import qualified Data.Vector.Unboxed           as U
>>> import qualified Data.Vector.Storable          as S -}

{-|
Vectors are encoded as arrays.

>>> tst (V.fromList [11::Word8,22,33])
(True,40,[3,11,22,33,0])

All Vectors are encoded in the same way:

>>> let l = [11::Word8,22,33] in all (tst (V.fromList l) ==) [tst (U.fromList l),tst (S.fromList l)]
True -}
instance Flat a => Flat (V.Vector a) where
  size = sizeSequence
  encode = encodeSequence
  decode = decodeSequence

instance (U.Unbox a, Flat a) => Flat (U.Vector a) where
  size = sizeSequence
  encode = encodeSequence
  decode = decodeSequence

instance (S.Storable a, Flat a) => Flat (S.Vector a) where
  size = sizeSequence
  encode = encodeSequence
  decode = decodeSequence
