{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE TypeApplications #-}
import Data.ByteString as BS
import Data.JSString
import Flat
import GHC.Generics
import GHCJS.Buffer qualified as Buffer
import JavaScript.TypedArray.ArrayBuffer

data Foo
  = Foo
  | Bar
  | Baz
  deriving (Show, Generic, Flat)

main :: IO ()
main = do
  -- >>> [1]
  print $ BS.unpack $ flat Foo
  -- >>> Right Foo
  print $ unflat @Foo $ flat Foo
  -- >>> Right Foo
  print $ unflat @Foo $ BS.pack [1]
  -- >>> RangeError: Offset is outside the bounds of the DataView
  -- at DataView.getUint16
  print $ unflat @Foo $ fromSingleByte 1

fromSingleByte :: Int -> ByteString
fromSingleByte = Buffer.toByteString 0 Nothing .
  Buffer.createFromArrayBuffer . fromSingleByte_js

foreign import javascript unsafe
  "var buf = new ArrayBuffer(1);\
  \var view = new Int8Array(buf);\
  \view[0] = $1;\
  \$r = buf;"
  fromSingleByte_js :: Int -> ArrayBuffer
