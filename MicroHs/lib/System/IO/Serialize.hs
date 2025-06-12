-- Copyright 2024 Lennart Augustsson
-- See LICENSE file for full license.
module System.IO.Serialize(
  hSerialize, hDeserialize
  writeSerialized, writeSerializedCompressed,
  readSerialized,
  ) where
import qualified Prelude(); import MiniPrelude
import Primitives(Ptr)
import System.IO
import System.IO.Internal

primHSerialize   :: forall a . Ptr BFILE -> a -> IO ()
primHSerialize    = _primitive "IO.serialize"
primHDeserialize :: forall a . Ptr BFILE -> IO a
primHDeserialize  = _primitive "IO.deserialize"

hSerialize   :: forall a . Handle -> a -> IO ()
hSerialize h a = withHandleWr h $ \ p -> primHSerialize p a

hDeserialize :: forall a . Handle -> IO a
hDeserialize h = withHandleRd h primHDeserialize

writeSerialized :: forall a . FilePath -> a -> IO ()
writeSerialized p s = do
  h <- openBinaryFile p WriteMode
  hSerialize h s
  hClose h

foreign import ccall "add_lz77_compressor" c_add_lz77_compressor :: Ptr BFILE -> IO (Ptr BFILE)
foreign import ccall "add_lz77_decompressor" c_add_lz77_decompressor :: Ptr BFILE -> IO (Ptr BFILE)

writeSerializedCompressed :: forall a . FilePath -> a -> IO ()
writeSerializedCompressed p s = do
  h <- openBinaryFile p WriteMode
  hPutChar h 'z'                               -- indicate compressed
  h' <- addTransducer c_add_lz77_compressor h
  hSerialize h' s
  hClose h'

-- Read compressed or uncompressed
readSerialized :: forall a . FilePath -> IO a
readSerialized p = do
  h <- openBinaryFile p ReadMode
  c <- hLookAhead h
  h' <- if c == 'z' then do                    -- compressed?
          hGetChar h   -- get rid of the 'z'
          addTransducer c_add_lz77_decompressor h
        else
          return h
  a <- hDeserialize h'
  hClose h'
  return a
