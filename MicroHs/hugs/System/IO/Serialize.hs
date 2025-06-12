-- Copyright 2024 Lennart Augustsson
-- See LICENSE file for full license.
module System.IO.Serialize(
{-
  hSerialize, hDeserialize,
  writeSerialized,
-}
  writeSerialized,
  writeSerializedCompressed,
  readSerialized,
  ) where
--import System.IO

{-
hSerialize   :: forall a . Handle -> a -> IO ()
hSerialize = errhugs
hDeserialize :: forall a . Handle -> IO a
hDeserialize = errhugs
writeSerialized :: forall a . FilePath -> a -> IO ()
writeSerialized = errhugs
-}

writeSerializedCompressed :: FilePath -> a -> IO ()
writeSerializedCompressed = errhugs

writeSerialized :: FilePath -> a -> IO ()
writeSerialized = errhugs

readSerialized ::  FilePath -> IO a
readSerialized = errhugs

errhugs :: a
errhugs = error "System.IO.Serialize: serialization not available with hugs"
