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
import GHC.Stack

{-
hSerialize   :: forall a . Handle -> a -> IO ()
hSerialize = errghc
hDeserialize :: forall a . Handle -> IO a
hDeserialize = errghc
writeSerialized :: forall a . FilePath -> a -> IO ()
writeSerialized = errghc
-}

writeSerializedCompressed :: forall a . HasCallStack => FilePath -> a -> IO ()
writeSerializedCompressed = errghc

writeSerialized :: forall a . HasCallStack => FilePath -> a -> IO ()
writeSerialized = errghc

readSerialized :: forall a . HasCallStack => FilePath -> IO a
readSerialized = errghc

errghc :: HasCallStack => a
errghc = error "System.IO.System: serialization not available with ghc"
