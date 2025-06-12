module Foreign.Marshal(
  module Foreign.Marshal.Alloc,
  module Foreign.Marshal.Array,
  module Foreign.Marshal.Error,
  module Foreign.Marshal.Utils,
  unsafeLocalState,
  ) where

import Primitives (primPerformIO)

import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Marshal.Error
import Foreign.Marshal.Utils

unsafeLocalState :: IO a -> a
unsafeLocalState = primPerformIO
