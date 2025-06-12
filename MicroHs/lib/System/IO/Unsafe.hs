module System.IO.Unsafe(unsafePerformIO, unsafeInterleaveIO) where
import qualified Prelude()
import Primitives

unsafePerformIO :: IO a -> a
unsafePerformIO = primPerformIO

unsafeInterleaveIO :: forall a . IO a -> IO a
unsafeInterleaveIO ioa = primReturn (primPerformIO ioa)
