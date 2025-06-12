module Foreign.C.String(
  CString, CStringLen,
  newCAString, newCAStringLen,
  peekCAString, peekCAStringLen,
  withCAString, withCAStringLen,
  newCString, newCStringLen,
  peekCString, peekCStringLen,
  withCString, withCStringLen,
  ) where
import Data.ByteString.Internal
import Data.Char_Type
import Data.Coerce (coerce)
import Foreign.C.Types (CChar)
import Foreign.Marshal.Alloc
import Prelude qualified ()
import Primitives

primNewCAStringLen :: [Char] -> IO (Ptr CChar, Int)
primNewCAStringLen = _primitive "newCAStringLen"

type CString = Ptr CChar
type CStringLen = (Ptr CChar, Int)

newCAString :: String -> IO CString
newCAString s = primNewCAStringLen s `primBind` \ (s, _) -> primReturn s

newCAStringLen :: String -> IO CStringLen
newCAStringLen = primNewCAStringLen

withCAString :: forall a . String -> (CString -> IO a) -> IO a
withCAString s io =
  newCAString s `primBind` \ cs ->
  io cs `primBind` \ a ->
  free cs `primThen`
  primReturn a

withCAStringLen :: forall a . String -> (CStringLen -> IO a) -> IO a
withCAStringLen s io =
  newCAStringLen s `primBind` \ cs@(p, _) ->
  io cs `primBind` \ a ->
  free p `primThen`
  primReturn a

peekCAString :: CString -> IO String
peekCAString cstr = primPackCString cstr `primBind` \bs -> primReturn (primUnsafeCoerce unpack bs)

peekCAStringLen :: CStringLen -> IO String
peekCAStringLen (cstr, len) = primPackCStringLen cstr len `primBind` \bs -> primReturn (primUnsafeCoerce unpack bs)

------------------------------------------------------
-- XXX:  No encoding!

newCString :: String -> IO CString
newCString = newCAString

newCStringLen :: String -> IO CStringLen
newCStringLen = newCAStringLen

withCString :: forall a . String -> (CString -> IO a) -> IO a
withCString = withCAString

withCStringLen :: forall a . String -> (CStringLen -> IO a) -> IO a
withCStringLen = withCAStringLen

peekCString :: CString -> IO String
peekCString = peekCAString

peekCStringLen :: CStringLen -> IO String
peekCStringLen = peekCAStringLen
