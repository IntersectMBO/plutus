module System.IO.Internal(
  FilePath,
  BFILE,
  Handle, HandleState(..),
  IOMode(..), ioModeToHMode,
  mkHandle, unsafeHandle,
  withHandleRd, withHandleWr, withHandleAny,
  getHandleState, setHandleState,
  killHandle,
  addTransducer) where
import qualified Prelude()
import Primitives
import Control.Applicative
import Control.Error
import Control.Monad
import Control.Monad.Fail
import Data.Bool
import Data.Char
import Data.Eq
import Data.Function
import Data.IORef
import Data.List
--import Foreign.ForeignPtr  causes import cycle
import Foreign.Ptr
import Mhs.Builtin
import System.IO_Handle
import System.IO.Unsafe
import Text.Show

instance Eq Handle where
  h == h'  =
    unsafePerformIO $
    withHandleAny h $ \ p ->
    withHandleAny h' $ \ p' ->
    pure (p == p')

instance Show Handle where
  show (Handle _ _ s) = "Handle(" ++ s ++ ")"

-----

type FilePath = String

data IOMode = ReadMode | WriteMode | AppendMode | ReadWriteMode
  deriving (Eq)

ioModeToHMode :: IOMode -> HandleState
ioModeToHMode ReadMode = HRead
ioModeToHMode WriteMode = HWrite
ioModeToHMode AppendMode = HWrite
ioModeToHMode ReadWriteMode = HReadWrite

unsafeHandle :: ForeignPtr BFILE -> HandleState -> String -> Handle
unsafeHandle fp m desc = unsafePerformIO $ do
  st <- newIORef m
  return (Handle fp st desc)

withHandle :: Handle -> (Ptr BFILE -> IO a) -> IO a
withHandle (Handle fp _ _) io = do
  a <- io (primForeignPtrToPtr fp)
  seq fp (return a)  -- hold on to fp so it's not gc():ed

withHandleM :: [HandleState] -> Handle -> (Ptr BFILE -> IO a) -> IO a
withHandleM ms h@(Handle _ st _) io = do
  m <- readIORef st
  unless (m `elem` ms) (error "Bad Handle mode")
  withHandle h io

withHandleRd :: Handle -> (Ptr BFILE -> IO a) -> IO a
withHandleRd = withHandleM [HRead, HReadWrite]

withHandleWr :: Handle -> (Ptr BFILE -> IO a) -> IO a
withHandleWr = withHandleM [HWrite, HReadWrite]

withHandleAny :: Handle -> (Ptr BFILE -> IO a) -> IO a
withHandleAny = withHandle

getHandleState :: Handle -> IO HandleState
getHandleState (Handle _ st _) = readIORef st

setHandleState :: Handle -> HandleState -> IO ()
setHandleState (Handle _ st _) m = writeIORef st m

foreign import ccall "&closeb" c_close :: FunPtr (Ptr BFILE -> IO ())

{-
primSetDesc :: [Char] -> ForeignPtr BFILE -> IO ()
primSetDesc = _primitive "fpstr"
-}

-- Create a Handle with the appropriate finalizer.
mkHandle :: [Char] -> Ptr BFILE -> HandleState -> IO Handle
mkHandle desc p mode = do
  fp <- primNewForeignPtr p
  primAddFinalizer c_close fp
{-
  primSetDesc desc fp
-}
  rmode <- newIORef mode
  return (Handle fp rmode desc)

-- When a handle is closed, we must remove the c_close finalizer.
killHandle :: Handle -> IO ()
killHandle (Handle fp _ _) =
  primAddFinalizer (primIntToFunPtr (0::Int)) fp

addTransducer :: (Ptr BFILE -> IO (Ptr BFILE)) -> Handle -> IO Handle
addTransducer trans h@(Handle _ st desc) =
  withHandle h $ \ p -> do        -- unwrap handle
    p' <- trans p                 -- add transducer
    mode <- readIORef st
    killHandle h                  -- old handle should not be finalized,
    mkHandle desc p' mode         --   because the new handle will do that

----------------------------------------

instance Functor IO where
  fmap f ioa   = ioa `primBind` \ a -> primReturn (f a)

instance Applicative IO where
  pure         = primReturn
  (<*>)        = ap

instance Monad IO where
  (>>=)        = primBind
  (>>)         = primThen
  return       = primReturn

instance MonadFail IO where
  fail         = error

