module Foreign.Marshal.Error (
  throwIf,
  throwIf_,
  throwIfNeg,
  throwIfNeg_,
  throwIfNull,
  void,
) where
import qualified Prelude(); import MiniPrelude
import Data.Functor(void)
import Foreign.Ptr
import System.IO.Error(ioError, userError)

throwIf :: (a -> Bool) -> (a -> String) -> IO a -> IO a
throwIf pred msgfct act = do
  res <- act
  (if pred res then ioError . userError . msgfct else return) res

throwIf_ :: (a -> Bool) -> (a -> String) -> IO a -> IO ()
throwIf_ pred msgfct act  = void $ throwIf pred msgfct act

throwIfNeg :: (Ord a, Num a) => (a -> String) -> IO a -> IO a
throwIfNeg = throwIf (< 0)

throwIfNeg_ :: (Ord a, Num a) => (a -> String) -> IO a -> IO ()
throwIfNeg_ = throwIf_ (< 0)

throwIfNull :: String -> IO (Ptr a) -> IO (Ptr a)
throwIfNull = throwIf (== nullPtr) . const
