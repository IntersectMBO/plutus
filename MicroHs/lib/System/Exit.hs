module System.Exit(
  ExitCode(..),
  exitWith,
  exitFailure,
  exitSuccess,
  die,
  ) where
import qualified Prelude(); import MiniPrelude
import Control.Exception
import Data.Typeable
import System.IO

data ExitCode = ExitSuccess | ExitFailure Int
  deriving (Eq, Ord, Typeable, Show)

instance Exception ExitCode

exitWith :: forall a . ExitCode -> IO a
exitWith = throwIO

exitFailure :: forall a . IO a
exitFailure = exitWith (ExitFailure 1)

exitSuccess :: forall a . IO a
exitSuccess = exitWith ExitSuccess

die :: forall a . String -> IO a
die err = hPutStrLn stderr err >> exitFailure
