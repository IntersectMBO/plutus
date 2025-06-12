module Control.Monad.Fail(MonadFail(..)) where
import qualified Prelude()              -- do not import Prelude
import Primitives
import Control.Applicative
import Control.Error
import Control.Monad
import Data.Char
import Data.List_Type

class Monad m => MonadFail m where
  fail :: forall a . String -> m a
  fail = error

instance MonadFail [] where
  fail _ = []
