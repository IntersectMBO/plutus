module Foundation.Exception
    ( finally
    , try
    , SomeException
    ) where

import Basement.Imports
import Control.Exception (Exception, SomeException)
import Foundation.Monad.Exception

finally :: MonadBracket m => m a -> m b -> m a
finally f g = generalBracket (return ()) (\() a -> g >> return a) (\() _ -> g) (const f)

try :: (MonadCatch m, Exception e) => m a -> m (Either e a)
try a = catch (a >>= \ v -> return (Right v)) (\e -> return (Left e))
