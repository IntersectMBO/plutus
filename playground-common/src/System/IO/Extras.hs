module System.IO.Extras where

import Control.Monad.Catch (MonadMask, bracket)
import Control.Monad.IO.Class (MonadIO, liftIO)
import System.IO (Handle, IOMode, hClose, openFile)

-- withFile is a clone of System.IO.withFile however it is generalized over the monad
-- This might be done using unliftio I think however it looked to be more pain that
-- it was worth so I simply copied and pasted the definitions and changed the types.
withFile
    :: (MonadMask m, MonadIO m)
    => FilePath
    -> IOMode
    -> (Handle -> m a)
    -> m a
withFile path mode =
    bracket
        (liftIO $ openFile path mode)
        (\handle ->
            liftIO (hClose handle)
        )
