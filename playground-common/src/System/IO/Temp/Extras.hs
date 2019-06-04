module System.IO.Temp.Extras where

import           Control.Monad.Catch       (MonadCatch, MonadMask, bracket, catch)
import           Control.Monad.Error.Class (MonadError, catchError, throwError)
import           Control.Monad.IO.Class    (MonadIO, liftIO)
import           System.Directory          (removeFile)
import           System.IO                 (Handle, hClose, hFlush)
import           System.IO.Temp            (getCanonicalTemporaryDirectory, openTempFile)

-- ignoringIOErrors and withSystemTempFile are clones of the functions
-- in System.IO.Temp however they are generalized over the monad
-- This could be done using unliftio I think however it looked to be
-- more pain that it was worth so I simply copied and pasted the
-- definitions and changed the types.
{-# ANN ignoringIOErrors ("HLint: ignore Evaluate" :: String) #-}

ignoringIOErrors :: MonadCatch m => m () -> m ()
ignoringIOErrors ioe = ioe `catch` (\e -> const (return ()) (e :: IOError))

withSystemTempFile
    :: (MonadMask m, MonadIO m, MonadError e m)
    => FilePath
    -> (FilePath -> Handle -> m a)
    -> m a
withSystemTempFile template action = do
    tmpDir <- liftIO getCanonicalTemporaryDirectory
    bracket
        (liftIO $ openTempFile tmpDir template)
        (\(name, handle) ->
            liftIO (hClose handle >> ignoringIOErrors (removeFile name))
        )
        (uncurry action)
