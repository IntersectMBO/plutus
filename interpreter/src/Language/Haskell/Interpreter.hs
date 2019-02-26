{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Interpreter (runghc, CompilationError(..)) where

import           Control.Exception         (IOException)
import           Control.Monad             (unless)
import           Control.Monad.Catch       (MonadCatch, MonadMask, bracket, catch)
import           Control.Monad.Error.Class (MonadError, throwError)
import           Control.Monad.IO.Class    (MonadIO, liftIO)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.State (StateT, evalStateT, get, put)
import           Control.Newtype.Generics  (Newtype)
import qualified Control.Newtype.Generics  as Newtype
import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Bifunctor            (second)
import           Data.Maybe                (fromMaybe)
import           Data.Monoid               ((<>))
import           Data.Text                 (Text)
import qualified Data.Text                 as Text
import qualified Data.Text.Internal.Search as Text
import qualified Data.Text.IO              as Text
import           GHC.Generics              (Generic)
import           System.Directory          (removeFile)
import           System.Environment        (lookupEnv)
import           System.Exit               (ExitCode (ExitSuccess))
import           System.FilePath           ((</>))
import           System.IO.Error           (tryIOError)
import           System.IO.Temp            (getCanonicalTemporaryDirectory, openTempFile)
import           System.Process            (cwd, proc, readProcessWithExitCode)
import           Text.Read                 (readMaybe)

data CompilationError
    = RawError Text
    | CompilationError { filename :: !Text
                       , row      :: !Int
                       , column   :: !Int
                       , text     :: ![Text] }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | spawn an external process to runghc a file
--
--   If you set the environmental varaiable GHC_BIN_DIR
--   then the executable runghc in that path will be used.
--   This is useful if you want to your file to be run with some packages
--   available, you can create a wrapper runghc that includes these
--
--   Any errors are converted to [CompilationError]
runghc
    :: (MonadIO m, MonadError [CompilationError] m, MonadMask m)
    => [String]
    -> FilePath
    -> m String
runghc runghcOpts file = do
    bin <- liftIO lookupRunghc
    (exitCode, stdout, stderr) <- runProcess bin runghcOpts file
    case exitCode of
        ExitSuccess -> pure stdout
        _ ->
            throwError
                . parseErrorsText
                . Text.pack
                $ stderr

runProcess
    :: (MonadIO m, MonadError [CompilationError] m, MonadMask m)
    => FilePath
    -> [String]
    -> String
    -> m (ExitCode, String, String)
runProcess runghc runghcOpts file = do
    result <- liftIO $ tryIOError $ readProcessWithExitCode runghc (runghcOpts <> [file]) ""
    case result of
        Left e  -> throwError . pure . RawError . Text.pack . show $ e
        Right v -> pure v

lookupRunghc :: IO String
lookupRunghc = do
    mBinDir <- liftIO $ lookupEnv "GHC_BIN_DIR"
    case mBinDir of
        Nothing  -> pure "runghc"
        Just val -> pure $ val <> "/runghc"

parseErrorsText :: Text -> [CompilationError]
parseErrorsText input = parseErrorText <$> Text.splitOn "\n\n" input

parseErrorText :: Text -> CompilationError
parseErrorText input = fromMaybe (RawError input) $ flip evalStateT input $ do
    filename  <- consumeTo ":"
    rowStr    <- consumeTo ":"
    columnStr <- consumeTo ":"
    text      <- Text.lines <$> consume
    row       <- lift $ readMaybe $ Text.unpack rowStr
    column    <- lift $ readMaybe $ Text.unpack columnStr
    pure CompilationError { .. }


consumeTo :: Monad m => Text -> StateT Text m Text
consumeTo needle = do
    (before, after) <- breakWith needle <$> get
    put after
    pure before

consume :: (Monad m, Monoid s) => StateT s m s
consume = get <* put mempty

-- | Light `Data.Text.breakOn`, but consumes the breakpoint text (the 'needle').
breakWith :: Text -> Text -> (Text, Text)
breakWith needle = second (Text.drop 1) . Text.breakOn needle
