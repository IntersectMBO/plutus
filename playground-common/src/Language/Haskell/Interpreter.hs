{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}

module Language.Haskell.Interpreter
    ( runghc
    , CompilationError(..)
    , InterpreterError(..)
    , SourceCode(..)
    , avoidUnsafe
    , Warning(..)
    , InterpreterResult(..)
    ) where

import           Control.Exception         (IOException)
import           Control.Monad             (unless)
import           Control.Monad.Catch       (MonadCatch, MonadMask, bracket, catch)
import           Control.Monad.Error.Class (MonadError, throwError)
import           Control.Monad.IO.Class    (MonadIO, liftIO)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.State (StateT, evalStateT, get, put)
import           Control.Newtype.Generics  (Newtype)
import qualified Control.Newtype.Generics  as Newtype
import           Control.Timeout           (timeout)
import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Bifunctor            (second)
import           Data.Maybe                (fromMaybe)
import           Data.Monoid               ((<>))
import           Data.Morpheus.Kind        (KIND, OBJECT, SCALAR, UNION)
import           Data.Morpheus.Types       (GQLArgs, GQLScalar (..), GQLType)
import qualified Data.Morpheus.Types       as Morpheus
import           Data.Text                 (Text)
import qualified Data.Text                 as Text
import qualified Data.Text.Internal.Search as Text
import qualified Data.Text.IO              as Text
import           Data.Time.Units           (TimeUnit)
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
    | CompilationError
          { filename :: !Text
          , row      :: !Int
          , column   :: !Int
          , text     :: ![Text]
          }
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON, GQLType)

data InterpreterError
    = CompilationErrors [CompilationError]
    | TimeoutError Text
    deriving (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON, GQLType)

type instance KIND InterpreterError = UNION

newtype SourceCode =
    SourceCode Text
    deriving (Generic)
    deriving newtype (ToJSON, FromJSON)
    deriving anyclass (Newtype, GQLType)

-- type instance KIND SourceCode = SCALAR

instance GQLScalar SourceCode where
    parseValue (Morpheus.String str) = Right $ SourceCode str
    parseValue _                     = Left "Expected SourceCode string."
    serialize (SourceCode str) = Morpheus.String str

newtype Warning =
    Warning Text
    deriving (Eq, Show, Generic)
    deriving newtype (ToJSON, GQLType)

type instance KIND Warning = SCALAR

instance GQLScalar Warning where
    parseValue (Morpheus.String str) = Right $ Warning str
    parseValue _                     = Left "Expected Warning string."
    serialize (Warning str) = Morpheus.String str

data InterpreterResult a =
    InterpreterResult
        { warnings :: [Warning]
        , result   :: a
        }
    deriving (Eq, Show, Generic, Functor)
    deriving anyclass (ToJSON, GQLType)

-- | spawn an external process to runghc a file
--
--   If you set the environmental varaiable GHC_BIN_DIR
--   then the executable runghc in that path will be used.
--   This is useful if you want to your file to be run with some packages
--   available, you can create a wrapper runghc that includes these
--
--   Any errors are converted to InterpreterError
runghc ::
       ( Show t
       , TimeUnit t
       , MonadIO m
       , MonadError InterpreterError m
       , MonadMask m
       )
    => t
    -> [String]
    -> FilePath
    -> m (InterpreterResult String)
runghc t runghcOpts file = do
    bin <- liftIO lookupRunghc
    (exitCode, stdout, stderr) <- runProcess bin t runghcOpts file
    case exitCode of
        ExitSuccess -> pure $ InterpreterResult [] stdout
        _ ->
            throwError . CompilationErrors . parseErrorsText . Text.pack $
            stderr

runProcess ::
       ( Show t
       , TimeUnit t
       , MonadIO m
       , MonadError InterpreterError m
       , MonadMask m
       )
    => FilePath
    -> t
    -> [String]
    -> String
    -> m (ExitCode, String, String)
runProcess bin timeoutValue runghcOpts file = do
    result <-
        timeout' timeoutValue $
        liftIO $
        tryIOError $ readProcessWithExitCode bin (runghcOpts <> [file]) ""
    case result of
        Left e ->
            throwError . CompilationErrors . pure . RawError . Text.pack . show $
            e
        Right v -> pure v
  where
    timeout' ::
           ( Show t
           , TimeUnit t
           , MonadIO m
           , MonadError InterpreterError m
           , MonadCatch m
           )
        => t
        -> m a
        -> m a
    timeout' timeoutValue a = do
        mr <- timeout timeoutValue a
        case mr of
            Nothing ->
                throwError (TimeoutError . Text.pack . show $ timeoutValue)
            Just r -> pure r

avoidUnsafe :: (MonadError InterpreterError m) => SourceCode -> m ()
avoidUnsafe s =
    unless (null . Text.indices "unsafe" . Newtype.unpack $ s) .
    throwError . CompilationErrors . pure $
    RawError "Cannot interpret unsafe functions"

lookupRunghc :: IO String
lookupRunghc = do
    mBinDir <- liftIO $ lookupEnv "GHC_BIN_DIR"
    case mBinDir of
        Nothing  -> pure "runghc"
        Just val -> pure $ val <> "/runghc"

parseErrorsText :: Text -> [CompilationError]
parseErrorsText input = parseErrorText <$> Text.splitOn "\n\n" input

parseErrorText :: Text -> CompilationError
parseErrorText input =
    fromMaybe (RawError input) $
    flip evalStateT input $ do
        filename <- consumeTo ":"
        rowStr <- consumeTo ":"
        columnStr <- consumeTo ":"
        text <- Text.lines <$> consume
        row <- lift $ readMaybe $ Text.unpack rowStr
        column <- lift $ readMaybe $ Text.unpack columnStr
        pure CompilationError {..}

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
