{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Interpreter where

import           API                          (RunResult (RunResult))
import           Control.Monad                (unless)
import           Control.Monad.Catch          (MonadCatch, MonadMask, bracket, catch)
import           Control.Monad.Error.Class    (MonadError, catchError, throwError)
import           Control.Monad.Except.Extras  (mapError)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import           Control.Monad.Trans.Class    (lift)
import           Control.Monad.Trans.State    (StateT, evalStateT, get, put)
import           Control.Newtype.Generics     (Newtype)
import qualified Control.Newtype.Generics     as Newtype
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Bifunctor               (second)
import           Data.Monoid                  ((<>))
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import qualified Data.Text.Internal.Search    as Text
import qualified Data.Text.IO                 as Text
import           Data.Time.Units              (TimeUnit)
import           Language.Haskell.Interpreter (CompilationError (RawError), InterpreterError (CompilationErrors),
                                               InterpreterResult (InterpreterResult), SourceCode, avoidUnsafe, runghc)
import           System.Directory             (removeFile)
import           System.FilePath              ((</>))
import           System.IO                    (Handle, hFlush)
import           System.IO.Temp               (getCanonicalTemporaryDirectory, openTempFile)
import           System.IO.Temp.Extras        (withSystemTempFile)
import           System.Process               (cwd, proc, readProcessWithExitCode)

runscript
    :: (Show t, TimeUnit t, MonadMask m, MonadIO m, MonadError InterpreterError m)
    => Handle
    -> FilePath
    -> t
    -> Text
    -> m (InterpreterResult String)
runscript handle file timeout script = do
    liftIO $ Text.hPutStr handle script
    liftIO $ hFlush handle
    runghc timeout [] file

runHaskell :: (Show t, TimeUnit t, MonadIO m, MonadError InterpreterError m, MonadMask m)
    => t -> SourceCode
    -> m (InterpreterResult RunResult)
runHaskell t source = do
    avoidUnsafe source
    withSystemTempFile "Main.hs" $ \file handle ->
        (fmap . fmap) (RunResult . Text.pack)
        . runscript handle file t
        . Newtype.unpack $ source

-- Not implemented yet but this will turn a marlowe script into Haskell code
mkRunMarlowe :: Text -> Text
mkRunMarlowe script = script <> "\n\nmain :: IO ()" <> "\nmain = putStrLn $ prettyPrintContract contract"


