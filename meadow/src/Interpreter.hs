{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Interpreter where

import           API                          (MeadowError (CompilationErrors, OtherError), RunResult (RunResult),
                                               SourceCode)
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
import           Language.Haskell.Interpreter (CompilationError, runghc)
import           System.Directory             (removeFile)
import           System.FilePath              ((</>))
import           System.IO                    (Handle, hFlush)
import           System.IO.Temp               (getCanonicalTemporaryDirectory, openTempFile)
import           System.IO.Temp.Extras        (withSystemTempFile)
import           System.Process               (cwd, proc, readProcessWithExitCode)

runscript
    :: (MonadMask m, MonadIO m, MonadError [CompilationError] m)
    => Handle
    -> FilePath
    -> Text
    -> m String
runscript handle file script = do
    liftIO $ Text.hPutStr handle script
    liftIO $ hFlush handle
    runghc [] file

avoidUnsafe :: (MonadError MeadowError m) => SourceCode -> m ()
avoidUnsafe s =
    unless (null . Text.indices "unsafe" . Newtype.unpack $ s)
        . throwError
        . OtherError
        $ "Cannot interpret unsafe functions"

runHaskell :: (MonadIO m, MonadError MeadowError m, MonadMask m) => SourceCode -> m RunResult
runHaskell source = do
    avoidUnsafe source
    withSystemTempFile "Main.hs" $ \file handle ->
        fmap (RunResult . Text.pack)
        . mapError CompilationErrors
        . runscript handle file
        . Newtype.unpack $ source

-- Not implemented yet but this will turn a marlowe script into Haskell code
mkRunMarlowe :: Text -> Text
mkRunMarlowe script = script <> "\n\nmain :: IO ()" <> "\nmain = putStrLn $ prettyPrintContract contract"


