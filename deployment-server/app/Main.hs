{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Main where

import           Control.Concurrent       (forkIO)
import           Control.Concurrent.Chan  (newChan)
import           Control.Monad            (void)
import           Control.Newtype.Generics (unpack)
import           Data.Aeson               (eitherDecodeFileStrict)
import qualified Data.ByteString.Char8    as BS
import qualified Data.Text                as Text
import           Deploy.Server            (app)
import           Deploy.Types             (Options (..), Secrets (..))
import           Deploy.Worker            (runWorker)
import           Network.Wai.Handler.Warp (run)
import           Options.Generic          (getRecord)
import           Servant.GitHub.Webhook   (gitHubKey)
import           System.Exit              (ExitCode (ExitFailure), exitWith)
import           System.IO                (BufferMode (LineBuffering), hPutStrLn, hSetBuffering, stderr, stdout)

main :: IO ()
main = do
    -- When using systemd, journald does something weird with buffering so let's force it to be line buffered
    hSetBuffering stdout LineBuffering
    hSetBuffering stderr LineBuffering
    options@Options {..} <- getRecord "Plutus CD Server"
    eJSON <- eitherDecodeFileStrict keyfile
    case eJSON of
        Left err -> do
            hPutStrLn stderr $ "failed to load keyfile with error " <> err
            exitWith $ ExitFailure 2
        Right Secrets {..} -> do
            chan <- newChan
            void . forkIO $ runWorker chan options
            putStrLn $ "start listening on port " <> show port
            run port $ app ref chan (gitHubKey . pure . BS.pack . Text.unpack . unpack $ githubWebhookKey)
