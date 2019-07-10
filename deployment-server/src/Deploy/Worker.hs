{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Deploy.Worker where

import           Control.Concurrent.Chan      (Chan, readChan)
import           Control.Exception            (SomeException, displayException, handle)
import           Control.Monad                (forever, void)
import           Control.Monad.Except         (MonadError, runExceptT, throwError)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import           Control.Monad.Reader         (runReaderT)
import           Control.Newtype.Generics     (unpack)
import qualified Data.ByteString.Lazy.Char8   as BS
import           Data.Char                    (isSpace)
import           Data.List                    (dropWhileEnd, isSuffixOf)
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           Deploy.Types                 (Options (Options, configDir, deploymentName, environment, include, slackChannel, stateFile),
                                               SlackChannel)
import           GitHub.Data.Webhooks.Events  (PullRequestEvent (evPullReqPayload))
import           GitHub.Data.Webhooks.Payload (HookPullRequest (whPullReqBase), PullRequestTarget (whPullReqTargetRef))
import           System.Directory             (listDirectory)
import           System.Exit                  (ExitCode (ExitFailure, ExitSuccess))
import           System.IO.Temp               (withSystemTempDirectory)
import           System.Process.Typed         (proc, readProcess, setWorkingDir)
import           Web.Slack                    (SlackConfig, chatPostMessage)
import           Web.Slack.Chat               (mkPostMsgReq)

newtype DeploymentError
    = CommandError Text
    deriving (Show)

data AZ = A | B

runWorker :: Chan PullRequestEvent -> Options -> SlackConfig -> IO ()
runWorker chan options slackConfig =
    forever $ do
        event <- readChan chan
        deploy event options slackConfig

deploy :: PullRequestEvent -> Options -> SlackConfig -> IO ()
deploy event Options {..} slackConfig =
    withSystemTempDirectory "deployment" $ \tempDir -> do
            let plutusDir = tempDir <> "/plutus"
                nixopsDir = plutusDir <> "/deployment/nixops"
                extraIncludesString = fmap (\s -> "-I" <> s) include
                args =
                      extraIncludesString <>
                      [ "-s"
                      , stateFile
                      , "-d"
                      , (Text.unpack . unpack) deploymentName
                      ]
                ref = Text.unpack . whPullReqTargetRef . whPullReqBase . evPullReqPayload $ event
            putStrLn $ "Deploy origin/" <> ref
            result <- runExceptT $ do
              void $ runIn tempDir "git" ["clone", "https://github.com/input-output-hk/plutus.git"]
              void $ runIn plutusDir "git" ["checkout", "origin/" <> ref]
              (_, gitHeadStdout, _) <- runIn plutusDir "git" ["rev-parse", "HEAD"]
              let gitHead = Text.pack . rstrip . BS.unpack $ gitHeadStdout
              jsonFiles <- filter isJson <$> liftIO (listDirectory configDir)
              -- we copy from the configDir in case someone has tried to be nasty by providing
              -- configDir like "/etc/passwd /proper/config/dir", this means configDir must be
              -- a proper directory otherwise runIn will fail
              void $ runIn configDir "cp" $ ["-p"] <> jsonFiles <> [nixopsDir]
              liftIO $ putStrLn $ "deploy " <> (Text.unpack . unpack) deploymentName
              void $ runIn nixopsDir "nixops" $ ["modify", "./default.nix", "./network.nix"] <> args
              -- We do a rolling deploy, if availability zone A fails to deploy or health check fails then we will
              -- investigate and roll forward, rather than rolling back
              void $ runIn nixopsDir "nixops" $ ["deploy", "--include", "playgroundA", "--include", "marlowePlaygroundA"] <> args
              checkHealth nixopsDir A environment
              void $ runIn nixopsDir "nixops" $ ["deploy", "--include", "playgroundB", "--include", "marlowePlaygroundB"] <> args
              checkHealth nixopsDir B environment
              pure gitHead
            putStrLn $ "finished deployment with result: " <> show result
            alert slackConfig slackChannel (showResult result)
  where
    rstrip = dropWhileEnd isSpace
    isJson = isSuffixOf "json"

checkHealth :: (MonadIO m, MonadError DeploymentError m) => FilePath -> AZ -> String -> m ()
checkHealth dir A environment = do
    void $ runIn dir "curl" ["--max-time", "10", "http://marlowe-a.internal." <> environment <> ".plutus.iohkdev.io/api/health"]
    void $ runIn dir "curl" ["--max-time", "10", "http://playground-a.internal." <> environment <> ".plutus.iohkdev.io/api/health"]
    liftIO $ putStrLn "health check success"
checkHealth dir B environment = do
    void $ runIn dir "curl" ["--max-time", "10", "http://marlowe-b.internal." <> environment <> ".plutus.iohkdev.io/api/health"]
    void $ runIn dir "curl" ["--max-time", "10", "http://playground-b.internal." <> environment <> ".plutus.iohkdev.io/api/health"]
    liftIO $ putStrLn "health check success"

runIn :: (MonadIO m, MonadError DeploymentError m) => FilePath -> String -> [String] -> m (ExitCode, BS.ByteString, BS.ByteString)
runIn dir bin args = do
    -- For some reason, readProcess fails to deal with all Exceptions, notably when `bin` does not exist
    -- We need to catch this otherwise the worker thread will fail silently and all further requests will
    -- result in a 200 but do nothing
    (exitCode, stdout, stderr) <- liftIO . handle otherErrors . readProcess . setWorkingDir dir . proc bin $ args
    case exitCode of
        ExitSuccess -> pure (exitCode, stdout, stderr)
        ExitFailure n -> do
            liftIO $ print stderr
            throwError $ CommandError ("Failed with exit code " <> (Text.pack . show) n <> " for command: " <> (Text.pack . unwords) ([dir, bin] <> args))
    where
        otherErrors :: SomeException -> IO (ExitCode, BS.ByteString, BS.ByteString)
        otherErrors e = pure (ExitFailure 1, mempty, BS.pack (displayException e))

showResult :: Either DeploymentError Text -> Text
showResult (Left (CommandError err)) = "failed to deploy with error: " <> err
showResult (Right gitHead)           = "git ref " <> gitHead <> " deployed successfully"

alert :: SlackConfig -> SlackChannel -> Text -> IO ()
alert config channel message = do
    let msg =
            mkPostMsgReq (unpack channel) message
    result <- flip runReaderT config $ chatPostMessage msg
    case result of
        Right _ -> pure ()
        Left e  -> putStrLn $ "Failed to notify slack with error " <> show e
