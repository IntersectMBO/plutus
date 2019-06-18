{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
module Deploy.Worker where

import           Control.Concurrent.Chan     (Chan, readChan)
import           Control.Monad               (forever)
import           Control.Monad.IO.Class      (liftIO)
import           Control.Monad.Reader        (runReaderT)
import           Control.Newtype.Generics    (unpack)
import qualified Data.ByteString.Lazy.Char8  as BS
import           Data.Char                   (isSpace)
import           Data.List                   (dropWhileEnd, isSuffixOf)
import           Data.Text                   (Text)
import qualified Data.Text                   as Text
import           Deploy.Types                (Deployment, Options (..), SlackChannel)
import           GitHub.Data.Webhooks.Events (PullRequestEvent)
import           System.Directory            (listDirectory)
import           System.Exit                 (ExitCode (ExitFailure, ExitSuccess))
import           System.IO.Temp              (withSystemTempDirectory)
import           System.Process.Typed        (proc, readProcess, runProcess, setEnv, setWorkingDir)
import           Web.Slack                   (SlackConfig, chatPostMessage)
import           Web.Slack.Chat              (mkPostMsgReq)

runWorker :: Chan PullRequestEvent -> Options -> SlackConfig -> IO ()
runWorker chan options slackConfig = forever $ do
    event <- readChan chan
    deploy event options slackConfig

deploy :: PullRequestEvent -> Options -> SlackConfig -> IO ()
deploy event Options{..} slackConfig = withSystemTempDirectory "deployment" $ \tempDir -> liftIO $ do
    let plutusDir = tempDir <> "/plutus"
        nixopsDir = plutusDir <> "/deployment/nixops"
    putStrLn "Deploy origin/master"
    runIn tempDir "git" ["clone", "https://github.com/input-output-hk/plutus.git"]
    runIn plutusDir "git" ["checkout", "origin/master"]
    (_, stdout', _) <- readIn plutusDir "git" ["rev-parse", "HEAD"]
    let gitHead = rstrip . BS.unpack $ stdout'
        extraIncludesString = fmap (\s -> "-I" <> s) include
        args = extraIncludesString <> ["-s", stateFile, "-d", (Text.unpack . unpack) deploymentName]
    jsonFiles <- filter isJson <$> listDirectory configDir
    -- we copy from the configDir in case someone has tried to be nasty by providing configDir like "/etc/passwd /proper/config/dir"
    -- this means configDir must be a proper directory otherwise runIn will fail
    runIn configDir "cp" $ ["-p"] <> jsonFiles <> [nixopsDir]
    putStrLn $ "deploy " <> (Text.unpack . unpack) deploymentName
    runIn nixopsDir "nixops" $ ["modify", "./default.nix", "./network.nix"] <> args
    exitCode <- runIn nixopsDir "nixops" $ ["deploy", "--exclude", "nixops"] <> args
    putStrLn $ "finished deployment of " <> gitHead <> " with exit code " <> show exitCode
    alert slackConfig slackChannel (Text.pack gitHead) exitCode
    where
        runIn dir bin = runProcess . setWorkingDir dir . proc bin
        readIn dir bin = readProcess . setWorkingDir dir . proc bin
        rstrip = dropWhileEnd isSpace
        isJson = isSuffixOf "json"

alert :: SlackConfig -> SlackChannel -> Text -> ExitCode -> IO ()
alert config channel gitHead exitCode = do
    let msg = mkPostMsgReq (unpack channel) $ case exitCode of
                                        ExitSuccess   -> "origin/master (" <> gitHead <> ") deployed successfully"
                                        ExitFailure i -> "failed to deploy origin/master (" <> gitHead <> ")"
    result <- flip runReaderT config $ chatPostMessage msg
    case result of
      Right _ -> pure ()
      Left e  -> putStrLn $ "Failed to notify slack with error " <> show e
