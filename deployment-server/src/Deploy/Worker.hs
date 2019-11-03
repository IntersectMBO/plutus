{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Deploy.Worker where

import           Control.Concurrent.Chan      (Chan, readChan)
import           Control.Exception            (SomeException, displayException, handle)
import           Control.Monad                (forever, void)
import           Control.Monad.Except         (ExceptT (ExceptT), MonadError, runExceptT, throwError)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import           Control.Newtype.Generics     (unpack)
import qualified Data.ByteString.Char8        as BS
import qualified Data.ByteString.Lazy.Char8   as LBS
import           Data.Char                    (isSpace)
import           Data.List                    (dropWhileEnd, isSuffixOf)
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           Deploy.Types                 (Options (Options, configDir, deploymentName, environment, githubToken, include, stateFile))
import qualified GitHub
import           GitHub.Data.Webhooks.Events  (PullRequestEvent (evPullReqPayload))
import           GitHub.Data.Webhooks.Payload (HookPullRequest (whPullReqBase), PullRequestTarget (whPullReqTargetRef))
import           System.Directory             (listDirectory)
import           System.Exit                  (ExitCode (ExitFailure, ExitSuccess))
import           System.IO.Temp               (withSystemTempDirectory)
import           System.Process.Typed         (proc, readProcess, setWorkingDir)

data DeploymentError
    = CommandError Text
    | GitHubError GitHub.Error
    deriving (Show)

data AZ = A | B

runWorker :: Chan PullRequestEvent -> Options -> IO ()
runWorker chan options =
    forever $ do
        event <- readChan chan
        deploy event options

deploy :: PullRequestEvent -> Options -> IO ()
deploy event Options {..} =
    withSystemTempDirectory "deployment" $ \tempDir -> do
            let ref = Text.unpack . whPullReqTargetRef . whPullReqBase . evPullReqPayload $ event
                auth = mkToken githubToken
            putStrLn $ "Deploy origin/" <> ref
            overallResult <- runExceptT $ do
                  deployment <- ExceptT . GitHub.executeRequest auth $ createGithubDeploymentRequest ref environment
                  deploymentResult <- runExceptT $ runDeployment tempDir ref
                  void $ ExceptT . GitHub.executeRequest auth $ completeGithubDeploymentRequest deployment deploymentResult
                  pure deploymentResult
            putStrLn $ case overallResult of
                    Left err              -> "github request failed with: " <> show err
                    Right (Left err)      -> "deployment failed with: " <> show err
                    Right (Right gitHead) -> Text.unpack $ "successfully deployed: " <> gitHead
  where
    mkToken = GitHub.OAuth . BS.pack . Text.unpack . unpack
    rstrip = dropWhileEnd isSpace
    isJson = isSuffixOf "json"
    runDeployment tempDir ref = do
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
                      void $ runIn tempDir "git" ["clone", "https://github.com/input-output-hk/plutus.git"]
                      void $ runIn plutusDir "git" ["checkout", "origin/" <> ref]
                      (_, gitHeadStdout, _) <- runIn plutusDir "git" ["rev-parse", "HEAD"]
                      let gitHead = Text.pack . rstrip . LBS.unpack $ gitHeadStdout
                      jsonFiles <- filter isJson <$> liftIO (listDirectory configDir)
                      -- we copy from the configDir in case someone has tried to be nasty by providing
                      -- configDir like "/etc/passwd /proper/config/dir", this means configDir must be
                      -- a proper directory otherwise runIn will fail
                      void $ runIn configDir "cp" $ ["-p"] <> jsonFiles <> [nixopsDir]
                      liftIO $ putStrLn $ "deploy " <> (Text.unpack . unpack) deploymentName
                      void $ runIn nixopsDir "nixops" $ ["modify", "./default.nix", "./network.nix"] <> args
                      -- We do a rolling deploy, if availability zone A fails to deploy or health check fails then we will
                      -- investigate and roll forward, rather than rolling back
                      void $ runIn nixopsDir "nixops" $ ["deploy", "--include", "playgroundA", "marlowePlaygroundA"] <> args
                      checkHealth nixopsDir A environment
                      void $ runIn nixopsDir "nixops" $ ["deploy", "--include", "playgroundB", "marlowePlaygroundB"] <> args
                      checkHealth nixopsDir B environment
                      pure gitHead

checkHealth :: (MonadIO m, MonadError DeploymentError m) => FilePath -> AZ -> String -> m ()
checkHealth dir A environment = do
    void $ runIn dir "curl" ["--max-time", "10", "http://marlowe-a.internal." <> environment <> ".plutus.iohkdev.io/api/health"]
    void $ runIn dir "curl" ["--max-time", "10", "http://playground-a.internal." <> environment <> ".plutus.iohkdev.io/api/health"]
    liftIO $ putStrLn "health check success"
checkHealth dir B environment = do
    void $ runIn dir "curl" ["--max-time", "10", "http://marlowe-b.internal." <> environment <> ".plutus.iohkdev.io/api/health"]
    void $ runIn dir "curl" ["--max-time", "10", "http://playground-b.internal." <> environment <> ".plutus.iohkdev.io/api/health"]
    liftIO $ putStrLn "health check success"

runIn :: (MonadIO m, MonadError DeploymentError m) => FilePath -> String -> [String] -> m (ExitCode, LBS.ByteString, LBS.ByteString)
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
        otherErrors :: SomeException -> IO (ExitCode, LBS.ByteString, LBS.ByteString)
        otherErrors e = pure (ExitFailure 1, mempty, LBS.pack (displayException e))

createGithubDeploymentRequest :: String -> String -> GitHub.Request 'GitHub.RW (GitHub.Deployment String)
createGithubDeploymentRequest ref environment =
    let deployment = GitHub.CreateDeployment
            { createDeploymentRef = Text.pack ref
            , createDeploymentTask = Nothing
            , createDeploymentAutoMerge = Just False
            -- our CI is set up so that after a PR is merged Hydra and buildkite run again on master
            -- these jobs are effictively no-ops but it means that creating a deployment fails because
            -- they are in the 'pending' state right after the merge when this request is sent
            -- we therefore ignore all contexts and rely on not being allowed to merge until the statuses
            -- are green
            , createDeploymentRequiredContexts = Just mempty
            -- despite being `Maybe a` this fails if the value is `Nothing`
            , createDeploymentPayload = Just ""
            , createDeploymentEnvironment = Just $ Text.pack environment
            , createDeploymentDescription = Just "Deploy Playgrounds"
            }
    in
        GitHub.createDeploymentR "input-output-hk" "plutus" deployment


completeGithubDeploymentRequest :: GitHub.Deployment String -> Either DeploymentError b -> GitHub.Request 'GitHub.RW GitHub.DeploymentStatus
completeGithubDeploymentRequest deployment result =
    let dId = GitHub.deploymentId deployment
        deploymentStatus = case result of
                            Right _ -> GitHub.CreateDeploymentStatus
                                            GitHub.DeploymentStatusSuccess
                                            Nothing
                                            (Just "Deployed Successfully")
                            Left err -> GitHub.CreateDeploymentStatus
                                            GitHub.DeploymentStatusFailure
                                            Nothing
                                            -- description is limited to 140 characters
                                            (Just . Text.pack $ "Deployment failed with " <> take 117 (show err))
    in
        GitHub.createDeploymentStatusR "input-output-hk" "plutus" dId deploymentStatus
