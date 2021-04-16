{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Server where

import           API
import qualified Auth
import           Auth.Types                                       (OAuthClientId (OAuthClientId),
                                                                   OAuthClientSecret (OAuthClientSecret))
import           Control.Monad.Except                             (ExceptT)
import           Control.Monad.IO.Class                           (MonadIO, liftIO)
import           Control.Monad.Logger                             (LoggingT, MonadLogger, logInfoN, runStderrLoggingT)
import           Control.Monad.Reader                             (ReaderT, runReaderT)
import           Data.Aeson                                       (FromJSON, ToJSON, eitherDecode, encode)
import           Data.Aeson                                       as Aeson
import qualified Data.HashMap.Strict                              as HM
import           Data.Proxy                                       (Proxy (Proxy))
import           Data.String                                      as S
import           Data.Text                                        (Text)
import qualified Data.Text                                        as Text
import qualified Data.Validation                                  as Validation
import           GHC.Generics                                     (Generic)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (ContractTerms)
import           Language.Marlowe.ACTUS.Generator                 (genFsContract, genStaticContract)
import           Language.Marlowe.Pretty                          (pretty)
import           Network.HTTP.Simple                              (getResponseBody, httpJSON)
import           Network.Wai.Middleware.Cors                      (cors, corsRequestHeaders, simpleCorsResourcePolicy)
import           Servant                                          (Application, Handler (Handler), Server, ServerError,
                                                                   hoistServer, serve, (:<|>) ((:<|>)), (:>))
import           System.Environment                               (lookupEnv)
import qualified Web.JWT                                          as JWT

genActusContract :: ContractTerms -> Handler String
genActusContract terms =
    case genFsContract terms of
        -- Should probably send this as a server error and handle it properly on the front end
        Validation.Failure errs -> pure (unlines . (:) "ACTUS Term Validation Failed:" . map ((++) "    " . show) $ errs)
        Validation.Success c -> pure . show . pretty $ c

genActusContractStatic :: ContractTerms -> Handler String
genActusContractStatic terms =
    case genStaticContract terms of
        Validation.Failure errs -> pure (unlines . (:) "ACTUS Term Validation Failed:" . map ((++) "    " . show) $ errs)
        Validation.Success c -> pure . show . pretty $ c

oracle :: MonadIO m => String -> String -> m Value
oracle exchange pair = do
    response <- liftIO (httpJSON (fromString $ "GET https://api.cryptowat.ch/markets/" <> exchange <> "/" <> pair <> "/price"))
    let result = getResponseBody response :: Value
    pure result

liftedAuthServer :: Auth.GithubEndpoints -> Auth.Config -> Server Auth.API
liftedAuthServer githubEndpoints config =
  hoistServer (Proxy @Auth.API) liftAuthToHandler Auth.server
  where
    liftAuthToHandler ::
      ReaderT (Auth.GithubEndpoints, Auth.Config) (LoggingT (ExceptT ServerError IO)) a ->
      Handler a
    liftAuthToHandler =
      Handler . runStderrLoggingT . flip runReaderT (githubEndpoints, config)

type Web = "api" :> (API :<|> Auth.API)

mkHandlers :: (MonadIO m) => AppConfig -> m (Server Web)
mkHandlers AppConfig {..} = do
  githubEndpoints <- liftIO Auth.mkGithubEndpoints
  pure (mhandlers :<|> liftedAuthServer githubEndpoints authConfig)

mhandlers :: Server API
mhandlers = oracle :<|> genActusContract :<|> genActusContractStatic

app :: Server Web -> Application
app handlers =
  cors (const $ Just policy) $ serve (Proxy @Web) handlers
  where
    policy =
      simpleCorsResourcePolicy

newtype AppConfig = AppConfig {authConfig :: Auth.Config}

initializeServerContext :: Maybe FilePath -> IO AppConfig
initializeServerContext secrets = do
  putStrLn "Initializing Context"
  authConfig <- mkAuthConfig secrets
  pure $ AppConfig authConfig

mkAuthConfig :: MonadIO m => Maybe FilePath -> m Auth.Config
mkAuthConfig (Just path) = do
  mConfig <- liftIO $ decodeFileStrict path
  case mConfig of
    Just config -> pure config
    Nothing -> do
      liftIO $ putStrLn $ "failed to decode " <> path
      mkAuthConfig Nothing
mkAuthConfig Nothing = liftIO $ do
  putStrLn "Initializing Context"
  githubClientId <- getEnvOrEmpty "GITHUB_CLIENT_ID"
  githubClientSecret <- getEnvOrEmpty "GITHUB_CLIENT_SECRET"
  jwtSignature <- getEnvOrEmpty "JWT_SIGNATURE"
  frontendURL <- getEnvOrEmpty "FRONTEND_URL"
  cbPath <- getEnvOrEmpty "GITHUB_CALLBACK_PATH"
  pure Auth.Config
          { _configJWTSignature = JWT.hmacSecret jwtSignature,
            _configFrontendUrl = frontendURL,
            _configGithubCbPath = cbPath,
            _configGithubClientId = OAuthClientId githubClientId,
            _configGithubClientSecret = OAuthClientSecret githubClientSecret
          }

getEnvOrEmpty :: String -> IO Text
getEnvOrEmpty name = do
  mEnv <- lookupEnv name
  case mEnv of
    Just env -> pure $ Text.pack env
    Nothing -> do
      putStrLn $ "Warning: " <> name <> " not set"
      pure mempty

initializeApplication :: AppConfig -> IO Application
initializeApplication config = do
  handlers <- mkHandlers config
  pure $ app handlers
