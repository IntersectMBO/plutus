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
import           GHC.Generics                                     (Generic)
import           Git                                              (gitRev)
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
genActusContract = pure . show . pretty . genFsContract

genActusContractStatic :: ContractTerms -> Handler String
genActusContractStatic = pure . show . pretty . genStaticContract


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

version :: Applicative m => m Text
version = pure gitRev

mhandlers :: Server API
mhandlers = oracle :<|> version :<|> genActusContract :<|> genActusContractStatic

app :: Server Web -> Application
app handlers =
  cors (const $ Just policy) $ serve (Proxy @Web) handlers
  where
    policy =
      simpleCorsResourcePolicy

newtype AppConfig = AppConfig {authConfig :: Auth.Config}

initializeContext :: IO AppConfig
initializeContext = do
  putStrLn "Initializing Context"
  githubClientId <- getEnvOrEmpty "GITHUB_CLIENT_ID"
  githubClientSecret <- getEnvOrEmpty "GITHUB_CLIENT_SECRET"
  jwtSignature <- getEnvOrEmpty "JWT_SIGNATURE"
  frontendURL <- getEnvOrEmpty "FRONTEND_URL"
  cbPath <- getEnvOrEmpty "GITHUB_CALLBACK_PATH"
  let authConfig =
        Auth.Config
          { _configJWTSignature = JWT.hmacSecret jwtSignature,
            _configFrontendUrl = frontendURL,
            _configGithubCbPath = cbPath,
            _configGithubClientId = OAuthClientId githubClientId,
            _configGithubClientSecret = OAuthClientSecret githubClientSecret
          }
  pure $ AppConfig authConfig

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
