{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module Lambda where

import           Aws.Lambda
import           Aws.Lambda.Wai (WaiHandler, waiHandler)
import           Data.IORef     (readIORef)
import           Server         (AppConfig, initializeApplication, initializeServerContext)

initializeContext :: IO AppConfig
initializeContext = initializeServerContext Nothing

handler :: WaiHandler AppConfig
handler request context = do
  -- This application config will be preserved while the Lambda is warm
  appConfig :: AppConfig <- readIORef $ customContext context
  putStrLn "Found Context, running app"

  -- This uses Aws.Lambda.Wai from aws-lambda-haskell-runtime-wai in order to convert the Wai application to Lambda.
  waiHandler (initializeApplication appConfig) request context

generateLambdaDispatcher UseWithAPIGateway defaultDispatcherOptions
