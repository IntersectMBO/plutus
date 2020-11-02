{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures       #-}
{-# OPTIONS_GHC -fno-warn-unused-matches       #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing       #-}
module Playground.Lambda where

import           Aws.Lambda
import           Aws.Lambda.Wai    (WaiHandler, waiHandler)
import           Data.IORef        (readIORef)
import           Playground.Server (AppConfig, initializeApplication, initializeContext)

handler :: WaiHandler AppConfig
handler request context = do
  -- This application config will be preserved while the Lambda is warm
  appConfig :: AppConfig <- readIORef $ customContext context
  putStrLn "Found Context, running app"

  -- This uses Aws.Lambda.Wai from aws-lambda-haskell-runtime-wai in order to convert the Wai application to Lambda.
  waiHandler (initializeApplication appConfig) request context

generateLambdaDispatcher UseWithAPIGateway defaultDispatcherOptions
