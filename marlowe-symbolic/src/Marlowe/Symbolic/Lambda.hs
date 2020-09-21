{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module Marlowe.Symbolic.Lambda where

import           Aws.Lambda
import           Aws.Lambda.Wai          (WaiHandler, waiHandler)
import           Marlowe.Symbolic.Server (initializeApplication, initializeContext)

handler :: WaiHandler ()
handler request context = do
  -- This uses Aws.Lambda.Wai from aws-lambda-haskell-runtime-wai in order to convert the Wai application to Lambda.
  waiHandler initializeApplication request context

generateLambdaDispatcher UseWithAPIGateway defaultDispatcherOptions
