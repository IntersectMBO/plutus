{-# LANGUAGE TypeApplications #-}

module Playground.Server where

import           Data.Proxy        (Proxy (Proxy))
import           Playground.API    (Evaluation, API, SourceCode)
import           Servant.API       ((:<|>) ((:<|>)), NoContent (NoContent))
import           Servant.Server    (Application, Handler, Server, serve)
import           Wallet.UTXO.Types (Blockchain)

acceptSourceCode :: SourceCode -> Handler NoContent
acceptSourceCode _ = pure NoContent

runFunction :: Evaluation -> Handler Blockchain
runFunction _ = pure []

handlers :: Server API
handlers = acceptSourceCode :<|> runFunction

api :: Proxy API
api = Proxy

app :: Application
app = serve api handlers
