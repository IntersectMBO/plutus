{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}
module Marlowe.Symbolic.Types.API where

import           Marlowe.Symbolic.Types.Response (Response)
import           Servant.API                     ((:<|>), (:>), Get, JSON, NoContent, Post, ReqBody)

type API = "notify" :> ReqBody '[JSON] Response :> Post '[JSON] NoContent
