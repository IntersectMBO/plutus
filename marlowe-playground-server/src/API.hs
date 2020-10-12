{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeOperators      #-}

module API where

import qualified Auth
import           Data.Aeson                                       (FromJSON, ToJSON)
import           GHC.Generics                                     (Generic)
import qualified Language.Marlowe.ACTUS.Definitions.ContractTerms as CT
import           Servant.API                                      ((:<|>), (:>), Get, Header, JSON, NoContent, Post,
                                                                   Raw, ReqBody)

type API =
  "actus" :> "generate" :> ReqBody '[JSON] CT.ContractTerms :> Post '[JSON] String
    :<|> "actus" :> "generate-static" :> ReqBody '[JSON] CT.ContractTerms :> Post '[JSON] String
