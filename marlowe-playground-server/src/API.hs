{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeOperators      #-}

module API where

import qualified Auth
import           Data.Aeson                                       (FromJSON, ToJSON)
import           Data.Text                                        (Text)
import           GHC.Generics                                     (Generic)
import qualified Language.Marlowe.ACTUS.Definitions.ContractTerms as CT
import           Servant.API                                      ((:<|>), (:>), Get, Header, JSON, NoContent,
                                                                   PlainText, Post, Raw, ReqBody)

type API
     = "version" :> Get '[ PlainText, JSON] Text
       :<|> "actus" :> ("generate" :> ReqBody '[ JSON] CT.ContractTerms :> Post '[ JSON] String
                        :<|> "generate-static" :> ReqBody '[ JSON] CT.ContractTerms :> Post '[ JSON] String)
