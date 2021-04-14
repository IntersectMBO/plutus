{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeOperators      #-}

module API where

import qualified Auth
import           Data.Aeson                                       (FromJSON, ToJSON, Value)
import           Data.Text                                        (Text)
import           GHC.Generics                                     (Generic)
import qualified Language.Marlowe.ACTUS.Definitions.ContractTerms as CT
import           Servant.API                                      (Capture, Get, Header, JSON, NoContent, PlainText,
                                                                   Post, Raw, ReqBody, (:<|>), (:>))

type API
     = "oracle" :> Capture "exchange" String :> Capture "pair" String :> Get '[JSON] Value
       :<|> "actus" :> ("generate" :> ReqBody '[ JSON] CT.ContractTerms :> Post '[ JSON] String
                        :<|> "generate-static" :> ReqBody '[ JSON] CT.ContractTerms :> Post '[ JSON] String)
