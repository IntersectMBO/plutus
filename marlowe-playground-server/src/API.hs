{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators              #-}
module API where

import           Control.Newtype.Generics                         (Newtype)
import           Data.Aeson                                       (FromJSON, ToJSON)
import           Data.Text                                        (Text)
import           GHC.Generics                                     (Generic)
import           Language.Haskell.Interpreter                     (InterpreterError, InterpreterResult, SourceCode)
import qualified Language.Marlowe                                 as M
import qualified Language.Marlowe.ACTUS.Definitions.ContractTerms as CT
import qualified Marlowe.Symbolic.Types.Request                   as MSReq
import qualified Marlowe.Symbolic.Types.Response                  as MSRes
import           Servant.API                                      ((:<|>), (:>), Get, Header, JSON, NoContent, Post,
                                                                   ReqBody)

type API
   = "contract" :> "haskell" :> ReqBody '[ JSON] SourceCode :> Post '[ JSON] (Either InterpreterError (InterpreterResult RunResult))
     :<|> "health" :> Get '[ JSON] ()
     :<|> "actus" :> "generate" :> ReqBody '[ JSON] CT.ContractTerms :> Post '[ JSON] String
     :<|> "actus" :> "generate-static" :> ReqBody '[ JSON] CT.ContractTerms :> Post '[ JSON] String
     :<|> "analyse" :> ReqBody '[ JSON] CheckForWarnings :> Post '[ JSON] MSRes.Result

data CheckForWarnings = CheckForWarnings String String String
   deriving (Generic, ToJSON, FromJSON)

type MarloweSymbolicAPI = "marlowe-analysis" :> Header "X-Amz-Invocation-Type" Text :> Header "x-api-key" Text :> ReqBody '[JSON] MSReq.Request :> Post '[JSON] MSRes.Response

newtype RunResult = RunResult Text
   deriving stock (Show, Eq, Generic)
   deriving newtype (ToJSON, FromJSON)
   deriving anyclass (Newtype)
