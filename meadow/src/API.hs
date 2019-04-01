{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators              #-}
module API where

import           Control.Newtype.Generics     (Newtype)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Text                    (Text)
import           GHC.Generics                 (Generic)
import           Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode)
import           Servant.API                  ((:<|>) ((:<|>)), (:>), Get, JSON, Post, ReqBody)

type API
   = "contract" :> "haskell" :> ReqBody '[ JSON] SourceCode :> Post '[ JSON] (Either InterpreterError (InterpreterResult RunResult))
     :<|> "health" :> Get '[ JSON] ()


newtype RunResult = RunResult Text
   deriving stock (Show, Eq, Generic)
   deriving newtype (ToJSON, FromJSON)
   deriving anyclass (Newtype)
