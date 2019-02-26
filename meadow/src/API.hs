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
import           Language.Haskell.Interpreter (CompilationError)
import           Servant.API                  ((:<|>) ((:<|>)), (:>), JSON, Post, ReqBody)

type API
   = "contract" :> "haskell" :> ReqBody '[ JSON] SourceCode :> Post '[ JSON] (Either [CompilationError] RunResult)

newtype SourceCode = SourceCode Text
   deriving stock (Generic)
   deriving newtype (ToJSON, FromJSON)
   deriving anyclass (Newtype)

newtype RunResult = RunResult Text
   deriving stock (Show, Eq, Generic)
   deriving newtype (ToJSON, FromJSON)
   deriving anyclass (Newtype)

data MeadowError
   = CompilationErrors [CompilationError]
   | OtherError Text
   | MeadowTimeout
   deriving stock (Eq, Show, Generic)
   deriving anyclass (ToJSON, FromJSON)
