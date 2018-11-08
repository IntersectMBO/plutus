{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TypeOperators              #-}

module Playground.API where

import           Control.Arrow              (left)
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.State  (StateT, evalStateT, get, put)
import           Control.Newtype.Generics   (Newtype)
import           Data.Aeson                 (FromJSON (parseJSON), ToJSON (toJSON), Value, withText)
import qualified Data.Aeson                 as JSON
import           Data.Bifunctor             (second)
import qualified Data.ByteString.Base64     as Base64
import           Data.ByteString.Lazy       (fromStrict, toStrict)
import           Data.Map                   (Map)
import           Data.Maybe                 (catMaybes, fromJust, fromMaybe)
import           Data.Swagger               (Schema, ToSchema)
import           Data.Text                  (Text)
import qualified Data.Text                  as Text
import           Data.Text.Encoding         (decodeUtf8, decodeUtf8', encodeUtf8)
import           GHC.Generics               (Generic)
import qualified Language.Haskell.TH.Syntax as TH
import           Network.HTTP.Media         ((//), (/:))
import           Servant.API                ((:<|>), (:>), Accept (contentType), Capture, JSON, MimeRender (mimeRender),
                                             MimeUnrender (mimeUnrender), NoContent, Post, ReqBody)
import           Text.Read                  (readMaybe)
import           Wallet.Emulator.Types      (Wallet)
import           Wallet.UTXO.Types          (Blockchain)

type API
   = "contract" :> ReqBody '[ JSON] SourceCode :> Post '[ JSON] (Either [CompilationError] [FunctionSchema])
     :<|> "evaluate" :> ReqBody '[ JSON] Evaluation :> Post '[ JSON] Blockchain

newtype SourceCode = SourceCode Text
  deriving stock (Generic)
  deriving newtype (ToJSON, FromJSON)
  deriving anyclass (Newtype)

newtype FunctionsSchema = FunctionsSchema [(Fn, Text)]
  deriving stock (Generic)
  deriving newtype (ToJSON, FromJSON)

newtype Fn = Fn Text
  deriving stock (Show, Generic, TH.Lift)
  deriving newtype (ToJSON, FromJSON)

data Expression = Expression
  { function  :: Fn
  , wallet    :: Wallet
  , arguments :: [Value]
  }
  deriving (Generic, ToJSON, FromJSON)

type Program = [Expression]

data Evaluation = Evaluation
  { wallets    :: [(Wallet, Integer)]
  , program    :: Program
  , sourceCode :: SourceCode
  , blockchain :: Blockchain
  }
  deriving (Generic, ToJSON, FromJSON)

data FunctionSchema = FunctionSchema
  { functionName   :: Fn
  , argumentSchema :: [Schema]
  }
  deriving (Show, Generic, ToJSON)


------------------------------------------------------------
data CompilationError = RawError Text | CompilationError
  { filename :: !Text
  , row      :: !Int
  , column   :: !Int
  , text     :: ![Text]
  } deriving stock (Show, Eq, Generic)
    deriving anyclass (ToJSON)

parseErrorText :: Text -> CompilationError
parseErrorText input =
  fromMaybe (RawError input) $ flip evalStateT input $ do
    filename <- consumeTo ":"
    rowStr <- consumeTo ":"
    columnStr <- consumeTo ":"
    text <- Text.lines <$> consume
  --
    row <- lift $ readMaybe $ Text.unpack rowStr
    column <- lift $ readMaybe $ Text.unpack columnStr
    pure CompilationError {..}

consumeTo :: Monad m => Text -> StateT Text m Text
consumeTo needle = do
  (before, after) <- breakWith needle <$> get
  put after
  pure before

consume :: (Monad m, Monoid s) => StateT s m s
consume = get <* put mempty

-- | Light `Data.Text.breakOn`, but consumes the breakpoint text (the 'needle').
breakWith :: Text -> Text -> (Text, Text)
breakWith needle = second (Text.drop 1) . Text.breakOn needle
