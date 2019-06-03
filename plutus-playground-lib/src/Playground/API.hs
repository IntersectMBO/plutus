{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TypeOperators              #-}

module Playground.API where

import           Control.Monad.Trans.Class    (lift)
import           Control.Monad.Trans.State    (StateT, evalStateT, get, put)
import           Data.Aeson                   (FromJSON, ToJSON, Value)
import           Data.Bifunctor               (second)
import qualified Data.ByteString.Lazy         as LBS
import           Data.List.NonEmpty           (NonEmpty ((:|)))
import           Data.Maybe                   (fromMaybe)
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           GHC.Generics                 (Generic)
import           Language.Haskell.Interpreter (CompilationError (CompilationError, RawError), InterpreterResult,
                                               SourceCode, column, filename, row, text)
import qualified Language.Haskell.Interpreter as HI
import qualified Language.Haskell.TH.Syntax   as TH
import           Ledger                       (Blockchain, PubKey, Tx, TxId)
import qualified Ledger.Ada                   as Ada
import           Ledger.Validation            (ValidatorHash, fromSymbol)
import           Ledger.Value                 (TokenName)
import qualified Ledger.Value                 as V
import           Schema                       (SimpleArgumentSchema (SimpleArraySchema, SimpleHexSchema, SimpleIntSchema, SimpleObjectSchema, SimpleStringSchema, SimpleTupleSchema, UnknownSchema, ValueSchema))
import           Servant.API                  (PlainText, (:<|>), (:>), Get, JSON, Post, ReqBody)
import           Text.Read                    (readMaybe)
import           Wallet.Emulator.Types        (EmulatorEvent, Wallet, walletPubKey)
import           Wallet.Graph                 (FlowGraph)

type API
     = "contract" :> ReqBody '[ JSON] SourceCode :> Post '[ JSON] (Either HI.InterpreterError (InterpreterResult CompilationResult))
       :<|> "evaluate" :> ReqBody '[ JSON] Evaluation :> Post '[ JSON] EvaluationResult
       :<|> "health" :> Get '[ JSON] ()

data KnownCurrency = KnownCurrency
    { hash         :: ValidatorHash
    , friendlyName :: String
    , knownTokens  :: NonEmpty TokenName
    }
    deriving (Eq, Show, Generic, ToJSON, FromJSON)

adaCurrency :: KnownCurrency
adaCurrency = KnownCurrency
    { hash = fromSymbol Ada.adaSymbol
    , friendlyName = "Ada"
    , knownTokens = Ada.adaToken :| []
    }

--------------------------------------------------------------------------------

newtype Fn = Fn Text
  deriving stock (Eq, Show, Generic, TH.Lift)
  deriving newtype (ToJSON, FromJSON)

data Expression
  = Action
    { function  :: Fn
    , wallet    :: Wallet
    , arguments :: [Value]
    }
  | Wait { blocks :: Int }
  deriving (Show, Generic, ToJSON, FromJSON)

type Program = [Expression]

data SimulatorWallet = SimulatorWallet
  { simulatorWalletWallet  :: Wallet
  , simulatorWalletBalance :: V.Value
  }
  deriving stock (Show, Generic, Eq)
  deriving anyclass (ToJSON, FromJSON)

data Evaluation = Evaluation
  { wallets    :: [SimulatorWallet]
  , program    :: Program
  , sourceCode :: SourceCode
  , blockchain :: Blockchain
  }
  deriving (Generic, ToJSON, FromJSON)

pubKeys :: Evaluation -> [PubKey]
pubKeys Evaluation{..} = walletPubKey . simulatorWalletWallet <$> wallets

data EvaluationResult = EvaluationResult
  { resultBlockchain  :: [[(TxId, Tx)]] -- Blockchain annotated with hashes.
  , resultGraph       :: FlowGraph
  , emulatorLog       :: [EmulatorEvent]
  , fundsDistribution :: [SimulatorWallet]
  , walletKeys        :: [(PubKey,Wallet)]
  }
  deriving (Generic, ToJSON)

data CompilationResult = CompilationResult
  { functionSchema  :: [FunctionSchema SimpleArgumentSchema]
  , knownCurrencies :: [KnownCurrency]
  }
  deriving (Show, Generic, ToJSON)

data FunctionSchema a = FunctionSchema
  { functionName   :: Fn
  , argumentSchema :: [a]
  } deriving (Eq, Show, Generic, ToJSON, FromJSON, Functor)

isSupportedByFrontend :: SimpleArgumentSchema -> Bool
isSupportedByFrontend SimpleIntSchema = True
isSupportedByFrontend SimpleStringSchema = True
isSupportedByFrontend SimpleHexSchema = True
isSupportedByFrontend (ValueSchema subSchema) =
    all isSupportedByFrontend (snd <$> subSchema)
isSupportedByFrontend (SimpleObjectSchema subSchema) =
    all isSupportedByFrontend (snd <$> subSchema)
isSupportedByFrontend (SimpleArraySchema subSchema) =
    isSupportedByFrontend subSchema
isSupportedByFrontend (SimpleTupleSchema (subSchemaX, subSchemaY)) =
    all isSupportedByFrontend [subSchemaX, subSchemaY]
isSupportedByFrontend (UnknownSchema _ _) = False
------------------------------------------------------------

data PlaygroundError
  = CompilationErrors [CompilationError]
  | InterpreterError HI.InterpreterError
  | FunctionSchemaError
  | DecodeJsonTypeError String String
  | PlaygroundTimeout
  | OtherError String
  deriving stock (Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

parseErrorsText :: Text -> [CompilationError]
parseErrorsText input = parseErrorText <$> Text.splitOn "\n\n" input

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
