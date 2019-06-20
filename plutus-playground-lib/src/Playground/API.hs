{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}

module Playground.API where

import           Control.Monad.Trans.Class    (lift)
import           Control.Monad.Trans.State    (StateT, evalStateT, get, put)
import           Data.Aeson                   (FromJSON, ToJSON, Value)
import           Data.Bifunctor               (second)
import           Data.List.NonEmpty           (NonEmpty ((:|)))
import           Data.Maybe                   (fromMaybe)
import           Data.Morpheus.Kind           (KIND, OBJECT, SCALAR, WRAPPER)
import           Data.Morpheus.Types          (GQLScalar (parseValue, serialize), GQLType)
import qualified Data.Morpheus.Types          as Morpheus
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
import           Servant.API                  ((:<|>), (:>), Get, JSON, Post, ReqBody)
import           Text.Read                    (readMaybe)
import           Wallet.Emulator.Types        (EmulatorEvent, Wallet, walletPubKey)
import           Wallet.Graph                 (FlowGraph)

type API
     = "contract" :> ReqBody '[ JSON] SourceCode :> Post '[ JSON] (Either HI.InterpreterError (InterpreterResult CompilationResult))
       :<|> "evaluate" :> ReqBody '[ JSON] Evaluation :> Post '[ JSON] EvaluationResult
       :<|> "health" :> Get '[ JSON] ()

data KnownCurrency =
    KnownCurrency
        { hash         :: ValidatorHash
        , friendlyName :: Text
        -- , knownTokens  :: NonEmpty TokenName
        , knownTokens  :: [TokenName] -- TODO Restore NonEmpty
        }
    deriving (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON, GQLType)

type instance KIND KnownCurrency = OBJECT

adaCurrency :: KnownCurrency
adaCurrency =
    KnownCurrency
        { hash = fromSymbol Ada.adaSymbol
        , friendlyName = "Ada"
        , knownTokens = [Ada.adaToken] -- TODO Restore NonEmpty
        --, knownTokens = Ada.adaToken :| []
        }

--------------------------------------------------------------------------------
newtype Fn =
    Fn Text
    deriving (Eq, Show, Generic, TH.Lift)
    deriving anyclass (GQLType)
    deriving newtype (ToJSON, FromJSON)

type instance KIND Fn = SCALAR

instance GQLScalar Fn where
    parseValue (Morpheus.String str) = Right $ Fn str
    parseValue scalar =
        Left $ "Expected Fn string, got: " <> Text.pack (show scalar)
    serialize (Fn str) = Morpheus.String str

data Expression
    = Action
          { function  :: Fn
          , wallet    :: Wallet
          , arguments :: [Value]
          }
    | Wait
          { blocks :: Int
          }
    deriving (Show, Generic, ToJSON, FromJSON)

type Program = [Expression]

data SimulatorWallet =
    SimulatorWallet
        { simulatorWalletWallet  :: Wallet
        , simulatorWalletBalance :: V.Value
        }
    deriving (Show, Generic, Eq)
    deriving anyclass (ToJSON, FromJSON)

data Evaluation =
    Evaluation
        { wallets    :: [SimulatorWallet]
        , program    :: Program
        , sourceCode :: SourceCode
        , blockchain :: Blockchain
        }
    deriving (Generic, ToJSON, FromJSON)

pubKeys :: Evaluation -> [PubKey]
pubKeys Evaluation {..} = walletPubKey . simulatorWalletWallet <$> wallets

data EvaluationResult =
    EvaluationResult
        { resultBlockchain  :: [[(TxId, Tx)]] -- Blockchain annotated with hashes.
        , resultGraph       :: FlowGraph
        , emulatorLog       :: [EmulatorEvent]
        , fundsDistribution :: [SimulatorWallet]
        , walletKeys        :: [(PubKey, Wallet)]
        }
    deriving (Generic, ToJSON, GQLType)

type instance KIND EvaluationResult = OBJECT
type instance KIND (TxId, Tx) = WRAPPER

newtype SchemaText =
    SchemaText Text
    deriving (Show, Generic, Eq, Ord)
    deriving anyclass (FromJSON, ToJSON, GQLType)

type instance KIND SchemaText = SCALAR

instance GQLScalar SchemaText where
    parseValue (Morpheus.String str) = Right $ SchemaText str
    parseValue scalar =
        Left $ "Expected SchemaText string, got: " <> Text.pack (show scalar)
    serialize (SchemaText str) = Morpheus.String str

data CompilationResult =
    CompilationResult
        { functionSchema  :: SchemaText
        , knownCurrencies :: [KnownCurrency]
        }
    deriving (Show, Generic)
    deriving anyclass (FromJSON, ToJSON, GQLType)

type instance KIND CompilationResult = OBJECT

data FunctionSchema a =
    FunctionSchema
        { functionName   :: Fn
        , argumentSchema :: [a]
        }
    deriving (Eq, Show, Generic, ToJSON, FromJSON, Functor)

------------------------------------------------------------
data PlaygroundError
    = CompilationErrors [CompilationError]
    | InterpreterError HI.InterpreterError
    | FunctionSchemaError
    | DecodeJsonTypeError String String
    | PlaygroundTimeout
    | OtherError String
    deriving (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

parseErrorsText :: Text -> [CompilationError]
parseErrorsText input = parseErrorText <$> Text.splitOn "\n\n" input

parseErrorText :: Text -> CompilationError
parseErrorText input =
    fromMaybe (RawError input) $
    flip evalStateT input $ do
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
