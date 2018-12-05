{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TypeOperators              #-}

module Playground.API where

import           Control.Lens                 (over, _2)
import           Control.Monad.Trans.Class    (lift)
import           Control.Monad.Trans.State    (StateT, evalStateT, get, put)
import           Control.Newtype.Generics     (Newtype, pack, unpack)
import           Data.Aeson                   (FromJSON, ToJSON, Value)
import           Data.Bifunctor               (second)
import qualified Data.HashMap.Strict.InsOrd   as HM
import           Data.Maybe                   (fromMaybe)
import           Data.Swagger                 (ParamSchema (ParamSchema), Referenced (Inline, Ref), Schema (Schema),
                                               SwaggerType (SwaggerInteger, SwaggerObject, SwaggerString))
import qualified Data.Swagger                 as Swagger
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           GHC.Generics                 (Generic)
import qualified Language.Haskell.Interpreter as Hint
import qualified Language.Haskell.TH.Syntax   as TH
import           Ledger.Types                 (Blockchain, PubKey)
import qualified Ledger.Types                 as Ledger
import           Servant.API                  ((:<|>), (:>), JSON, Post, ReqBody)
import           Text.Read                    (readMaybe)
import           Wallet.Emulator.Types        (EmulatorEvent, Wallet)
import           Wallet.Graph                 (FlowGraph)

type API
   = "contract" :> ReqBody '[ JSON] SourceCode :> Post '[ JSON] (Either [CompilationError] [FunctionSchema SimpleArgumentSchema])
     :<|> "evaluate" :> ReqBody '[ JSON] Evaluation :> Post '[ JSON] EvaluationResult

newtype SourceCode = SourceCode Text
  deriving stock (Generic)
  deriving newtype (ToJSON, FromJSON)
  deriving anyclass (Newtype)

newtype Fn = Fn Text
  deriving stock (Show, Generic, TH.Lift)
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

data Evaluation = Evaluation
  { wallets    :: [(Wallet, Integer)]
  , program    :: Program
  , sourceCode :: SourceCode
  , blockchain :: Blockchain
  }
  deriving (Generic, ToJSON, FromJSON)

pubKeys :: Evaluation -> [PubKey]
pubKeys Evaluation{..} = fmap (pack . unpack . fst) wallets

data EvaluationResult = EvaluationResult
  { resultBlockchain  :: Blockchain
  , resultGraph       :: FlowGraph
  , emulatorLog       :: [EmulatorEvent]
  , fundsDistribution :: [(Wallet, Ledger.Value)]
  }
  deriving (Generic, ToJSON)

data FunctionSchema a = FunctionSchema
  { functionName   :: Fn
  , argumentSchema :: [a]
  } deriving (Show, Generic, ToJSON, Functor)

data SimpleArgumentSchema
  = SimpleIntArgument
  | SimpleStringArgument
  | SimpleObjectArgument [(Text, SimpleArgumentSchema)]
  | UnknownArgument Text
  deriving (Show, Eq, Generic, ToJSON)

toSimpleArgumentSchema :: Schema -> SimpleArgumentSchema
toSimpleArgumentSchema schema@Schema {..} =
  case _schemaParamSchema of
    ParamSchema {..} ->
      case _paramSchemaType of
        SwaggerInteger -> SimpleIntArgument
        SwaggerString -> SimpleStringArgument
        SwaggerObject ->
          SimpleObjectArgument $
          over
            _2
            (\case
               Inline v -> toSimpleArgumentSchema v
               Ref _ -> unknown) <$>
          HM.toList _schemaProperties
        _ -> unknown
  where
    unknown = UnknownArgument $ Text.pack $ show schema

------------------------------------------------------------

data CompilationError
  = RawError Text
  | CompilationError { filename :: !Text
                     , row      :: !Int
                     , column   :: !Int
                     , text     :: ![Text] }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (ToJSON)

data PlaygroundError
  = CompilationErrors [CompilationError]
  | InterpreterError Hint.InterpreterError
  | FunctionSchemaError
  | DecodeJsonTypeError String String
  | OtherError String
  deriving stock (Show, Generic)

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
