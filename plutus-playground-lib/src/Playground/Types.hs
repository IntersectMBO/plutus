{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TemplateHaskell            #-}

module Playground.Types where

import           Control.Lens                 (makeLenses)
import           Control.Newtype.Generics     (Newtype)
import           Data.Aeson                   (FromJSON, ToJSON)
import qualified Data.Aeson                   as JSON
import           Data.Eq.Deriving             (deriveEq1)
import           Data.List.NonEmpty           (NonEmpty ((:|)))
import           Data.Row (type Row)
import           Data.Text                    (Text)
import           GHC.Generics                 (Generic)
import           Language.Haskell.Interpreter (CompilationError, SourceCode)
import qualified Language.Haskell.Interpreter as HI
import qualified Language.Haskell.TH.Syntax   as TH
import           Ledger                       (PubKey, Tx, fromSymbol, Interval, Slot)
import qualified Ledger.Ada                   as Ada
import           Ledger.Scripts               (ValidatorHash)
import           Ledger.Value                 (TokenName)
import qualified Ledger.Value                 as V
import           Schema                       (FormSchema,ToSchema)
import           Wallet.Emulator.Types        (EmulatorEvent, Wallet, walletPubKey)
import           Wallet.Rollup.Types          (AnnotatedTx)

data KnownCurrency =
    KnownCurrency
        { hash         :: ValidatorHash
        , friendlyName :: String
        , knownTokens  :: NonEmpty TokenName
        }
    deriving (Eq, Show, Generic, ToJSON, FromJSON)

adaCurrency :: KnownCurrency
adaCurrency =
    KnownCurrency
        { hash = fromSymbol Ada.adaSymbol
        , friendlyName = "Ada"
        , knownTokens = Ada.adaToken :| []
        }

--------------------------------------------------------------------------------
newtype EndpointName =
    EndpointName Text
    deriving (Eq, Show, Generic, TH.Lift)
    deriving newtype (ToJSON, FromJSON)

instance Newtype EndpointName

data Expression (schema :: Row *)
    = AddBlocks
          { blocks :: Int
          }
    | CallEndpoint
          { endpointName :: EndpointName
          , wallet :: Wallet
          , arguments :: JSON.Value
          }
    deriving (Show, Generic, ToJSON, FromJSON)

data PayToWalletParams =
    PayToWalletParams
        { payTo :: Wallet
        , value :: V.Value
        }
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema)

type Program schema = [Expression schema]

data SimulatorWallet =
    SimulatorWallet
        { simulatorWalletWallet :: Wallet
        , simulatorWalletBalance :: V.Value
        }
    deriving (Show, Generic, Eq)
    deriving anyclass (ToJSON, FromJSON)

data FormArgumentF a
    = FormUnitF
    | FormBoolF Bool
    | FormIntF (Maybe Int)
    | FormStringF (Maybe String)
    | FormHexF (Maybe String)
    | FormRadioF [String] (Maybe String)
    | FormArrayF FormSchema [a]
    | FormMaybeF FormSchema (Maybe a)
    | FormTupleF a a
    | FormObjectF [(String, a)]
    | FormValueF V.Value
    | FormSlotRangeF (Interval Slot)
    | FormUnsupportedF
          { description :: String
          }
    deriving (Show, Generic, Eq, Functor)
    deriving anyclass (ToJSON, FromJSON)

deriveEq1 ''FormArgumentF

data Evaluation =
    Evaluation
        { wallets    :: [SimulatorWallet]
        , sourceCode :: SourceCode
        , program    :: JSON.Value
        -- ^ This will be a '[Expression s]' where 's' is the schema from the compiled 'SourceCode'.
        -- It has to be JSON, because we can't know the type of 's' until the 'SourceCode' has been compiled.
        }
    deriving (Generic, ToJSON, FromJSON)

pubKeys :: Evaluation -> [PubKey]
pubKeys Evaluation {..} = walletPubKey . simulatorWalletWallet <$> wallets

data EvaluationResult =
    EvaluationResult
        { resultBlockchain  :: [[Tx]]
        , resultRollup      :: [[AnnotatedTx]]
        , emulatorLog       :: [EmulatorEvent]
        , fundsDistribution :: [SimulatorWallet]
        , walletKeys        :: [(PubKey, Wallet)]
        }
    deriving (Generic, ToJSON, FromJSON)

data CompilationResult =
    CompilationResult
        { functionSchema  :: [FunctionSchema FormSchema]
        , knownCurrencies :: [KnownCurrency]
        , iotsSpec        :: Text
        }
    deriving (Show, Generic, ToJSON)

data FunctionSchema a =
    FunctionSchema
        { functionName   :: EndpointName
        , argumentSchema :: [a]
        }
    deriving (Eq, Show, Generic, ToJSON, FromJSON, Functor)

------------------------------------------------------------
data PlaygroundError
    = CompilationErrors [CompilationError]
    | InterpreterError HI.InterpreterError
    | FunctionSchemaError
    | PlaygroundTimeout
    | RollupError Text
    | OtherError String
    | JsonDecodingError { expected :: String
                        , decodingError:: String
                        , input :: String}
    deriving (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeLenses 'EvaluationResult
