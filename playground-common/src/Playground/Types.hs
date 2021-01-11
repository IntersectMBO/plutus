{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}

module Playground.Types where

import           Control.Lens                                    (makeLenses)
import           Data.Aeson                                      (FromJSON, ToJSON)
import qualified Data.Aeson                                      as JSON
import           Data.Functor.Foldable                           (Fix)
import           Data.List.NonEmpty                              (NonEmpty ((:|)))
import           Data.Text                                       (Text)
import           GHC.Generics                                    (Generic)
import           Language.Haskell.Interpreter                    (CompilationError, SourceCode)
import qualified Language.Haskell.Interpreter                    as HI
import           Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription)
import           Ledger                                          (PubKeyHash, fromSymbol, pubKeyHash)
import qualified Ledger.Ada                                      as Ada
import           Ledger.Scripts                                  (ValidatorHash)
import           Ledger.Slot                                     (Slot)
import           Ledger.Value                                    (TokenName)
import qualified Ledger.Value                                    as V
import           Schema                                          (FormArgumentF, FormSchema, ToArgument, ToSchema)
import           Wallet.Emulator.Types                           (EmulatorEvent, Wallet, walletPubKey)
import           Wallet.Rollup.Types                             (AnnotatedTx)

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
data PayToWalletParams =
    PayToWalletParams
        { payTo :: Wallet
        , value :: V.Value
        }
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema, ToArgument)

data SimulatorWallet =
    SimulatorWallet
        { simulatorWalletWallet  :: Wallet
        , simulatorWalletBalance :: V.Value
        }
    deriving (Show, Generic, Eq)
    deriving anyclass (ToJSON, FromJSON)

-- | Describes the mockchain requests the frontend can make of the
-- backend. These will be mostly calls to their contract's various
-- endpoints, but we supply a few extra special calls for the sake of
-- easier testing and simulation.
data ContractCall a
    = CallEndpoint
          { caller         :: Wallet
          , argumentValues :: FunctionSchema a
          }
      -- ^ Call one of the defined endpoints of your contract.
    | AddBlocks
          { blocks :: Integer
          }
      -- ^ Add the specified number of blocks to the mockchain before continuing.
    | AddBlocksUntil
          { slot :: Slot
          }
      -- ^ Keep adding blocks until the mockchain reaches the
      -- specified slot, then continue.  (Note that calling
      -- @AddBlocksUntil 20@ doesn't mean you'll continue at slot 20,
      -- just that the slot number will now be /at least/ that high.
    | PayToWallet
          { sender    :: Wallet
          , recipient :: Wallet
          , amount    :: V.Value
          }
      -- ^ Make a wallet-to-wallet transfer of the specified value.
    deriving ( Show
             , Eq
             , Generic
             , Functor
             , ToJSON
             , FromJSON
             , Foldable
             , Traversable
             )

type SimulatorAction = ContractCall (Fix FormArgumentF)

type Expression = ContractCall JSON.Value

data Simulation =
    Simulation
        { simulationName    :: String
        , simulationActions :: [SimulatorAction]
        , simulationWallets :: [SimulatorWallet]
        }
    deriving (Show, Generic, Eq)
    deriving anyclass (ToJSON, FromJSON)

data Evaluation =
    Evaluation
        { wallets    :: [SimulatorWallet]
        , sourceCode :: SourceCode
        , program    :: JSON.Value
        -- ^ This will be a '[Expression s]' where 's' is the schema from the compiled 'SourceCode'.
        -- It has to be JSON, because we can't know the type of 's' until the 'SourceCode' has been compiled.
        }
    deriving (Generic, ToJSON, FromJSON)

pubKeys :: Evaluation -> [PubKeyHash]
pubKeys Evaluation {..} = pubKeyHash . walletPubKey . simulatorWalletWallet <$> wallets

data EvaluationResult =
    EvaluationResult
        { resultRollup      :: [[AnnotatedTx]] -- ^ Annotated blockchain, newest blocks first
        , emulatorLog       :: [EmulatorEvent] -- ^ The emulator log, newest events first
        , emulatorTrace     :: Text
        , fundsDistribution :: [SimulatorWallet]
        , walletKeys        :: [(PubKeyHash, Wallet)]
        }
    deriving (Show, Generic, ToJSON, FromJSON)

data CompilationResult =
    CompilationResult
        { functionSchema  :: [FunctionSchema FormSchema]
        , knownCurrencies :: [KnownCurrency]
        , iotsSpec        :: Text
        }
    deriving (Show, Eq, Generic, ToJSON)

data ContractDemo =
    ContractDemo
        { contractDemoName           :: Text
        , contractDemoEditorContents :: SourceCode
        , contractDemoSimulations    :: [Simulation]
        , contractDemoContext        :: HI.InterpreterResult CompilationResult
        }
    deriving (Show, Eq, Generic, ToJSON)

data FunctionSchema a =
    FunctionSchema
        { endpointDescription :: EndpointDescription
        , argument            :: a
        -- ^ All contract endpoints take a single argument. (Multiple arguments must be wrapped up into a container.)
        }
    deriving ( Eq
             , Show
             , Generic
             , ToJSON
             , FromJSON
             , Functor
             , Foldable
             , Traversable
             )

------------------------------------------------------------
data PlaygroundError
    = CompilationErrors [CompilationError]
    | InterpreterError HI.InterpreterError
    | RollupError Text
    | OtherError String
    | JsonDecodingError
          { expected      :: String
          , decodingError :: String
          , input         :: String
          }
    deriving (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeLenses 'EvaluationResult
