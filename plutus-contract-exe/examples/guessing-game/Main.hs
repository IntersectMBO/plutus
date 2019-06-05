{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
-- | Contract interface for the guessing game
module Main where

import           Control.Lens                                  (at, (^.))
import qualified Data.Aeson                                    as Aeson
import qualified Data.Map                                      as Map
import           Data.Maybe                                    (fromMaybe)
import           Data.Proxy                                    (Proxy (Proxy))
import           Data.Text                                     (Text)
import           GHC.Generics                                  (Generic)
import           Network.Wai.Handler.Warp                      (run)
import           Servant                                       ((:<|>) ((:<|>)), (:>), Get, JSON, Post, ReqBody)
import           Servant.Server                                (Application, Server, layout, serve)

import           Language.Plutus.Contract                      (ContractOut (ContractFinished, StartWatching, SubmitTransaction),
                                                                LedgerUpdate (OutputAdded, OutputSpent), mkUnbalancedTx)
import           Language.PlutusTx.Coordination.Contracts.Game (gameAddress, gameDataScript, gameRedeemerScript,
                                                                gameValidator)
import qualified Ledger                                        as L
import           Ledger.Ada                                    (Ada)
import qualified Ledger.Ada                                    as Ada
import qualified Ledger.AddressMap                             as AM

-- | Parameters for the "lock" endpoint
data LockParams = LockParams
    { secretWord :: String
    , amount     :: Ada
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (Aeson.FromJSON, Aeson.ToJSON)

--  | Parameters for the "guess" endpoint
newtype GuessParams = GuessParams
    { guess :: String
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (Aeson.FromJSON, Aeson.ToJSON)

newtype GameState = GameState
    { interestingAddresses :: AM.AddressMap
    }
    deriving stock (Show, Generic)
    deriving newtype (Aeson.FromJSON, Aeson.ToJSON)

initialState :: GameState
initialState = GameState mempty

type GuessingGameAPI =

  --  All endpoints (except layout) use the POST method to supply parameters in
  --  the request body. They expect the current 'GameState' and an
  --  endpoint-specific argument, and return the new 'GameState' and a list of
  --  'ContractOut' events.

  --  The first two endpoints are the same for all contracts:

  -- ledger-update, informing the contract about changes to the ledger state
    "ledger-update" :> ReqBody '[JSON] (GameState, LedgerUpdate) :> Post '[JSON] (GameState, [ContractOut]) -- POST /ledger-update

  -- initialise, a sequence of 'ContractOut' events that need to be processed
  -- when the contract is first started.
    :<|> "initialise" :> Get '[JSON] (GameState, [ContractOut])

  -- The following two endpoints are specific to this example (guessing game)

  -- lock some funds
    :<|> "lock" :> ReqBody '[JSON] (GameState, LockParams) :> Post '[JSON] (GameState, [ContractOut]) -- POST /lock

  -- make a guess
    :<|> "guess" :> ReqBody '[JSON] (GameState, GuessParams) :> Post '[JSON] (GameState, [ContractOut]) -- POST /guess

  -- returns a textual description of the API (this is only a stand-in until
  -- we have an actual schema endpoint)
    :<|> "layout" :> Get '[JSON] Text

server :: Server GuessingGameAPI
server = ledgerUpdate :<|> initialise :<|> lock :<|> guess_ :<|> l
    where

        -- To initialise the game contract we start watching the game address
        -- TODO: We don't need to watch the game address if we are the
        --       organisers of the game. (See note [ContractFinished event] in
        --       Language.Plutus.Contract). Maybe we need one initialise
        --       endpoint per role?
        initialise          = pure (initialState, [StartWatching gameAddress])

        -- When the outputs at the address change we call 'AM.updateAddresses'
        -- to update the 'GameState'
        ledgerUpdate (GameState mp, u) =
            let mp' = case u of
                        OutputAdded _ tx -> AM.updateAddresses tx mp
                        OutputSpent _ tx -> AM.updateAddresses tx mp
                        _                -> mp
            in
                pure (GameState mp', [])

        -- The lock endpoint. Produces a transaction with a single
        -- pay-to-script output, locked by the game validator using
        -- the hash of the secret word.
        lock (s, LockParams secret amt) =
          let
              vl         = Ada.toValue amt
              dataScript = gameDataScript secret
              output = L.TxOutOf gameAddress vl (L.PayToScript dataScript)
              tx     = mkUnbalancedTx [] [output]
          in
            -- submit transaction, then this contract instance is finished
            -- see note [ContractFinished event] in Language.Plutus.Contract
            pure (s, [SubmitTransaction tx, ContractFinished])

        -- The guess endpoint. Produces a transaction that spends all known
        -- outputs at the game address using the guess
        guess_ (GameState mp, GuessParams gss)       =
            let
                outputs  = fmap fst . Map.toList . fromMaybe Map.empty $ mp ^. at gameAddress
                redeemer = gameRedeemerScript gss
                inp      = (\o -> L.scriptTxIn o gameValidator redeemer) <$> outputs
                tx       = mkUnbalancedTx inp []
            in
                pure (GameState mp, [SubmitTransaction tx, ContractFinished])

        l = pure (layout (Proxy @GuessingGameAPI))

app :: Application
app = serve (Proxy @GuessingGameAPI) server

-- Run the server on port 8080
main :: IO ()
main = run 8080 app
