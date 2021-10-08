-- This capability exposes the API for the Plutus Aplication called `MarloweApp`, which
-- has it's endpoints defined as the MarloweSchema in Language.Marlowe.Client module.
-- There is one `MarloweApp` per wallet, and it serves as a control app for all
-- the Marlowe contracts that the wallet has a role token.
module Capability.PlutusApps.MarloweApp
  ( class MarloweApp
  , createContract
  , applyInputs
  , redeem
  , createEndpointMutex
  , onNewActiveEndpoints
  ) where

import Prologue
import AppM (AppM)
import Bridge (toBack)
import Capability.Contract (invokeEndpoint) as Contract
import Capability.PlutusApps.MarloweApp.Lenses (_applyInputs, _create, _marloweAppEndpointMutex, _redeem)
import Capability.PlutusApps.MarloweApp.Types (EndpointMutex, MarloweAppEndpointMutexEnv)
import Control.Monad.Reader (class MonadAsk, asks)
import Data.Foldable (elem)
import Data.Json.JsonNTuple ((/\), type (/\)) as Json
import Data.Lens (toArrayOf, traversed, view)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.AVar as EAVar
import Effect.Aff.AVar as AVar
import Effect.Aff.Class (class MonadAff, liftAff)
import Marlowe.PAB (PlutusAppId)
import Marlowe.Semantics (Contract, MarloweParams, SlotInterval(..), TokenName, TransactionInput(..))
import Plutus.Contract.Effects (ActiveEndpoint, _ActiveEndpoint)
import Plutus.V1.Ledger.Crypto (PubKeyHash) as Back
import Plutus.V1.Ledger.Slot (Slot) as Back
import Plutus.V1.Ledger.Value (TokenName) as Back
import PlutusTx.AssocMap (Map) as Back
import Types (AjaxResponse)
import Wallet.Types (_EndpointDescription)
import Contacts.Types (PubKeyHash)

class MarloweApp m where
  createContract :: PlutusAppId -> Map TokenName PubKeyHash -> Contract -> m (AjaxResponse Unit)
  applyInputs :: PlutusAppId -> MarloweParams -> TransactionInput -> m (AjaxResponse Unit)
  -- TODO auto
  -- TODO close (I think it currently does nothing, maybe remove?)
  redeem :: PlutusAppId -> MarloweParams -> TokenName -> PubKeyHash -> m (AjaxResponse Unit)

instance marloweAppM :: MarloweApp AppM where
  createContract plutusAppId roles contract = do
    let
      backRoles :: Back.Map Back.TokenName Back.PubKeyHash
      backRoles = toBack roles
    mutex <- asks $ view (_marloweAppEndpointMutex <<< _create)
    liftAff $ AVar.take mutex
    Contract.invokeEndpoint plutusAppId "create" (backRoles /\ contract)
  applyInputs plutusAppId marloweContractId (TransactionInput { interval: SlotInterval slotStart slotEnd, inputs }) = do
    let
      backSlotInterval :: Back.Slot Json./\ Back.Slot
      backSlotInterval = (toBack slotStart) Json./\ (toBack slotEnd)

      payload = marloweContractId Json./\ Just backSlotInterval Json./\ inputs
    mutex <- asks $ view (_marloweAppEndpointMutex <<< _applyInputs)
    liftAff $ AVar.take mutex
    Contract.invokeEndpoint plutusAppId "apply-inputs" payload
  redeem plutusAppId marloweContractId tokenName pubKeyHash = do
    let
      payload :: MarloweParams Json./\ Back.TokenName Json./\ Back.PubKeyHash
      payload = marloweContractId Json./\ toBack tokenName Json./\ toBack pubKeyHash
    mutex <- asks $ view (_marloweAppEndpointMutex <<< _redeem)
    -- TODO: we could later add a forkAff with a timer that unlocks this timer if we
    --       dont get a response
    liftAff $ AVar.take mutex
    Contract.invokeEndpoint plutusAppId "redeem" payload

createEndpointMutex :: Effect EndpointMutex
createEndpointMutex = do
  create <- EAVar.empty
  applyInputs <- EAVar.empty
  redeem <- EAVar.empty
  pure { create, applyInputs, redeem }

-- Plutus contracts have endpoints that can be available or not. We get notified by the
-- websocket message NewActiveEndpoints when the status change, and we use this function
-- to update some mutex we use to restrict access to unavailable methods.
onNewActiveEndpoints ::
  forall env m.
  MonadAff m =>
  MonadAsk (MarloweAppEndpointMutexEnv env) m =>
  Array ActiveEndpoint ->
  m Unit
onNewActiveEndpoints endpoints = do
  let
    endpointsName :: Array String
    endpointsName =
      toArrayOf
        ( traversed
            <<< _ActiveEndpoint
            <<< prop (SProxy :: SProxy "aeDescription")
            <<< _EndpointDescription
            <<< prop (SProxy :: SProxy "getEndpointDescription")
        )
        endpoints

    -- For each endpoint:
    updateEndpoint name getter = do
      mutex <- asks $ view (_marloweAppEndpointMutex <<< getter)
      -- We check if it's available or not
      if (elem name endpointsName) then
        -- If it's available we put a unit in the mutex, to allow
        -- users to call the endpoint. If the mutex already has a unit,
        -- `tryPut` will return false but wont block the thread.
        void $ liftAff $ AVar.tryPut unit mutex
      else
        -- If it's not available we remove a unit from the mutex to make
        -- callers to wait until we put a unit. If the mutex was already
        -- empty, tryTake will return Nothing but wont block the thread.
        void $ liftAff $ AVar.tryTake mutex
  updateEndpoint "redeem" _redeem
  updateEndpoint "create" _create
  updateEndpoint "apply-inputs" _applyInputs
