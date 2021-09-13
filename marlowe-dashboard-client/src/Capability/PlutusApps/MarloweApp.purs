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

import Prelude
import AppM (AppM)
import Bridge (toBack)
import Capability.Contract (invokeEndpoint) as Contract
import Capability.PlutusApps.MarloweApp.Lenses (_applyInputs, _create, _marloweAppEndpointMutex, _redeem)
import Capability.PlutusApps.MarloweApp.Types (EndpointMutex, MarloweAppEndpointMutexEnv)
import Control.Monad.Reader (class MonadAsk, asks)
import Data.Foldable (elem)
import Data.Json.JsonTriple (JsonTriple(..))
import Data.Json.JsonTuple (JsonTuple)
import Data.Lens (toArrayOf, traversed, view)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.AVar as EAVar
import Effect.Aff.AVar as AVar
import Effect.Aff.Class (class MonadAff, liftAff)
import Marlowe.PAB (PlutusAppId)
import Marlowe.Semantics (Contract, MarloweParams, TokenName, TransactionInput(..))
import Plutus.Contract.Effects (ActiveEndpoint, _ActiveEndpoint)
import Plutus.V1.Ledger.Crypto (PubKeyHash) as Back
import Plutus.V1.Ledger.Slot (Slot) as Back
import Plutus.V1.Ledger.Value (TokenName) as Back
import PlutusTx.AssocMap (Map) as Back
import Types (AjaxResponse)
import Wallet.Types (_EndpointDescription)
import WalletData.Types (PubKeyHash)

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
  applyInputs plutusAppId marloweContractId (TransactionInput { interval, inputs }) = do
    let
      backSlotInterval :: JsonTuple Back.Slot Back.Slot
      backSlotInterval = toBack interval

      payload = JsonTriple (marloweContractId /\ (Just backSlotInterval) /\ inputs)
    mutex <- asks $ view (_marloweAppEndpointMutex <<< _applyInputs)
    liftAff $ AVar.take mutex
    Contract.invokeEndpoint plutusAppId "apply-inputs" payload
  redeem plutusAppId marloweContractId tokenName pubKeyHash = do
    let
      payload :: JsonTriple MarloweParams Back.TokenName Back.PubKeyHash
      payload = JsonTriple (marloweContractId /\ toBack tokenName /\ toBack pubKeyHash)
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

    updateEndpoint name getter = do
      mutex <- asks $ view (_marloweAppEndpointMutex <<< getter)
      if (elem name endpointsName) then
        void $ liftAff $ AVar.tryPut unit mutex
      else
        void $ liftAff $ AVar.tryTake mutex
  updateEndpoint "redeem" _redeem
  updateEndpoint "create" _create
  updateEndpoint "apply-inputs" _applyInputs
