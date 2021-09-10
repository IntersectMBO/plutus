-- This capability exposes the API for the Plutus Aplication called `MarloweApp`, which
-- has it's endpoints defined as the MarloweSchema in Language.Marlowe.Client module.
-- There is one `MarloweApp` per wallet, and it serves as a control app for all
-- the Marlowe contracts that the wallet has a role token.
module Capability.PlutusApps.MarloweApp
  ( class MarloweApp
  , createContract
  , applyInputs
  , redeem
  , onNewState
  ) where

import Prelude
import AppM (AppM)
import Bridge (toBack)
import Capability.Contract (invokeEndpoint) as Contract
import Capability.PlutusApps.MarloweApp.Types (MarloweAppState, LastResult(..), MarloweAppEndpoint(..))
import Capability.Toast (class Toast, addToast)
import Control.Monad.Reader (class MonadAsk, asks)
import Data.Json.JsonTriple (JsonTriple(..))
import Data.Json.JsonTuple (JsonTuple)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Traversable (for_)
import Data.Tuple.Nested ((/\))
import Debug.Trace (traceM)
import Effect.Aff.AVar (AVar)
import Effect.Aff.AVar as AVar
import Effect.Aff.Class (class MonadAff, liftAff)
import Marlowe.PAB (PlutusAppId)
import Marlowe.Semantics (Contract, MarloweParams, TokenName, TransactionInput(..))
import Plutus.V1.Ledger.Crypto (PubKeyHash) as Back
import Plutus.V1.Ledger.Slot (Slot) as Back
import Plutus.V1.Ledger.Value (TokenName) as Back
import PlutusTx.AssocMap (Map) as Back
import Toast.Types (errorToast, successToast)
import Types (AjaxResponse)
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
    mutex <- asks _.lastMarloweAppEndpointCall
    traceM "Mutex put Create"
    liftAff $ AVar.put Create mutex
    Contract.invokeEndpoint plutusAppId "create" (backRoles /\ contract)
  applyInputs plutusAppId marloweContractId (TransactionInput { interval, inputs }) = do
    let
      backSlotInterval :: JsonTuple Back.Slot Back.Slot
      backSlotInterval = toBack interval

      payload = JsonTriple (marloweContractId /\ (Just backSlotInterval) /\ inputs)
    mutex <- asks _.lastMarloweAppEndpointCall
    traceM "Mutex put ApplyInputs"
    liftAff $ AVar.put ApplyInputs mutex
    Contract.invokeEndpoint plutusAppId "apply-inputs" payload
  redeem plutusAppId marloweContractId tokenName pubKeyHash = do
    let
      payload :: JsonTriple MarloweParams Back.TokenName Back.PubKeyHash
      payload = JsonTriple (marloweContractId /\ toBack tokenName /\ toBack pubKeyHash)
    mutex <- asks _.lastMarloweAppEndpointCall
    -- TODO: we could later add a forkAff with a timer that unlocks this timer if we
    --       dont get a response
    traceM "Mutex put Redeem"
    liftAff $ AVar.put Redeem mutex
    Contract.invokeEndpoint plutusAppId "redeem" payload

onNewState ::
  forall env m.
  MonadAff m =>
  Toast m =>
  MonadAsk { lastMarloweAppEndpointCall :: AVar MarloweAppEndpoint | env } m =>
  MarloweAppState ->
  m Unit
onNewState lastResult = do
  mutex :: AVar MarloweAppEndpoint <- asks _.lastMarloweAppEndpointCall
  -- We try to take instead of taking as the later will block the thread until there
  -- is a response, but if we are at this point, we should already have a value put in
  -- the mutex. We use for_ to ignore the case in which we have a response but not a request.
  traceM "Mutex tryTake"
  traceM lastResult
  mLastMarloweAppEndpointCall <- liftAff $ AVar.tryTake mutex
  traceM mLastMarloweAppEndpointCall
  for_ mLastMarloweAppEndpointCall \lastMarloweAppEndpointCall -> case lastResult of
    OK -> case lastMarloweAppEndpointCall of
      Create -> addToast $ successToast "Contract initialised."
      ApplyInputs -> addToast $ successToast "Contract update applied."
      _ -> pure unit
    SomeError marloweError -> case lastMarloweAppEndpointCall of
      Create -> addToast $ errorToast "Failed to initialise contract." Nothing
      ApplyInputs -> addToast $ errorToast "Failed to update contract." Nothing
      _ -> pure unit
    Unknown -> pure unit
