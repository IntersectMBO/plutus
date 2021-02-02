{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
module Language.PlutusTx.Coordination.Contracts.Auction(
    AuctionState(..),
    AuctionInput(..),
    BuyerSchema,
    SellerSchema,
    AuctionParams(..),
    auctionBuyer,
    auctionSeller,
    ) where


import           Data.Aeson                            (FromJSON, ToJSON)
import           Data.Foldable                         (traverse_)
import           GHC.Generics                          (Generic)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.StateMachine (State (..), StateMachine (..), StateMachineClient,
                                                        StateMachineInstance (..), Void)
import qualified Language.Plutus.Contract.StateMachine as SM
import           Language.Plutus.Contract.Util         (loopM)
import qualified Language.PlutusTx                     as PlutusTx
import           Language.PlutusTx.Prelude
import           Ledger                                (Ada, PubKeyHash, Slot, Value)
import qualified Ledger
import qualified Ledger.Ada                            as Ada
import qualified Ledger.Constraints                    as Constraints
import           Ledger.Constraints.TxConstraints      (TxConstraints)
import qualified Ledger.Interval                       as Interval
import qualified Ledger.Typed.Scripts                  as Scripts
import           Ledger.Typed.Tx                       (TypedScriptTxOut (..))
import qualified Prelude                               as Haskell

-- | Definition of an auction
data AuctionParams
    = AuctionParams
        { apOwner   :: PubKeyHash -- ^ Current owner of the asset. This is where the proceeds of the auction will be sent.
        , apAsset   :: Value -- ^ The asset itself. This value is going to be locked by the auction script output.
        , apEndTime :: Slot -- ^ When the time window for bidding ends.
        }
        deriving stock (Haskell.Eq, Haskell.Show, Generic)
        deriving anyclass (ToJSON, FromJSON)

PlutusTx.makeLift ''AuctionParams


data HighestBid =
    HighestBid
        { highestBid    :: Ada
        , highestBidder :: PubKeyHash
        }
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

PlutusTx.makeIsData ''HighestBid

-- | The states of the auction
data AuctionState
    = Ongoing HighestBid -- Bids can be submitted
    | Finished HighestBid -- The auction is finished
    deriving stock (Generic, Haskell.Show)
    deriving anyclass (ToJSON, FromJSON)

PlutusTx.makeIsData ''AuctionState

-- | Transition between auction states
data AuctionInput
    = Bid { newBid :: Ada, newBidder :: PubKeyHash } -- Increase the price
    | Payout
    deriving stock (Generic, Haskell.Show)
    deriving anyclass (ToJSON, FromJSON)

PlutusTx.makeIsData ''AuctionInput

{-# INLINABLE auctionTransition #-}
-- | The transitions of the auction state machine.
auctionTransition :: AuctionParams -> State AuctionState -> AuctionInput -> Maybe (TxConstraints Void Void, State AuctionState)

auctionTransition AuctionParams{apOwner, apAsset, apEndTime} State{stateData=oldState} input =
    case (oldState, input) of

        (Ongoing HighestBid{highestBid, highestBidder}, Bid{newBid, newBidder}) | newBid > highestBid -> -- if the new bid is higher,
            let constraints =
                    Constraints.mustPayToPubKey highestBidder (Ada.toValue highestBid) -- we pay back the previous highest bid
                    <> Constraints.mustValidateIn (Interval.to apEndTime) -- but only if we haven't gone past 'apEndTime'
                newState =
                    State
                        { stateData = Ongoing HighestBid{highestBid = newBid, highestBidder = newBidder}
                        , stateValue = apAsset <> Ada.toValue newBid -- and lock the new bid in the script output
                        }
            in Just (constraints, newState)

        (Ongoing h@HighestBid{highestBidder, highestBid}, Payout) ->
            let constraints =
                    Constraints.mustValidateIn (Interval.from apEndTime) -- When the auction has ended,
                    <> Constraints.mustPayToPubKey apOwner (Ada.toValue highestBid) -- the owner receives the payment
                    <> Constraints.mustPayToPubKey highestBidder apAsset -- and the highest bidder the asset
                newState = State { stateData = Finished h, stateValue = mempty }
            in Just (constraints, newState)

        -- Any other combination of 'AuctionState' and 'AuctionInput' is disallowed.
        -- This rules out new bids that don't go over the current highest bid.
        _ -> Nothing


{-# INLINABLE auctionStateMachine #-}
auctionStateMachine :: AuctionParams -> StateMachine AuctionState AuctionInput
auctionStateMachine auctionParams = SM.mkStateMachine (auctionTransition auctionParams) isFinal where
    isFinal Finished{} = True
    isFinal _          = False


-- | The script instance of the auction state machine. It contains the state
--   machine compiled to a Plutus core validator script.
scriptInstance :: AuctionParams -> Scripts.ScriptInstance (StateMachine AuctionState AuctionInput)
scriptInstance auctionParams =
    let val = $$(PlutusTx.compile [|| validatorParam ||])
            `PlutusTx.applyCode`
                PlutusTx.liftCode auctionParams
        validatorParam f = SM.mkValidator (auctionStateMachine f)
        wrap = Scripts.wrapValidator @AuctionState @AuctionInput

    in Scripts.validator @(StateMachine AuctionState AuctionInput)
        val
        $$(PlutusTx.compile [|| wrap ||])

-- | The machine client of the auction state machine. It contains the script instance
--   with the on-chain code, and the Haskell definition of the state machine for
--   off-chain use.
machineClient
    :: Scripts.ScriptInstance (StateMachine AuctionState AuctionInput)
    -> AuctionParams
    -> StateMachineClient AuctionState AuctionInput
machineClient inst auctionParams =
    let machine = auctionStateMachine auctionParams
    in SM.mkStateMachineClient (StateMachineInstance machine inst)
--BLOCK7

type BuyerSchema = BlockchainActions .\/ Endpoint "bid" Ada
type SellerSchema = BlockchainActions -- Don't need any endpoints: the contract runs automatically until the auction is finished.

data AuctionLog =
    AuctionStarted AuctionParams
    | AuctionFailed SM.SMContractError
    | CurrentState HighestBid
    | BidSubmitted HighestBid
    | AuctionEnded HighestBid
    | CurrentStateNotFound
    | TransitionFailed (SM.InvalidTransition AuctionState AuctionInput)
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON)


-- | Client code for the seller
auctionSeller :: Value -> Slot -> Contract SellerSchema SM.SMContractError ()
auctionSeller value slot = do
    self <- Ledger.pubKeyHash <$> ownPubKey
    let params       = AuctionParams{apOwner = self, apAsset = value, apEndTime = slot }
        inst         = scriptInstance params
        client       = machineClient inst params
        initialState = Ongoing HighestBid{highestBid = 0, highestBidder = self}

    _ <- handleError
            (\e -> do { logError (AuctionFailed e); throwError e})
            (SM.runInitialise client initialState value)

    logInfo $ AuctionStarted params
    _ <- awaitSlot slot

    r <- SM.runStep client Payout
    case r of
        SM.TransitionFailure i            -> logError (TransitionFailed i)
        SM.TransitionSuccess (Finished h) -> logInfo $ AuctionEnded h
        SM.TransitionSuccess s            -> logWarn ("Unexpected state after Payout transition: " <> show s)


-- | Get the current state of the contract and log it.
currentState :: StateMachineClient AuctionState AuctionInput -> Contract BuyerSchema SM.SMContractError (Maybe HighestBid)
currentState client = SM.getOnChainState client >>= \case
    Just ((TypedScriptTxOut{tyTxOutData=Ongoing s}, _), _) -> do
        logInfo (CurrentState s)
        pure (Just s)
    _ -> do
        logWarn CurrentStateNotFound
        pure Nothing

{- Note [Buyer client]

In the buyer client we want to keep track of the on-chain state of the auction
to give our user a chance to react if they are outbid by somebody else.

At the same time we want to have the "bid" endpoint active for any bids of our
own, and we want to stop the client when the auction is over.

To achieve this, we have a loop where we wait for one of several events to
happen and then deal with the event. The waiting is implemented in
@waitForChange@ and the event handling is in @handleChange@.

Updates to the user are provided via the log functionality. This is not as bad
as it sounds because the log records JSON objects so we are at least semi-
structured. (Basically we have a @Writer [Aeson.Value]@ - in the future we
should just make it a @Writer a@ for some user-defined @a@ so that we can
export the "current state" of the app more easily.)

-}

data BuyerChange =
        AuctionIsOver HighestBid -- ^ The auction has ended with the highest bid
        | SubmitOwnBid Ada -- ^ We want to submit a new bid
        | OtherBid HighestBid -- ^ Another buyer submitted a higher bid
        | NoChange HighestBid -- ^ Nothing has changed

waitForChange :: AuctionParams -> StateMachineClient AuctionState AuctionInput -> HighestBid -> Contract BuyerSchema SM.SMContractError BuyerChange
waitForChange AuctionParams{apEndTime} client lastHighestBid = do
    s <- currentSlot
    let
        auctionOver = awaitSlot apEndTime >> pure (AuctionIsOver lastHighestBid)
        submitOwnBid = SubmitOwnBid <$> endpoint @"bid"
        otherBid = do
            let address = Scripts.scriptAddress (validatorInstance (SM.scInstance client))
                targetSlot = succ (succ s) -- FIXME (jm): There is some off-by-one thing going on that requires us to
                                           -- use succ.succ instead of just a single succ if we want 'addressChangeRequest'
                                           -- to wait for the next slot to begin.
                                           -- I don't have the time to look into that atm though :(
            AddressChangeResponse{acrTxns} <- addressChangeRequest AddressChangeRequest{acreqSlot=targetSlot, acreqAddress = address}
            case acrTxns of
                [] -> pure (NoChange lastHighestBid)
                _  -> currentState client >>= pure . maybe (AuctionIsOver lastHighestBid) OtherBid

    -- see note [Buyer client]
    auctionOver `select` submitOwnBid `select` otherBid

handleChange :: StateMachineClient AuctionState AuctionInput -> HighestBid -> BuyerChange -> Contract BuyerSchema SM.SMContractError (Either HighestBid ())
handleChange client lastHighestBid change =
    let continue = pure . Left
        stop     = pure (Right ())
    -- see note [Buyer client]
    in case change of
        AuctionIsOver _ -> stop
        SubmitOwnBid ada -> do
            self <- Ledger.pubKeyHash <$> ownPubKey
            r <- SM.runStep client Bid{newBid = ada, newBidder = self}
            let newHighestBid = HighestBid{highestBid= ada, highestBidder = self}
            case r of
                SM.TransitionFailure i -> logError (TransitionFailed i) >> continue lastHighestBid
                SM.TransitionSuccess _ -> logInfo (BidSubmitted newHighestBid) >> continue newHighestBid
        OtherBid s -> do
            logInfo (CurrentState s)
            continue s
        NoChange s -> continue s

auctionBuyer :: AuctionParams -> Contract BuyerSchema SM.SMContractError ()
auctionBuyer params = do
    let inst         = scriptInstance params
        client       = machineClient inst params

        -- the actual loop, see note [Buyer client]
        loop         = loopM (\h -> waitForChange params client h >>= handleChange client h)
    initial <- currentState client
    traverse_ loop initial
