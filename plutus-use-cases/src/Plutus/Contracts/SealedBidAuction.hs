{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
module Plutus.Contracts.SealedBidAuction(
  AuctionParams(..)
  , BidArgs(..)
  , RevealArgs(..)
  , AuctionError(..)
  , BidderSchema
  , SellerSchema
  , startAuction
  , bid
  , reveal
  , payout
  , packInteger
  , sellerContract
  , bidderContract
  ) where

import           Control.Lens                     (makeClassyPrisms)
import           Control.Monad                    (void)
import           Data.Aeson                       (FromJSON, ToJSON)
import           GHC.Generics                     (Generic)
import           Ledger                           (POSIXTime, PubKeyHash, Value)
import qualified Ledger
import qualified Ledger.Ada                       as Ada
import qualified Ledger.Constraints               as Constraints
import           Ledger.Constraints.TxConstraints (TxConstraints)
import qualified Ledger.Interval                  as Interval
import qualified Ledger.Typed.Scripts             as Scripts
import           Plutus.Contract
import           Plutus.Contract.Secrets
import           Plutus.Contract.StateMachine     (State (..), StateMachine (..), StateMachineClient, Void)
import qualified Plutus.Contract.StateMachine     as SM
import qualified PlutusTx
import           PlutusTx.Prelude
import qualified Prelude                          as Haskell

{- Note [Sealed bid auction disclaimer]
   This file implements a sealed bid auction using `SecretArgument`s. In the bidding
   phase of the contract sealed bids appear hashed on the blockchain and hashed
   bids are "claimed" by the participants in the second phase of the auction.

   Because bids are integer lovelace values there is the faint possibility of a
   brute-force attack or lookup table attack on the bids in the bidding phase. An
   implementation intended to be deployed in the real world may consider adding a
   salt to the secret bids or using some other more sophisticated mechanism to
   avoid this attack. In other words, please don't blidnly deploy this code
   without understanding the possible attack scenarios.
 -}

data BidArgs = BidArgs{ secretBid :: SecretArgument Integer }
          deriving stock (Haskell.Show, Generic)
          deriving anyclass (ToJSON, FromJSON)

data RevealArgs = RevealArgs{ publicBid :: Integer }
          deriving stock (Haskell.Show, Generic)
          deriving anyclass (ToJSON, FromJSON)

type BidderSchema = Endpoint "bid" BidArgs
                    .\/ Endpoint "reveal" RevealArgs
                    .\/ Endpoint "payout" ()
type SellerSchema = Endpoint "payout" ()

-- | Definition of an auction
data AuctionParams
    = AuctionParams
        { apOwner      :: PubKeyHash -- ^ Current owner of the asset. This is where the proceeds of the auction will be sent.
        , apAsset      :: Value -- ^ The asset itself. This value is going to be locked by the auction script output.
        , apEndTime    :: POSIXTime -- ^ When the time window for bidding ends.
        , apPayoutTime :: POSIXTime -- ^ When the time window for revealing your bid ends.
        }
        deriving stock (Haskell.Eq, Haskell.Show, Generic)
        deriving anyclass (ToJSON, FromJSON)

PlutusTx.makeLift ''AuctionParams


data SealedBid =
    SealedBid
        { sealedBid       :: BuiltinByteString
        , sealedBidBidder :: PubKeyHash
        }
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

PlutusTx.unstableMakeIsData ''SealedBid

instance Eq SealedBid where
  (SealedBid bid bidder) == (SealedBid bid' bidder') = bid == bid' && bidder == bidder'

data RevealedBid =
    RevealedBid
        { revealedBid       :: Integer
        , revealedBidBidder :: PubKeyHash
        }
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

PlutusTx.unstableMakeIsData ''RevealedBid

-- | The states of the auction
data AuctionState
    = Ongoing [SealedBid] -- Bids can be submitted.
    | AwaitingPayout RevealedBid [SealedBid] -- The bidding is finished and we are awaiting payout
    | Finished
    deriving stock (Generic, Haskell.Show, Haskell.Eq)
    deriving anyclass (ToJSON, FromJSON)

PlutusTx.unstableMakeIsData ''AuctionState

-- | Initial 'AuctionState'. In the beginning there are no bids.
initialState :: AuctionState
initialState = Ongoing []

-- | Transition between auction states
data AuctionInput
    = PlaceBid SealedBid -- Register a sealed bid
    | RevealBid RevealedBid -- Reveal a bid
    | Payout
    deriving stock (Generic, Haskell.Show)
    deriving anyclass (ToJSON, FromJSON)

PlutusTx.unstableMakeIsData ''AuctionInput

type AuctionMachine = StateMachine AuctionState AuctionInput

{-# INLINABLE packInteger #-}
-- | Pack an integer into a byte string with a leading
-- sign byte in little-endian order
packInteger :: Integer -> BuiltinByteString
packInteger k = if k < 0 then consByteString 1 (go (negate k) emptyByteString) else consByteString 0 (go k emptyByteString)
  where
    go n s
      | n == 0            = s
      | otherwise         = go (n `divide` 256) (consByteString (n `modulo` 256) s)

{-# INLINABLE hashInteger #-}
hashInteger :: Integer -> BuiltinByteString
hashInteger = sha2_256 . packInteger

{-# INLINABLE hashSecretInteger #-}
hashSecretInteger :: Secret Integer -> BuiltinByteString
hashSecretInteger = escape_sha2_256 . (fmap packInteger)

{-# INLINABLE sealBid #-}
sealBid :: RevealedBid -> SealedBid
sealBid RevealedBid{revealedBid, revealedBidBidder} = SealedBid (hashInteger revealedBid) revealedBidBidder

{-# INLINABLE valueOfBid #-}
valueOfBid :: RevealedBid -> Value
valueOfBid = Ada.lovelaceValueOf . revealedBid

{-# INLINABLE auctionTransition #-}
-- | The transitions of the auction state machine.
auctionTransition
  :: AuctionParams
  -> State AuctionState
  -> AuctionInput
  -> Maybe (TxConstraints Void Void, State AuctionState)
auctionTransition AuctionParams{apOwner, apAsset, apEndTime, apPayoutTime} State{stateData=oldState} input =
  case (oldState, input) of
    -- A new bid is placed, a bidder is only allowed to bid once
    (Ongoing bids, PlaceBid bid)
      | sealedBidBidder bid `notElem` map sealedBidBidder bids ->
        let constraints = Constraints.mustValidateIn (Interval.to $ apEndTime - 1)
            newState =
              State
                  { stateData  = Ongoing (bid:bids)
                  , stateValue = apAsset
                  }
        in Just (constraints, newState)

    -- The first bid is revealed
    (Ongoing bids, RevealBid bid)
      | (sealBid bid)  `elem` bids ->
        let constraints = Constraints.mustValidateIn (Interval.interval apEndTime (apPayoutTime - 1))
            newState =
              State
                  { stateData  = AwaitingPayout bid (filter (/= sealBid bid) bids)
                  , stateValue = apAsset <> valueOfBid bid
                  }
        in Just (constraints, newState)

    -- Nobody has revealed their bid and the deadline has arrived
    (Ongoing _, Payout) ->
      let constraints = Constraints.mustValidateIn (Interval.from apPayoutTime)
                      <> Constraints.mustPayToPubKey apOwner apAsset
          newState =
            State
                { stateData  = Finished
                , stateValue = mempty
                }
      in Just (constraints, newState)

    -- We are waiting for the payout deadine and a bid is revealed that is higher
    -- than the current maximum bid
    (AwaitingPayout highestBid sealedBids, RevealBid bid)
      | revealedBid bid > revealedBid highestBid
        && (sealBid bid)  `elem` sealedBids ->
        let constraints = Constraints.mustValidateIn (Interval.to $ apPayoutTime - 1)
                        <> Constraints.mustPayToPubKey (revealedBidBidder highestBid) (valueOfBid highestBid)
            newState =
              State
                  { stateData = AwaitingPayout bid (filter (/= sealBid bid) sealedBids)
                  , stateValue = apAsset <> valueOfBid bid
                  }
        in Just (constraints, newState)

    -- At least one bid has been revealed and the payout is triggered
    (AwaitingPayout highestBid _, Payout) ->
      let constraints = Constraints.mustValidateIn (Interval.from apPayoutTime)
                      <> Constraints.mustPayToPubKey apOwner (valueOfBid highestBid)
                      <> Constraints.mustPayToPubKey (revealedBidBidder highestBid) apAsset
          newState =
            State
                { stateData  = Finished
                , stateValue = mempty
                }
      in Just (constraints, newState)

    -- No other combination of inputs makes sense
    _ -> Nothing

{-# INLINABLE auctionStateMachine #-}
auctionStateMachine :: AuctionParams -> AuctionMachine
auctionStateMachine auctionParams =
    SM.mkStateMachine Nothing (auctionTransition auctionParams) isFinal
  where
    isFinal Finished = True
    isFinal _        = False

{-# INLINABLE mkValidator #-}
mkValidator :: AuctionParams -> Scripts.ValidatorType AuctionMachine
mkValidator = SM.mkValidator . auctionStateMachine

-- | The script instance of the auction state machine. It contains the state
--   machine compiled to a Plutus core validator script.
typedValidator :: AuctionParams -> Scripts.TypedValidator AuctionMachine
typedValidator = Scripts.mkTypedValidatorParam @AuctionMachine
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

data AuctionError =
    StateMachineContractError SM.SMContractError -- ^ State machine operation failed
    | AuctionContractError ContractError -- ^ Endpoint, coin selection, etc. failed
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''AuctionError

instance AsContractError AuctionError where
    _ContractError = _AuctionContractError . _ContractError

instance SM.AsSMContractError AuctionError where
    _SMContractError = _StateMachineContractError . SM._SMContractError

client :: AuctionParams -> StateMachineClient AuctionState AuctionInput
client auctionParams =
    let machine = auctionStateMachine auctionParams
        inst    = typedValidator auctionParams
    in SM.mkStateMachineClient (SM.StateMachineInstance machine inst)

startAuction :: Value -> POSIXTime -> POSIXTime -> Contract () SellerSchema AuctionError ()
startAuction asset endTime payoutTime = do
    self <- Ledger.pubKeyHash <$> ownPubKey
    let params = AuctionParams self asset endTime payoutTime
    void $ SM.runInitialise (client params) (Ongoing []) (apAsset params)

bid :: AuctionParams -> Promise () BidderSchema AuctionError ()
bid params = endpoint @"bid" $ \ BidArgs{secretBid} -> do
    self <- Ledger.pubKeyHash <$> ownPubKey
    let sBid = extractSecret secretBid
    void $ SM.runStep (client params) (PlaceBid $ SealedBid (hashSecretInteger sBid) self)

reveal :: AuctionParams -> Promise () BidderSchema AuctionError ()
reveal params = endpoint @"reveal" $ \ RevealArgs{publicBid} -> do
    self <- Ledger.pubKeyHash <$> ownPubKey
    void $ SM.runStep (client params) (RevealBid $ RevealedBid publicBid self)

payout :: (HasEndpoint "payout" () s) => AuctionParams -> Promise () s AuctionError ()
payout params = endpoint @"payout" $ \() -> do
    void $ SM.runStep (client params) Payout

-- | Top-level contract for seller
sellerContract :: AuctionParams -> Contract () SellerSchema AuctionError ()
sellerContract params@AuctionParams{..} = startAuction apAsset apEndTime apPayoutTime >> awaitPromise (payout params)

-- | Top-level contract for buyer
bidderContract :: AuctionParams -> Contract () BidderSchema AuctionError ()
bidderContract params = selectList [bid params, reveal params, payout params] >> bidderContract params
