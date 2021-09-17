{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-orphans #-}
module Spec.SealedBidAuction where

import           Cardano.Crypto.Hash                as Crypto
import           Control.Lens                       hiding (elements)
import           Control.Monad                      (void, when)
import           Control.Monad.Freer.Extras.Log     (LogLevel (..))
import           Data.Default                       (Default (def))

import           Ledger                             (Slot (..), Value, pubKeyHash)
import qualified Ledger.Ada                         as Ada
import           Plutus.Contract.Test               hiding (not)

import qualified Ledger.TimeSlot                    as TimeSlot
import qualified Ledger.Value                       as Value
import           Plutus.Contract.Secrets
import           Plutus.Contract.Test.ContractModel
import           Plutus.Contracts.SealedBidAuction
import qualified Plutus.Trace.Emulator              as Trace
import qualified PlutusTx.Prelude                   as PlutusTx

import           Test.QuickCheck                    hiding ((.&&.))
import           Test.Tasty
import           Test.Tasty.QuickCheck              (testProperty)

instance Arbitrary AuctionParams where
  arbitrary = do
    endTime    <- choose (20, 50)
    payoutTime <- choose (endTime+1, 70)
    return $ AuctionParams
              { apOwner      = pubKeyHash $ walletPubKey w1
              , apAsset      = theToken
              , apEndTime    = TimeSlot.scSlotZeroTime def + fromInteger (endTime*1000)
              , apPayoutTime = TimeSlot.scSlotZeroTime def + fromInteger (payoutTime*1000)
              }

-- | The token that we are auctioning off.
theToken :: Value
theToken = Value.singleton mpsHash "token" 1

mpsHash :: Value.CurrencySymbol
mpsHash = Value.CurrencySymbol $ PlutusTx.toBuiltin $ Crypto.hashToBytes $ Crypto.hashWith @Crypto.Blake2b_224 id "ffff"

-- | 'EmulatorConfig' that includes 'theToken' in the initial distribution of Wallet 1.
auctionEmulatorCfg :: Trace.EmulatorConfig
auctionEmulatorCfg =
    let initialDistribution = defaultDist & over (ix w1) ((<>) theToken)
    in (def & Trace.initialChainState .~ Left initialDistribution) & Trace.slotConfig .~ def

-- | 'CheckOptions' that includes our own 'auctionEmulatorCfg'.
options :: CheckOptions
options = set emulatorConfig auctionEmulatorCfg defaultCheckOptions

-- * QuickCheck model

data AuctionModel = AuctionModel
    { _currentBids       :: [(Integer, Wallet)]
    , _currentWinningBid :: Maybe (Integer, Wallet)
    , _endBidSlot        :: Slot
    , _payoutSlot        :: Slot
    , _phase             :: Phase }
    deriving (Show)

data Phase = NotStarted | Bidding | AwaitingPayout | PayoutTime | AuctionOver
    deriving (Eq, Show)

makeLenses 'AuctionModel

deriving instance Eq (ContractInstanceKey AuctionModel w s e)
deriving instance Show (ContractInstanceKey AuctionModel w s e)

instance ContractModel AuctionModel where

    data ContractInstanceKey AuctionModel w s e where
        SellerH :: ContractInstanceKey AuctionModel () SellerSchema AuctionError
        BidderH :: Wallet -> ContractInstanceKey AuctionModel () BidderSchema AuctionError

    data Action AuctionModel = Init AuctionParams | Bid Wallet Integer | WaitUntil Slot | Reveal Wallet Integer | Payout Wallet
        deriving (Eq, Show)

    initialState = AuctionModel
        { _currentBids       = []
        , _currentWinningBid = Nothing
        , _endBidSlot        = TimeSlot.posixTimeToEnclosingSlot def (TimeSlot.scSlotZeroTime def)
        , _payoutSlot        = TimeSlot.posixTimeToEnclosingSlot def (TimeSlot.scSlotZeroTime def)
        , _phase             = NotStarted
        }

    arbitraryAction s
        | p /= NotStarted =
            frequency [ (1, WaitUntil . step <$> choose (1, 3 :: Integer))
                      , (5, pure (WaitUntil $ s ^. contractState . endBidSlot))
                      , (5, pure (WaitUntil $ s ^. contractState . payoutSlot))
                      , (40, Bid  <$> elements [w2, w3, w4] <*> choose (1, 20))
                      -- Random reveal
                      , (20, Reveal <$> elements [w2, w3, w4] <*> choose (1, 20))
                      -- Correct reveal
                      , (20, uncurry Reveal <$> elements [ (w,i) | (i,w) <- (s ^. contractState . currentBids) ])
                      , (20, Payout <$> elements [w1, w2, w3, w4]) ]
        | otherwise = Init <$> arbitrary
        where
            p    = s ^. contractState . phase
            slot = s ^. currentSlot
            step n = slot + fromIntegral n

    precondition s cmd  =
        case cmd of
            Init _         -> s ^. contractState . phase == NotStarted

            WaitUntil slot -> slot > s ^. currentSlot

            Bid w _        -> s ^. contractState . phase == Bidding
                              && w `notElem` fmap snd (s ^. contractState . currentBids)

            Reveal w _     -> s ^. contractState . phase == AwaitingPayout
                              && w `elem` fmap snd (s ^. contractState . currentBids)

            Payout _       -> s ^. contractState . phase == PayoutTime

    perform _ _ (Init _)            = delay 3
    perform _ _ (WaitUntil slot)    = void $ Trace.waitUntilSlot slot
    perform handle _ (Bid w bid)    = do
        Trace.callEndpoint @"bid" (handle $ BidderH w) (BidArgs (secretArg bid))
        delay 1
    perform handle _ (Reveal w bid) = do
        Trace.callEndpoint @"reveal" (handle $ BidderH w) (RevealArgs bid)
        delay 1
    perform handle _ (Payout w)
      | w == w1 = do
        Trace.callEndpoint @"payout" (handle $ SellerH) ()
        delay 1
      | otherwise = do
        Trace.callEndpoint @"payout" (handle $ BidderH w) ()
        delay 1

    shrinkAction _ (WaitUntil (Slot n))  = [ WaitUntil (Slot n') | n' <- shrink n ]
    shrinkAction s (Bid w v) =
        WaitUntil (s ^. currentSlot + 1) : [ Bid w v' | v' <- shrink v ]
    shrinkAction s (Reveal w v) =
        WaitUntil (s ^. currentSlot + 1) : [ Reveal w v' | v' <- shrink v ]
    shrinkAction _ _ = []

    monitoring _ _ = id

    -- This command is only for setting up the model state with theToken
    nextState cmd = do
        updatePhase
        currentPhase <- viewContractState phase
        case cmd of
            Init params -> do
                phase $= Bidding
                withdraw w1 theToken
                endBidSlot $= TimeSlot.posixTimeToEnclosingSlot def (apEndTime params)
                payoutSlot $= TimeSlot.posixTimeToEnclosingSlot def (apPayoutTime params)
                wait 3

            WaitUntil slot' -> do
                waitUntil slot'

            Bid w bid | currentPhase == Bidding -> do
                  bids <- viewContractState currentBids
                  when (w `notElem` fmap snd bids) $ do
                    currentBids $= ((bid, w):bids)
                  wait 1

            Reveal w bid | currentPhase == AwaitingPayout -> do
                bids <- viewContractState currentBids
                mwinningBid <- viewContractState currentWinningBid
                case mwinningBid of
                  Just (oldBid, w') ->
                    when ((bid, w) `elem` bids && bid > oldBid) $ do
                      withdraw w $ Ada.lovelaceValueOf bid
                      deposit w' $ Ada.lovelaceValueOf oldBid
                      currentWinningBid $= Just (bid, w)
                  Nothing ->
                    when ((bid, w) `elem` bids) $ do
                      withdraw w $ Ada.lovelaceValueOf bid
                      currentWinningBid $= Just (bid, w)
                wait 1

            Payout _ | currentPhase == PayoutTime -> do
                  mwinningBid <- viewContractState currentWinningBid
                  case mwinningBid of
                    Just (bid, winner) -> do
                      deposit winner theToken
                      deposit w1 $ Ada.lovelaceValueOf bid

                    Nothing -> do
                      deposit w1 theToken
                  wait 1
                  phase $= AuctionOver

            _ -> pure ()
        updatePhase
      where
        updatePhase = do
          currentPhase <- viewContractState phase
          when (currentPhase /= AuctionOver) $ do
            slot       <- viewModelState currentSlot
            eSlot      <- viewContractState endBidSlot
            pSlot <- viewContractState payoutSlot
            when (slot >= eSlot) $ do
              phase $= AwaitingPayout
            when (slot >= pSlot) $ do
              phase $= PayoutTime

delay :: Integer -> Trace.EmulatorTrace ()
delay n = void $ Trace.waitNSlots $ fromIntegral n

prop_Auction :: DL AuctionModel () -> Property
prop_Auction script =
    forAll arbitrary $ \params ->
      forAllDL (action (Init params) >> script) $ \actions ->
        propRunActionsWithOptions (set minLogLevel Info options) (spec params)
          (\ _ -> pure True)  -- TODO: check termination
          actions
    where
        spec params = ContractInstanceSpec SellerH w1 (sellerContract params) :
                      [ ContractInstanceSpec (BidderH w) w (bidderContract params) | w <- [w2, w3, w4] ]

prop_AuctionModelCorrect :: Property
prop_AuctionModelCorrect = prop_Auction anyActions_

tests :: TestTree
tests =
  testGroup "sealed bid auction"
    [ testProperty "packInteger is injective" $ \x y -> x /= y ==> packInteger x /= packInteger y
    , testProperty "prop_AuctionModelCorrect" $ withMaxSuccess 20 prop_AuctionModelCorrect
    ]
