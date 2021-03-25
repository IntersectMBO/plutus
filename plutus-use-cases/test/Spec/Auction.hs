{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
module Spec.Auction(tests, auctionTrace1, auctionTrace2,
                    prop_Auction, prop_FinishAuction) where

import           Control.Lens
import           Control.Monad                      (void, when)
import           Control.Monad.Freer.Extras.Log     (LogLevel (..))
import           Data.Semigroup                     (Last (..))

import           Ledger                             (Ada, Slot (..), Value, pubKeyHash)
import qualified Ledger.Ada                         as Ada
import           Plutus.Contract                    hiding (currentSlot, when)
import           Plutus.Contract.Test               hiding (not)

import qualified Ledger.Value                       as Value
import qualified Plutus.Contract.StateMachine       as SM
import           Plutus.Contract.Test.ContractModel
import           Plutus.Contracts.Auction           hiding (Bid)
import qualified Plutus.Trace.Emulator              as Trace
import           PlutusTx.Monoid                    (inv)

import           Test.QuickCheck                    hiding ((.&&.))
import           Test.Tasty

tests :: TestTree
tests =
    testGroup "auction"
        [ checkPredicateOptions options "run an auction"
            (assertDone seller (Trace.walletInstanceTag w1) (const True) "seller should be done"
            .&&. assertDone buyer (Trace.walletInstanceTag w2) (const True) "buyer should be done"
            .&&. assertAccumState buyer (Trace.walletInstanceTag w2) ((==) (Just $ Last trace1FinalState)) "final state should be OK"
            .&&. walletFundsChange w1 (Ada.toValue trace1WinningBid <> inv theToken)
            .&&. walletFundsChange w2 (inv (Ada.toValue trace1WinningBid) <> theToken))
            auctionTrace1
        , checkPredicateOptions options "run an auction with multiple bids"
            (assertDone seller (Trace.walletInstanceTag w1) (const True) "seller should be done"
            .&&. assertDone buyer (Trace.walletInstanceTag w2) (const True) "buyer should be done"
            .&&. assertDone buyer (Trace.walletInstanceTag w3) (const True) "3rd party should be done"
            .&&. assertAccumState buyer (Trace.walletInstanceTag w2) ((==) (Just $ Last trace2FinalState)) "final state should be OK"
            .&&. walletFundsChange w1 (Ada.toValue trace2WinningBid <> inv theToken)
            .&&. walletFundsChange w2 (inv (Ada.toValue trace2WinningBid) <> theToken)
            .&&. walletFundsChange w3 mempty)
            auctionTrace2
        ]

params :: AuctionParams
params =
    AuctionParams
        { apOwner   = pubKeyHash $ walletPubKey (Wallet 1)
        , apAsset   = theToken
        , apEndTime = 100

        }

-- | The token that we are auctioning off.
theToken :: Value
theToken =
    -- "ffff" is not a valid MPS hash. But this doesn't matter because we
    -- never try to forge any value of "ffff" using a script.
    -- This currency is created by the initial transaction.
    Value.singleton "ffff" "token" 1

-- | 'CheckOptions' that inclues 'theToken' in the initial distribution of wallet 1.
options :: CheckOptions
options =
    let initialDistribution = defaultDist & over (at (Wallet 1) . _Just) ((<>) theToken)
    in defaultCheckOptions & emulatorConfig . Trace.initialChainState .~ Left initialDistribution

seller :: Contract (Maybe (Last AuctionState)) SellerSchema SM.SMContractError ()
seller = auctionSeller (apAsset params) (apEndTime params)

buyer :: Contract (Maybe (Last AuctionState)) BuyerSchema SM.SMContractError ()
buyer = auctionBuyer params

w1, w2, w3 :: Wallet
w1 = Wallet 1
w2 = Wallet 2
w3 = Wallet 3

trace1WinningBid :: Ada
trace1WinningBid = 50

auctionTrace1 :: Trace.EmulatorTrace ()
auctionTrace1 = do
    _ <- Trace.activateContractWallet w1 seller
    _ <- Trace.waitNSlots 1
    hdl2 <- Trace.activateContractWallet w2 buyer
    _ <- Trace.waitNSlots 1     -- waiting an even multiple of 3 here makes test fail!
    Trace.callEndpoint @"bid" hdl2 trace1WinningBid
    void $ Trace.waitUntilSlot (succ $ succ $ apEndTime params)

trace2WinningBid :: Ada
trace2WinningBid = 70

auctionTrace2 :: Trace.EmulatorTrace ()
auctionTrace2 = do
    _ <- Trace.activateContractWallet w1 seller
    _ <- Trace.waitNSlots 1
    hdl2 <- Trace.activateContractWallet w2 buyer
    hdl3 <- Trace.activateContractWallet w3 buyer
    _ <- Trace.waitNSlots 1
    Trace.callEndpoint @"bid" hdl2 50
    _ <- Trace.waitNSlots 15
    Trace.callEndpoint @"bid" hdl3 60
    _ <- Trace.waitNSlots 35
    Trace.callEndpoint @"bid" hdl2 trace2WinningBid
    void $ Trace.waitUntilSlot (succ $ succ $ apEndTime params)

trace1FinalState :: AuctionState
trace1FinalState =
    Finished $
        HighestBid
            { highestBid = trace1WinningBid
            , highestBidder = pubKeyHash (walletPubKey w2)
            }

trace2FinalState :: AuctionState
trace2FinalState =
    Finished $
        HighestBid
            { highestBid = trace2WinningBid
            , highestBidder = pubKeyHash (walletPubKey w2)
            }

-- * QuickCheck model

data AuctionModel = AuctionModel
    { _currentBid :: Integer
    , _winner     :: Wallet
    , _endSlot    :: Slot
    , _phase      :: Phase }
    deriving (Show)

data Phase = NotStarted | Bidding | AuctionOver
    deriving (Eq, Show)

makeLenses 'AuctionModel

deriving instance Eq (ContractInstanceKey AuctionModel w s e)
deriving instance Show (ContractInstanceKey AuctionModel w s e)

instance ContractModel AuctionModel where

    data ContractInstanceKey AuctionModel w s e where
        SellerH :: ContractInstanceKey AuctionModel (Maybe (Last AuctionState)) SellerSchema SM.SMContractError
        BuyerH  :: Wallet -> ContractInstanceKey AuctionModel (Maybe (Last AuctionState)) BuyerSchema SM.SMContractError

    data Action AuctionModel = Init | Bid Wallet Integer | WaitUntil Slot
        deriving (Eq, Show)

    initialState = AuctionModel { _currentBid = 0
                                , _winner     = w1
                                , _endSlot    = apEndTime params
                                , _phase      = NotStarted }

    arbitraryAction s
        | p /= NotStarted =
            oneof [ WaitUntil . step <$> choose (1, 10 :: Integer)
                  , Bid  <$> (Wallet <$> choose (2, 4)) <*> choose (1, 1000) ]
        | otherwise = pure Init
        where
            p    = s ^. contractState . phase
            slot = s ^. currentSlot
            step n = slot + fromIntegral n

    precondition s Init = s ^. contractState . phase == NotStarted
    precondition s cmd  = s ^. contractState . phase /= NotStarted &&
        case cmd of
            WaitUntil slot -> slot > s ^. currentSlot
            _              -> True

    -- This command is only for setting up the model state with theToken
    nextState cmd = do
        slot <- viewModelState currentSlot
        end  <- viewContractState endSlot
        case cmd of
            Init -> do
                phase $= Bidding
                withdraw w1 theToken
                wait 3
            WaitUntil slot' -> waitUntil slot'
            Bid w bid -> do
                current <- viewContractState currentBid
                leader  <- viewContractState winner
                wait 1
                when (bid > current && slot <= end) $ do
                    withdraw w $ Ada.lovelaceValueOf bid
                    deposit leader $ Ada.lovelaceValueOf current
                    currentBid $= bid
                    winner     $= w
        slot' <- viewModelState currentSlot
        p     <- viewContractState phase
        when (slot' > end && p == Bidding) $ do
            w   <- viewContractState winner
            bid <- viewContractState currentBid
            phase $= AuctionOver
            deposit w theToken
            deposit w1 $ Ada.lovelaceValueOf bid

    perform _ _ Init = delay 3
    perform _ _ (WaitUntil slot) = void $ Trace.waitUntilSlot slot
    perform handle _ (Bid w bid) = do
        Trace.callEndpoint @"bid" (handle $ BuyerH w) (Ada.lovelaceOf bid)
        delay 1

    shrinkAction _ Init      = []
    shrinkAction _ (WaitUntil (Slot n))  = [ WaitUntil (Slot n') | n' <- shrink n ]
    shrinkAction s (Bid w v) =
        [ WaitUntil (s ^. currentSlot + 1) ] ++
        [ Bid w v' | v' <- shrink v ]

    monitoring _ _ = id

delay :: Integer -> Trace.EmulatorTrace ()
delay n = void $ Trace.waitNSlots $ fromIntegral n

prop_Auction :: Actions AuctionModel -> Property
prop_Auction script =
    propRunActionsWithOptions (set minLogLevel Info options) spec
        (\ _ -> pure True)  -- TODO: check termination
        script
    where
        spec = ContractInstanceSpec SellerH w1 seller :
               [ ContractInstanceSpec (BuyerH w) w buyer | w <- map Wallet [2..4] ]

finishAuction :: DL AuctionModel ()
finishAuction = do
    action Init
    anyActions_
    slot <- viewModelState currentSlot
    when (slot < 101) $ action $ WaitUntil 101
    assertModel "Locked funds are not zero" (Value.isZero . lockedValue)

prop_FinishAuction :: Property
prop_FinishAuction = forAllDL finishAuction prop_Auction

