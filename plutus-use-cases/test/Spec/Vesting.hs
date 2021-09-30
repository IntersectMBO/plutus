{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-unused-do-bind -fno-warn-name-shadowing #-}
module Spec.Vesting (tests, prop_Vesting, prop_CheckNoLockedFundsProof, retrieveFundsTrace) where

import           Control.Lens                       hiding (elements)
import           Control.Monad                      (void, when)
import           Data.Default                       (Default (def))
import           Test.Tasty
import qualified Test.Tasty.HUnit                   as HUnit
import           Test.Tasty.QuickCheck              (testProperty)

import qualified Ledger
import qualified Ledger.Ada                         as Ada
import           Ledger.Slot
import           Ledger.Time                        (POSIXTime)
import qualified Ledger.TimeSlot                    as TimeSlot
import           Ledger.Value
import           Plutus.Contract.Test               hiding (not)
import           Plutus.Contract.Test.ContractModel
import           Plutus.Contracts.Vesting
import           Plutus.Trace.Emulator              (EmulatorTrace, callEndpoint)
import qualified Plutus.Trace.Emulator              as Trace
import qualified PlutusTx
import qualified PlutusTx.Numeric                   as Numeric
import           Prelude
import           Test.QuickCheck                    hiding ((.&&.))

-- | The scenario used in the property tests. It sets up a vesting scheme for a
--   total of 60 lovelace over 20 blocks (20 lovelace can be taken out before
--   that, at 10 blocks).
vesting :: POSIXTime -> VestingParams
vesting startTime =
    VestingParams
        { vestingTranche1 = VestingTranche (startTime + 10000) (Ada.lovelaceValueOf 20)
        , vestingTranche2 = VestingTranche (startTime + 20000) (Ada.lovelaceValueOf 40)
        , vestingOwner    = Ledger.pubKeyHash $ walletPubKey w1 }

params :: VestingParams
params = vesting (TimeSlot.scSlotZeroTime def)

-- * QuickCheck model

data VestingModel =
  VestingModel { _vestedAmount :: Value -- ^ How much value is in the contract
               , _vested       :: [Wallet] -- ^ What wallets have already vested money
               , _t1Slot       :: Slot -- ^ The time for the first tranche
               , _t2Slot       :: Slot -- ^ The time for the second tranche
               , _t1Amount     :: Value -- ^ The size of the first tranche
               , _t2Amount     :: Value -- ^ The size of the second tranche
               } deriving (Show, Eq)

makeLenses 'VestingModel

deriving instance Eq (ContractInstanceKey VestingModel w schema err)
deriving instance Show (ContractInstanceKey VestingModel w schema err)

-- This instance models the behaviour of the vesting contract. There are some peculiarities
-- that stem from the implementation of the contract that are apparent in the precondition
-- to the `Vest` endpoint.
instance ContractModel VestingModel where
  data ContractInstanceKey VestingModel w schema err where
    WalletKey :: Wallet -> ContractInstanceKey VestingModel () VestingSchema VestingError

  data Action VestingModel = Vest Wallet
                           | Retrieve Wallet Value
                           | WaitUntil Slot
                           deriving (Eq, Show)

  initialState = VestingModel
    { _vestedAmount = mempty
    , _vested       = []
    , _t1Slot       = TimeSlot.posixTimeToEnclosingSlot def $ vestingTrancheDate (vestingTranche1 params)
    , _t2Slot       = TimeSlot.posixTimeToEnclosingSlot def $ vestingTrancheDate (vestingTranche2 params)
    , _t1Amount     = vestingTrancheAmount (vestingTranche1 params)
    , _t2Amount     = vestingTrancheAmount (vestingTranche2 params) }

  perform handle _ cmd = case cmd of
    Vest w -> do
      callEndpoint @"vest funds" (handle $ WalletKey w) ()
      delay 1

    Retrieve w val -> do
      callEndpoint @"retrieve funds" (handle $ WalletKey w) val
      delay 2

    WaitUntil slot -> void $ Trace.waitUntilSlot slot

  -- Vest the sum of the two tranches
  nextState (Vest w) = do
    let amount =  vestingTrancheAmount (vestingTranche1 params)
               <> vestingTrancheAmount (vestingTranche2 params)
    withdraw w amount
    vestedAmount $~ (<> amount)
    vested       $~ (w:)
    wait 1

  -- Retrieve `v` value as long as that leaves enough value to satisfy
  -- the tranche requirements
  nextState (Retrieve w v) = do
    slot   <- viewModelState currentSlot
    amount <- viewContractState vestedAmount
    s      <- getContractState
    when ( enoughValueLeft slot s v
         && v `leq` amount
         && Ledger.pubKeyHash (walletPubKey w) == vestingOwner params) $ do
      deposit w v
      vestedAmount $= (amount Numeric.- v)
    wait 2

  nextState (WaitUntil s) = do
    slot <- viewModelState currentSlot
    when (slot < s) $ do
      waitUntil s

  precondition s (Vest w) =  w `notElem` s ^. contractState . vested -- After a wallet has vested the contract shuts down
                          && Ledger.pubKeyHash (walletPubKey w) /= vestingOwner params -- The vesting owner shouldn't vest
                          && slot < t1 -- If you vest after slot 1 it can cause the vesting owner to terminate prematurely
    where
      slot   = s ^. currentSlot
      t1     = s ^. contractState . t1Slot

  precondition s (Retrieve w v) = enoughValueLeft slot (s ^. contractState) v
                                && Ledger.pubKeyHash (walletPubKey w) == vestingOwner params
    where
      slot   = s ^. currentSlot


  precondition s (WaitUntil slot') = s ^. currentSlot < slot'

  arbitraryAction s = frequency [ (1, Vest <$> genWallet)
                                , (1, Retrieve <$> genWallet
                                           <*> (Ada.lovelaceValueOf
                                                <$> choose (0, (valueOf amount Ada.adaSymbol Ada.adaToken))))
                                , (1, WaitUntil . Slot <$> choose (n+1, n+30 :: Integer)) ]
    where
      amount   = s ^. contractState . vestedAmount
      (Slot n) = s ^. currentSlot

  shrinkAction _ (Vest _)             = []
  shrinkAction _ (Retrieve w v)       = Retrieve w <$> shrinkValue v
  shrinkAction _ (WaitUntil (Slot n)) = [ WaitUntil (Slot n') | n' <- shrink n ]

-- | Check that the amount of value left in the contract
-- is at least the amount that remains locked at the current
-- slot.
enoughValueLeft :: Slot -- ^ current slot
                -> VestingModel
                -> Value
                -> Bool
enoughValueLeft slot s take =
  let availableValue   = mconcat $ [ t1v | slot > t1 ] ++ [ t2v | slot > t2 ]
      totalValue       = t1v <> t2v
      mustRemainLocked = totalValue Numeric.- availableValue
  in mustRemainLocked `leq` (vested Numeric.- take)
  where
    vested = s ^. vestedAmount
    t1     = s ^. t1Slot
    t1v    = s ^. t1Amount
    t2     = s ^. t2Slot
    t2v    = s ^. t2Amount

wallets :: [Wallet]
wallets = [w1, w2, w3]

genWallet :: Gen Wallet
genWallet = elements wallets

shrinkValue :: Value -> [Value]
shrinkValue v = Ada.lovelaceValueOf <$> (shrink (valueOf v Ada.adaSymbol Ada.adaToken))

handleSpec :: [ContractInstanceSpec VestingModel]
handleSpec = [ ContractInstanceSpec (WalletKey w) w (vestingContract params) | w <- [w1, w2, w3] ]

prop_Vesting :: Actions VestingModel -> Property
prop_Vesting = propRunActions_ handleSpec

noLockProof :: NoLockedFundsProof VestingModel
noLockProof = NoLockedFundsProof{
      nlfpMainStrategy   = mainStrat,
      nlfpWalletStrategy = walletStrat }
    where
        -- To get all the money out simply wait until after the
        -- deadline and take as much money as has been vested.
        mainStrat = do
            amount <- viewContractState vestedAmount
            t2     <- viewContractState t2Slot
            slot   <- viewModelState currentSlot
            when (slot < t2 + Slot 1) $ do
              action (WaitUntil $ t2 + Slot 1)
            when (amount `gt` mempty) $ do
              action (Retrieve w1 amount)

        -- No one but w1 ever gets any money out of the contract.
        walletStrat w | w == w1 = mainStrat
                      | otherwise = return ()

prop_CheckNoLockedFundsProof :: Property
prop_CheckNoLockedFundsProof = checkNoLockedFundsProof defaultCheckOptions handleSpec noLockProof

-- Tests

tests :: TestTree
tests =
    let con = vestingContract (vesting startTime) in
    testGroup "vesting"
    [ checkPredicate "secure some funds with the vesting script"
        (walletFundsChange w2 (Numeric.negate $ totalAmount $ vesting startTime))
        $ do
            hdl <- Trace.activateContractWallet w2 con
            Trace.callEndpoint @"vest funds" hdl ()
            void $ Trace.waitNSlots 1

    , checkPredicate "retrieve some funds"
        (walletFundsChange w2 (Numeric.negate $ totalAmount $ vesting startTime)
        .&&. assertNoFailedTransactions
        .&&. walletFundsChange w1 (Ada.lovelaceValueOf 10))
        retrieveFundsTrace

    , checkPredicate "cannot retrieve more than allowed"
        (walletFundsChange w1 mempty
        .&&. assertContractError con (Trace.walletInstanceTag w1) (== expectedError) "error should match")
        $ do
            hdl1 <- Trace.activateContractWallet w1 con
            hdl2 <- Trace.activateContractWallet w2 con
            Trace.callEndpoint @"vest funds" hdl2 ()
            Trace.waitNSlots 10
            Trace.callEndpoint @"retrieve funds" hdl1 (Ada.lovelaceValueOf 30)
            void $ Trace.waitNSlots 1

    , checkPredicate "can retrieve everything at the end"
        (walletFundsChange w1 (totalAmount $ vesting startTime)
        .&&. assertNoFailedTransactions
        .&&. assertDone con (Trace.walletInstanceTag w1) (const True) "should be done")
        $ do
            hdl1 <- Trace.activateContractWallet w1 con
            hdl2 <- Trace.activateContractWallet w2 con
            Trace.callEndpoint @"vest funds" hdl2 ()
            Trace.waitNSlots 20
            Trace.callEndpoint @"retrieve funds" hdl1 (totalAmount $ vesting startTime)
            void $ Trace.waitNSlots 2

    , goldenPir "test/Spec/vesting.pir" $$(PlutusTx.compile [|| validate ||])
    , HUnit.testCaseSteps "script size is reasonable" $ \step -> reasonable' step (vestingScript $ vesting startTime) 33000
    , testProperty "prop_Vesting" $ withMaxSuccess 20 prop_Vesting
    , testProperty "prop_CheckNoLockedFundsProof" $ withMaxSuccess 20 prop_CheckNoLockedFundsProof
    ]

    where
        startTime = TimeSlot.scSlotZeroTime def

-- | The scenario used in the property tests. It sets up a vesting scheme for a
--   total of 60 lovelace over 20 blocks (20 lovelace can be taken out before
--   that, at 10 blocks).
vesting :: POSIXTime -> VestingParams
vesting startTime =
    VestingParams
        { vestingTranche1 = VestingTranche (startTime + 10000) (Ada.lovelaceValueOf 20)
        , vestingTranche2 = VestingTranche (startTime + 20000) (Ada.lovelaceValueOf 40)
        , vestingOwner    = walletPubKeyHash w1 }

retrieveFundsTrace :: EmulatorTrace ()
retrieveFundsTrace = do
    startTime <- TimeSlot.scSlotZeroTime <$> Trace.getSlotConfig
    let con = vestingContract (vesting startTime)
    hdl1 <- Trace.activateContractWallet w1 con
    hdl2 <- Trace.activateContractWallet w2 con
    Trace.callEndpoint @"vest funds" hdl2 ()
    Trace.waitNSlots 10
    Trace.callEndpoint @"retrieve funds" hdl1 (Ada.lovelaceValueOf 10)
    void $ Trace.waitNSlots 2

expectedError :: VestingError
expectedError =
    let payment = Ada.lovelaceValueOf 30
        maxPayment = Ada.lovelaceValueOf 20
        mustRemainLocked = Ada.lovelaceValueOf 40
    in InsufficientFundsError payment maxPayment mustRemainLocked


-- Util
delay :: Integer -> Trace.EmulatorTrace ()
delay n = void $ Trace.waitNSlots $ fromIntegral n
