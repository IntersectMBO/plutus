{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-unused-do-bind #-}
module Spec.Vesting(tests, retrieveFundsTrace, vesting) where

import           Test.Tasty
import qualified Test.Tasty.HUnit                                 as HUnit

import           Spec.Lib                                         as Lib

import qualified Language.PlutusTx                                as PlutusTx
import           Language.PlutusTx.Coordination.Contracts.Vesting
import           Language.PlutusTx.Lattice
import qualified Language.PlutusTx.Numeric                        as Numeric
import qualified Ledger
import qualified Ledger.Ada                                       as Ada

import           Language.Plutus.Contract.Test
import           Prelude                                          hiding (not)

wallet1, wallet2 :: Wallet
wallet1 = Wallet 1
wallet2 = Wallet 2

tests :: TestTree
tests =
    let con = vestingContract vesting in
    testGroup "vesting"
    [ checkPredicate "secure some funds with the vesting script"
        con
        (walletFundsChange wallet2 (Numeric.negate $ totalAmount vesting))
        ( callEndpoint @"vest funds" wallet2 ()
        >> handleBlockchainEvents wallet2
        >> addBlocks 1
        )

    , checkPredicate "retrieve some funds"
        con
        (walletFundsChange wallet2 (Numeric.negate $ totalAmount vesting)
        /\ assertNoFailedTransactions
        /\ walletFundsChange wallet1 (Ada.lovelaceValueOf 10))
        retrieveFundsTrace

    , checkPredicate "cannot retrieve more than allowed"
        con
        (walletFundsChange wallet1 mempty
        /\ assertContractError wallet1 (== expectedError) "error should match")
        (callEndpoint @"vest funds" wallet2 ()
        >> handleBlockchainEvents wallet2
        >> addBlocks 10
        >> callEndpoint @"retrieve funds" wallet1 (Ada.lovelaceValueOf 30)
        >> notifySlot wallet1
        >> addBlocks 1
        >> handleBlockchainEvents wallet1)

    , checkPredicate "can retrieve everything at the end"
        con
        (walletFundsChange wallet1 (totalAmount vesting)
        /\ assertNoFailedTransactions
        /\ assertDone wallet1 (const True) "should be done")
        (callEndpoint @"vest funds" wallet2 ()
        >> handleBlockchainEvents wallet2
        >> addBlocks 20
        >> callEndpoint @"retrieve funds" wallet1 (totalAmount vesting)
        >> notifySlot wallet1
        >> handleBlockchainEvents wallet1
        >> addBlocks 1
        )

    , Lib.goldenPir "test/Spec/vesting.pir" $$(PlutusTx.compile [|| validate ||])
    , HUnit.testCase "script size is reasonable" (Lib.reasonable (vestingScript vesting) 33000)
    ]

-- | The scenario used in the property tests. It sets up a vesting scheme for a
--   total of 60 lovelace over 20 blocks (20 lovelace can be taken out before
--   that, at 10 blocks).
vesting :: VestingParams
vesting =
    VestingParams
        { vestingTranche1 = VestingTranche (Ledger.Slot 10) (Ada.lovelaceValueOf 20)
        , vestingTranche2 = VestingTranche (Ledger.Slot 20) (Ada.lovelaceValueOf 40)
        , vestingOwner    = Ledger.pubKeyHash $ walletPubKey wallet1 }

retrieveFundsTrace
    :: ( MonadEmulator (TraceError e) m )
    => ContractTrace VestingSchema e m () ()
retrieveFundsTrace = do
    callEndpoint @"vest funds" wallet2 ()
    handleBlockchainEvents wallet2
    addBlocks 10
    callEndpoint @"retrieve funds" wallet1 (Ada.lovelaceValueOf 10)
    addBlocks 1
    handleBlockchainEvents wallet1
    addBlocks 1

expectedError :: TraceError VestingError
expectedError =
    let payment = Ada.lovelaceValueOf 30
        maxPayment = Ada.lovelaceValueOf 20
        mustRemainLocked = Ada.lovelaceValueOf 40
    in TContractError
        $ InsufficientFundsError
            payment
            maxPayment
            mustRemainLocked
