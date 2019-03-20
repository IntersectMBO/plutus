{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns
-fno-warn-name-shadowing
-fno-warn-unused-do-bind #-}


module Spec.Actus
    ( tests
    )
where

import qualified Data.Map.Strict         as Map
import           Hedgehog                (Property)
import           Test.Tasty
import           Test.Tasty.Hedgehog     (HedgehogTestLimit (..), testProperty)
import           Test.Tasty.HUnit

import           Language.Marlowe        hiding (discountFromPairList, insertCommit, mergeChoices)
import           Language.Marlowe.Actus  as Actus
import           Language.Marlowe.Client (commit', evalContract, receivePayment, redeem)
import           Ledger                  hiding (Value)
import qualified Ledger.Ada              as Ada
import           Spec.Common
import           Wallet.Emulator


tests :: TestTree
tests = testGroup "Actus"
        [ testCase "Safe zero coupon bond" checkZeroCouponBond
        , testCase "Trusted zero coupon bond" checkTrustedZeroCouponBond
        , localOption (HedgehogTestLimit $ Just 3) $
            testProperty "Safe zero coupon bond on mockchain" zeroCouponBondMockchainTest
        , localOption (HedgehogTestLimit $ Just 3) $
            testProperty "Safe zero coupon bond with guarantor on mockchain"
                zeroCouponBondGuaranteedMockchainTest
        ]


checkZeroCouponBond :: IO ()
checkZeroCouponBond = do
    let input cmd = Input cmd [] []
        state = State [] []
        notional = 1000
        discount = 80
        startDate = 50
        maturityDate = 500
        gracePeriod = 30240 -- about a week, 20sec * 3 * 60 * 24 * 7
        deposit = 12
        contract = zeroCouponBond (PubKey 1) (PubKey 2) notional discount startDate maturityDate gracePeriod
        eval = evalContract (PubKey 1)
    -- investor commits money for a bond with discount
    let (state1, con1, v) = eval (input $ Commit (IdentCC 1) (Signature 2)) (Slot 10)
                                    (Ada.fromInt deposit)
                                    (Ada.fromInt (notional - discount + deposit))
                                    state
                                    contract
    v @?= True
    -- issuer commits money for a bond redeem
    let (state2, con2, v) = eval (input $ Commit (IdentCC 2) (Signature 1)) (Slot 20)
                                    (Ada.fromInt (notional - discount + deposit))
                                    (Ada.fromInt (2*notional - discount + deposit))
                                    state1
                                    con1
    v @?= True
    -- issuer receives payment for a bond
    let (state3, con3, v) = eval (input $ Payment (IdentPay 1) (Signature 1)) (Slot 60)
                                    (Ada.fromInt (2*notional - discount + deposit))
                                    (Ada.fromInt (notional + deposit))
                                    state2
                                    con2
    v @?= True
    -- investor redeems a bond
    let (_, _, v) = eval (input $ Payment (IdentPay 2) (Signature 2)) (Slot 510)
                                    (Ada.fromInt (notional + deposit))
                                    (Ada.fromInt deposit)
                                    state3
                                    con3
    v @?= True
    -- issuer can't receive payment for a bond before start date
    let (_, _, v) = eval (input $ Payment (IdentPay 1) (Signature 1)) (Slot 49)
                                    (Ada.fromInt (2*notional - discount + deposit))
                                    (Ada.fromInt (notional + deposit))
                                    state2
                                    con2
    v @?= False


checkTrustedZeroCouponBond :: IO ()
checkTrustedZeroCouponBond = do
    let input cmd = Input cmd [] []
        state = State [] []
        notional = 1000
        discount = 80
        startDate = 50
        maturityDate = 500
        gracePeriod = 30240 -- about a week, 20sec * 3 * 60 * 24 * 7
        deposit = 12
        contract = trustedZeroCouponBond
                        (PubKey 1)
                        (PubKey 2)
                        notional
                        discount
                        startDate
                        maturityDate
                        gracePeriod
        eval = evalContract (PubKey 1)
    -- investor commits money for a bond with discount
    let (state1, con1, v) = eval (input $ Commit (IdentCC 1) (Signature 2)) (Slot 10)
                                    (Ada.fromInt deposit)
                                    (Ada.fromInt (notional - discount + deposit))
                                    state
                                    contract
    v @?= True
    -- issuer receives payment for a bond
    let (state2, con2, v) = eval (input $ Payment (IdentPay 1) (Signature 1)) (Slot 60)
                                    (Ada.fromInt (notional - discount + deposit))
                                    (Ada.fromInt deposit)
                                    state1
                                    con1
    v @?= True
    -- issuer commits money for a bond redeem
    let (state3, con3, v) = eval (input $ Commit (IdentCC 2) (Signature 1)) (Slot 450)
                                    (Ada.fromInt deposit)
                                    (Ada.fromInt (notional + deposit))
                                    state2
                                    con2
    v @?= True

    -- investor redeems a bond
    let (_, _, v) = eval (input $ Payment (IdentPay 2) (Signature 2)) (Slot 510)
                                    (Ada.fromInt (notional + deposit))
                                    (Ada.fromInt deposit)
                                    state3
                                    con3
    v @?= True
    -- issuer can't receive payment for a bond before start date
    let (_, _, v) = eval (input $ Payment (IdentPay 1) (Signature 1)) (Slot 49)
                                    (Ada.fromInt (2*notional - discount + deposit))
                                    (Ada.fromInt (notional + deposit))
                                    state1
                                    con1
    v @?= False


zeroCouponBondMockchainTest :: Property
zeroCouponBondMockchainTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, Ada.adaValueOf 1000000), (PubKey 2, Ada.adaValueOf 1000000) ] }) $ do
    -- Init a contract
    let issuer = Wallet 1
        issuerPk = PubKey 1
        investor = Wallet 2
        investorPk = PubKey 2
        update = updateAll [issuer, investor]
        notional = 1000
        discount = 80
        startDate = 50
        maturityDate = 500
        gracePeriod = 30240 -- about a week, 20sec * 3 * 60 * 24 * 7
    update

    let contract = zeroCouponBond (PubKey 1) (PubKey 2) notional discount startDate maturityDate gracePeriod

    withContract [issuer, investor] contract $ \txOut validator -> do
        txOut <- investor `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 1)
            (notional - discount)
            emptyState
            contract

        update

        txOut <- issuer `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 2)
            notional
            (State [ (IdentCC 1, (PubKey 2, NotRedeemed (notional - discount) maturityDate))] [])
            (CommitCash (IdentCC 2) issuerPk (Value notional) startDate (maturityDate + gracePeriod)
                (When FalseObs startDate Null
                    (Pay (IdentPay 1) investorPk issuerPk (Committed (IdentCC 1)) maturityDate
                        (When FalseObs maturityDate Null
                            (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 2))
                                (maturityDate + gracePeriod) Null)
                        )
                    )
                )
                Null
            )

        addBlocksAndNotify [issuer, investor] (startDate + 10)

        txOut <- issuer `performs` receivePayment txOut
            validator
            [] []
            (IdentPay 1)
            (notional - discount)
            (State [(IdentCC 2, (PubKey 1, NotRedeemed notional (maturityDate + gracePeriod)))] [])
            (When FalseObs maturityDate Null
                (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 2))
                    (maturityDate + gracePeriod) Null)
            )

        addBlocksAndNotify [issuer, investor] maturityDate

        txOut <- investor `performs` receivePayment txOut
            validator
            [] []
            (IdentPay 2)
            notional
            (State [] [])
            Null

        return (txOut, State [] [])
    return ()


zeroCouponBondGuaranteedMockchainTest :: Property
zeroCouponBondGuaranteedMockchainTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList    [ (PubKey 1, Ada.adaValueOf 1000000)
                                        , (PubKey 2, Ada.adaValueOf 1000000)
                                        , (PubKey 3, Ada.adaValueOf 1000000) ] }) $ do
    -- Init a contract
    let issuer = Wallet 1
        issuerPk = PubKey 1
        investor = Wallet 2
        investorPk = PubKey 2
        guarantor = Wallet 3
        guarantorPk = PubKey 3
        update = updateAll [issuer, investor, guarantor]
        notional = 1000
        discount = 80
        startDate = 50
        maturityDate = 500
        gracePeriod = 30240 -- about a week, 20sec * 3 * 60 * 24 * 7
    update

    let contract = zeroCouponBondGuaranteed
                        (PubKey 1) (PubKey 2) (PubKey 3) -- parties
                        notional discount -- values
                        startDate maturityDate gracePeriod -- dates

    withContract [issuer, investor, guarantor] contract $ \txOut validator -> do
        -- investor commits money for a bond with discount
        txOut <- investor `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 1)
            (notional - discount)
            emptyState
            contract

        update

        -- guarantor commits a guarantee
        txOut <- guarantor `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 2)
            notional
            (State [ (IdentCC 1, (PubKey 2, NotRedeemed (notional - discount) maturityDate))] [])
            (CommitCash (IdentCC 2) guarantorPk (Value notional) startDate (maturityDate + gracePeriod)
                (When FalseObs startDate Null
                    (Pay (IdentPay 1) investorPk issuerPk (Committed (IdentCC 1)) maturityDate
                        (CommitCash (IdentCC 3) issuerPk (Value notional) maturityDate (maturityDate + gracePeriod)
                            -- if the issuer commits the notional before maturity date pay from it, redeem the 'guarantee'
                            (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 3))
                                (maturityDate + gracePeriod) (RedeemCC (IdentCC 2) Null))
                            -- pay from the guarantor otherwise
                            (Pay (IdentPay 3) guarantorPk investorPk (Committed (IdentCC 2))
                                (maturityDate + gracePeriod) Null)
                        )
                    )
                )
                Null
            )

        addBlocksAndNotify [issuer, investor, guarantor] (startDate + 10)

        -- after startDate the issuer recevies the bond payment
        txOut <- issuer `performs` receivePayment txOut
            validator
            [] []
            (IdentPay 1)
            (notional - discount)
            (State [(IdentCC 2, (PubKey 3, NotRedeemed notional (maturityDate + gracePeriod)))] [])
            (CommitCash (IdentCC 3) issuerPk (Value notional) maturityDate (maturityDate + gracePeriod)
                -- if the issuer commits the notional before maturity date pay from it, redeem the 'guarantee'
                (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 3))
                    (maturityDate + gracePeriod) (RedeemCC (IdentCC 2) Null))
                -- pay from the guarantor otherwise
                (Pay (IdentPay 3) guarantorPk investorPk (Committed (IdentCC 2))
                    (maturityDate + gracePeriod) Null)
            )

        addBlocksAndNotify [issuer, investor, guarantor] 100

        -- before maturityDate the issuer commits the bond value
        txOut <- issuer `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 3)
            notional
            (State [(IdentCC 2, (PubKey 3, NotRedeemed notional (maturityDate + gracePeriod)))] [])
            (CommitCash (IdentCC 3) issuerPk (Value notional) maturityDate (maturityDate + gracePeriod)
                -- if the issuer commits the notional before maturity date pay from it, redeem the 'guarantee'
                (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 3))
                    (maturityDate + gracePeriod) (RedeemCC (IdentCC 2) Null))
                -- pay from the guarantor otherwise
                (Pay (IdentPay 3) guarantorPk investorPk (Committed (IdentCC 2))
                    (maturityDate + gracePeriod) Null)
            )

        addBlocksAndNotify [issuer, investor, guarantor] maturityDate

        -- after maturity date the investor collects the bond payment
        txOut <- investor `performs` receivePayment txOut
            validator
            [] []
            (IdentPay 2)
            notional
            (State  [ (IdentCC 2, (PubKey 3, NotRedeemed notional (maturityDate + gracePeriod)))] [])
            (RedeemCC (IdentCC 2) Null)

        update

        -- after that guarantor can recall the `guarantee` commit
        txOut <- guarantor `performs` redeem
            txOut
            validator
            [] []
            (IdentCC 2)
            notional
            (State [] [])
            Null

        return (txOut, State [] [])
    return ()
