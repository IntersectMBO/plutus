{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns
-fno-warn-name-shadowing
-fno-warn-unused-do-bind #-}
module Spec.Actus
    ( tests
    )
where

import qualified Data.Map.Strict                as Map
import           Hedgehog                       ( Property
                                                )
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog            ( testProperty
                                                )

import           Ledger                  hiding ( Value )
import qualified Ledger.Ada                     as Ada
import           Wallet.Emulator
import           Language.Marlowe        hiding (insertCommit, discountFromPairList, mergeChoices)
import           Language.Marlowe.Client        ( commit'
                                                , receivePayment
                                                , evalContract
                                                )
import           Language.Marlowe.Actus        as Actus
import           Spec.Common


tests :: TestTree
tests = testGroup "Actus"
        [ testCase "Safe zero coupon bond" checkZeroCouponBond
        , testCase "Trusted zero coupon bond" checkTrustedZeroCouponBond
        , testProperty "Trusted zero coupon bond" zeroCouponBondTest
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


zeroCouponBondTest :: Property
zeroCouponBondTest = checkMarloweTrace (MarloweScenario {
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
            (notional-discount)
            (State [(IdentCC 1, (PubKey 1, NotRedeemed (notional-discount) maturityDate))] [])
            (CommitCash (IdentCC 2) issuerPk (Value notional) startDate (maturityDate+1000)
                (When FalseObs startDate Null
                    (Pay (IdentPay 1) investorPk issuerPk (Committed (IdentCC 1)) maturityDate
                        (When FalseObs maturityDate Null
                            (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 2)) (maturityDate+1000) Null)
                        )
                    )
                )
                Null
            )

        update

        txOut <- issuer `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 2)
            notional
            (State [ (IdentCC 1, (PubKey 1, NotRedeemed (notional-discount) maturityDate)),
                        (IdentCC 2, (PubKey 2, NotRedeemed notional maturityDate))] [])
            (When FalseObs startDate Null
                (Pay (IdentPay 1) investorPk issuerPk (Committed (IdentCC 1)) maturityDate
                    (When FalseObs maturityDate Null
                        (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 2)) (maturityDate+1000) Null)
                    )
                )
            )

        addBlocksAndNotify [issuer, investor] startDate

        txOut <- issuer `performs` receivePayment txOut
            validator
            [] []
            (IdentPay 1)
            (notional-discount)
            (State [(IdentCC 2, (PubKey 2, NotRedeemed notional (maturityDate+1000)))] [])
            (When FalseObs maturityDate Null
                (Pay (IdentPay 2) issuerPk investorPk (Committed (IdentCC 2)) (maturityDate+1000) Null)
            )

        addBlocksAndNotify [issuer, investor] maturityDate

        txOut <- investor `performs` receivePayment txOut
            validator
            [] []
            (IdentPay 1)
            notional
            (State [] [])
            Null

        return (txOut, State [] [])
    return ()
