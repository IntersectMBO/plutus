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

import           Data.Either                    ( isRight )
import           Data.Maybe
import           Control.Monad                  ( void, when )
import           Data.Set                       ( Set )
import qualified Data.List                      as List
import qualified Data.Set                       as Set
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict                as Map

import           Hedgehog                       ( Gen
                                                , Property
                                                , Size(..)
                                                , forAll
                                                , property
                                                )
import qualified Hedgehog.Range                 as Range
import           Hedgehog.Gen                   ( element
                                                , int
                                                , choice
                                                , list
                                                , sized
                                                )
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog            ( testProperty
                                                , HedgehogTestLimit(..)
                                                )

import           Ledger                  hiding ( Value )
import qualified Ledger.Ada                     as Ada
import qualified Ledger
import           Ledger.Validation              ( OracleValue(..) )
import           Wallet                         ( PubKey(..)
                                                , startWatching
                                                )
import           Wallet.Emulator
import qualified Wallet.Generators              as Gen
import           Language.Marlowe        hiding (insertCommit, discountFromPairList, mergeChoices)
import qualified Language.Marlowe               as Marlowe
import           Language.Marlowe.Client        ( commit'
                                                , commit
                                                , redeem
                                                , createContract
                                                , spendDeposit
                                                , receivePayment
                                                , marloweValidator
                                                , evalContract
                                                )
import           Language.Marlowe.Actus        as Actus

newtype MarloweScenario = MarloweScenario { mlInitialBalances :: Map.Map PubKey Ledger.Value }
data Bounds = Bounds {
    oracleBounds :: Map PubKey (Integer, Integer),
    choiceBounds :: Map IdentChoice (Integer, Integer)
}

emptyBounds :: Bounds
emptyBounds = Bounds Map.empty Map.empty


tests :: TestTree
tests = testGroup "Actus"
        [ testCase "Safe zero coupon bond" checkZeroCouponBond
        , testCase "Trusted zero coupon bond" checkTrustedZeroCouponBond
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
