{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
module Spec.Contract(tests) where

import           Data.Either                           (isLeft)
import           Test.Tasty

import           Language.Plutus.Contract              as Con
import           Language.Plutus.Contract.Tx           as Tx
import qualified Language.Plutus.Contract.Prompt.Event as Event
import           Language.Plutus.Contract.Test
import           Language.Plutus.Contract.Util         (loopM)
import           Ledger                                (Address)
import qualified Ledger                                as Ledger
import qualified Ledger.Ada                            as Ada
import           Prelude                               hiding (not)
import qualified Wallet.Emulator                       as EM


someAddress :: Address
someAddress =
    -- this isn't the address of a valid validator script,
    -- but it doesn't matter because we only need the address,
    -- not the script
    Ledger.scriptAddress $
        Ledger.ValidatorScript $$(Ledger.compileScript [|| \(i :: Integer) -> i ||])

tests :: TestTree
tests = testGroup "contracts"
    [ checkPredicate "awaitSlot"
        (awaitSlot 10)
        (waitingForSlot w1 10)
        $ pure ()

    , checkPredicate "selectEither"
        (selectEither (awaitSlot 10) (awaitSlot 5))
        (waitingForSlot w1 5)
        $ pure ()

    , checkPredicate "until"
        (awaitSlot 10 `Con.until` 5)
        (waitingForSlot w1 5)
        $ pure ()

    , checkPredicate "both"
        (Con.both (awaitSlot 10) (awaitSlot 20))
        (waitingForSlot w1 10)
        $ pure ()

    , checkPredicate "both (2)"
        (Con.both (awaitSlot 10) (awaitSlot 20))
        (waitingForSlot w1 20)
        $ addEvent w1 (Event.changeSlot 10)

    , checkPredicate "fundsAtAddressGt"
        (fundsAtAddressGt someAddress (Ada.adaValueOf 10))
        (interestingAddress w1 someAddress)
        $ pure ()

    , checkPredicate "watchAddressUntil"
        (watchAddressUntil someAddress 5)
        (interestingAddress w1 someAddress <> waitingForSlot w1 5)
        $ pure ()

    , checkPredicate "endpoint"
        (endpoint @() "ep")
        (endpointAvailable w1 "ep")
        $ pure ()

    , checkPredicate "call endpoint (1)"
        (endpoint @Int "1" >> endpoint @Int "2")
        (endpointAvailable w1 "1")
        $ pure ()

    , checkPredicate "call endpoint (2)"
        (endpoint @Int "1" >> endpoint @Int "2")
          (endpointAvailable w1 "2" <> not (endpointAvailable w1 "1"))
        (callEndpoint w1 "1" (1::Int))

    , checkPredicate "call endpoint (3)"
        (endpoint @Int "1" >> endpoint @Int "2")
          (not (endpointAvailable w1 "2") <> not (endpointAvailable w1 "1"))
        (callEndpoint w1 "1" (1::Int) >> callEndpoint w1 "2" (1::Int))

    , checkPredicate "submit tx"
        (writeTx Tx.emptyTx >> watchAddressUntil someAddress 20)
        (waitingForSlot w1 20 <> interestingAddress w1 someAddress)
        (handleBlockchainEvents w1)

    , checkPredicate "select either"
        (let l = endpoint @() "1" >> endpoint @() "2"
             r = endpoint @() "3" >> endpoint @() "4"
        in selectEither l r)
        (assertResult w1 $ maybe False isLeft)
        (callEndpoint w1 "3" () >> callEndpoint w1 "1" () >> callEndpoint w1 "2" ())

    , checkPredicate "loopM"
        (loopM (\_ -> Left <$> endpoint @Int "1") 0)
        (endpointAvailable w1 "1")
        (callEndpoint w1 "1" (1::Int))

    , checkPredicate "collect until"
        (collectUntil (+) 0 (endpoint @Int "1") 10)
        (endpointAvailable w1 "1" <> waitingForSlot w1 10)
        (callEndpoint w1 "1" (1::Int))
    ]

w1 :: EM.Wallet
w1 = EM.Wallet 1
