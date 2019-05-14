{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns
-fno-warn-name-shadowing
-fno-warn-unused-do-bind #-}
module Spec.Marlowe
    ( tests
    )
where

import           Data.Maybe
import           Control.Monad                  ( void, when )
import qualified Data.List                      as List
import qualified Data.Set                       as Set
import qualified Data.Map.Strict                as Map

import           Hedgehog                       ( Property
                                                , forAll
                                                , property
                                                )
import qualified Hedgehog.Range                 as Range
import           Hedgehog.Gen                   (list
                                                )
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog            ( testProperty
                                                , HedgehogTestLimit(..)
                                                )

import           Ledger                  hiding ( Value )
import qualified Ledger.Ada                     as Ada
import           Ledger.Validation              ( OracleValue(..) )
import           Wallet                         ( PubKey(..)
                                                , startWatching
                                                )
import           Wallet.Emulator
import           Language.Marlowe        hiding (insertCommit, discountFromPairList, mergeChoices)
import qualified Language.Marlowe               as Marlowe
import           Language.Marlowe.Client        ( commit'
                                                , commit
                                                , redeem
                                                , receivePayment
                                                , marloweValidator
                                                )
import           Language.Marlowe.Escrow        as Escrow
import           Spec.Common


tests :: TestTree
tests = testGroup "Marlowe" [validatorTests]
    --, contractsTests]
    -- TODO: fix 'contractsTests' and add them back in

validatorTests :: TestTree
validatorTests = testGroup "Marlowe Validator" [
    testProperty "eqValue is reflective, symmetric, and transitive" checkEqValue,
    testProperty "eqObservation is reflective, symmetric, and transitive" checkEqObservation,
    testProperty "eqContract is reflective, symmetric, and transitive" checkEqContract,
    testProperty "validateContract is a total function" checkValidateContract,
    testProperty "interprebObs is a total function" checkInterpretObsTotality,
    testProperty "insertCommit" checkInsertCommit,
    testProperty "discountFromPairList is correct" checkDiscountFromPairList,
    testCase     "findAndRemove" checkFindAndRemove,
    testCase     "mergeChoices" checkMergeChoices,
    testProperty "mergeChoices produces ordered list of unique choices" checkMergeChoicesProperties,
    testCase     "invalid contract: not enought money" notEnoughMoney,
    testProperty "invalid contract: duplicate IdentCC" duplicateIdentCC
    ]

contractsTests :: TestTree
contractsTests = localOption (HedgehogTestLimit $ Just 3) $ testGroup "Marlowe Contracts" [
    testProperty "Oracle Commit/Pay works" oraclePayment,
    testProperty "Escrow Contract" escrowTest,
    testProperty "Futures" futuresTest,
    testProperty "can't commit after timeout" cantCommitAfterStartTimeout,
    testProperty "redeem after commit expired" redeemAfterCommitExpired
    ]


eqValue :: Value -> Value -> Bool
eqValue = $$(equalValue)

eqObservation :: Observation -> Observation -> Bool
eqObservation = $$(equalObservation) eqValue

eqContract :: Contract -> Contract -> Bool
eqContract = $$(equalContract) eqValue eqObservation

validContract :: State -> Contract -> Slot -> Ada -> Bool
validContract = $$(Marlowe.validateContract)

evalValue :: Slot -> [OracleValue Integer] -> State -> Value -> Integer
evalValue pendingTxBlockHeight inputOracles = $$(evaluateValue) pendingTxBlockHeight inputOracles

interpretObs :: [OracleValue Integer] -> Integer -> State -> Observation -> Bool
interpretObs inputOracles blockNumber state obs = let
    ev = evalValue (Slot blockNumber) inputOracles
    in $$(interpretObservation) ev blockNumber state obs

insertCommit :: Commit -> [Commit] -> [Commit]
insertCommit = $$(Marlowe.insertCommit)

discountFromPairList :: PubKey
    -> Slot
    -> Ada
    -> [(IdentCC, CCStatus)]
    -> Maybe [(IdentCC, CCStatus)]
discountFromPairList = $$(Marlowe.discountFromPairList)

mergeChoices :: [Choice] -> [Choice] -> [Choice]
mergeChoices = $$(Marlowe.mergeChoices)

money :: Commit -> Integer
money (_, (_, NotRedeemed m _)) = m

{-| Slide across a list with 2 elements window
    >>> slide [1,2,3]
    [(1,2), (2,3)]
-}
slide :: [a] -> [(a, a)]
slide [a, b] = [(a, b)]
slide (a:b:rest) = (a, b) : slide (b:rest)
slide _ = error "at least 2 elements"

pubKey1 :: PubKey
pubKey1 = toPublicKey privateKey1

pubKey2 :: PubKey
pubKey2 = toPublicKey privateKey2

pubKey3 :: PubKey
pubKey3 = toPublicKey privateKey3

checkInsertCommit :: Property
checkInsertCommit = property $ do
    commits <- forAll $ list (Range.linear 0 100) commitGen
    let result = List.foldl' (flip insertCommit) [] commits
    let expectedMoney   = List.foldl' (\acc c -> acc + money c) 0 commits
    let actualMoney     = List.foldl' (\acc c -> acc + money c) 0 result
    Hedgehog.assert (length result == length commits)
    Hedgehog.assert (actualMoney == expectedMoney)
    when (length result >= 2) $ do
        -- check commits are partially ordered by timeout
        let partialyOrderedByTimeout ((_, (lpk, NotRedeemed _ ltimeout)), (_, (rpk, NotRedeemed _ rtimeout))) =
                if lpk == rpk then ltimeout <= rtimeout else True
        Hedgehog.assert $ all partialyOrderedByTimeout (slide result)

checkDiscountFromPairList :: Property
checkDiscountFromPairList = property $ do
    generated <- forAll $ list (Range.linear 0 100) commitGen
    let commits = List.foldl' (flip insertCommit) [] generated
    let availableMoney commits  = List.foldl' (\acc c -> acc + money c) 0 commits
    let mergeFunds acc (_, (pk, NotRedeemed m _)) = Map.alter (maybe (Just m) (\v -> Just $ v+m)) pk acc
    let funds = List.foldl' mergeFunds Map.empty commits
    case Map.toList funds of
        [] -> do
            let r = discountFromPairList pubKey1 (Slot 2) (Ada.fromInt 10) []
            Hedgehog.assert (isNothing r)
        (pk, amount) : _ -> do
            -- we are able to spend all the money for a person, when nothing is timedout yet
            let r = discountFromPairList pk (Slot 1) (Ada.fromInt amount) commits
            Hedgehog.assert (isJust r)
            let Just after = r
            Hedgehog.assert (length after < length commits)
            Hedgehog.assert (availableMoney after < availableMoney commits)
            -- we are not able to spend anything after timeouts
            let r = discountFromPairList pk (Slot 55) (Ada.fromInt amount) commits
            Hedgehog.assert (isNothing r)

checkFindAndRemove :: IO ()
checkFindAndRemove = do
    let pk = toPublicKey privateKey1
    let commits =   [ (IdentCC 1, (pk, NotRedeemed 12 10))
                    , (IdentCC 2, (pk, NotRedeemed 22 10))
                    , (IdentCC 2, (pk, NotRedeemed 33 10))]
    let r = $$(Marlowe.findAndRemove) (\(IdentCC id, _) -> id == 2) commits
    r @?= Just  [ (IdentCC 1, (pk, NotRedeemed 12 10))
                , (IdentCC 2, (pk, NotRedeemed 33 10))]


checkMergeChoices :: IO ()
checkMergeChoices = do
    let pk1 = toPublicKey privateKey1
    let pk2 = toPublicKey privateKey2
    let r1 = mergeChoices [((IdentChoice 2, pk1), 22)] []
    r1 @?= [((IdentChoice 2, pk1), 22)]
    let r2 = mergeChoices [((IdentChoice 2, pk2), 33)] r1
    r2 @?= [((IdentChoice 2, pk1), 22), ((IdentChoice 2, pk2), 33)]
    let r3 = mergeChoices [((IdentChoice 1, pk1), 10)] r2
    r3 @?=  [ ((IdentChoice 1, pk1), 10)
            , ((IdentChoice 2, pk1), 22)
            , ((IdentChoice 2, pk2), 33)]
    let r = mergeChoices r3 r3
    r @?= r3

checkMergeChoicesProperties :: Property
checkMergeChoicesProperties = property $ do
    input  <- forAll $ list (Range.linear 0 20) choiceGen
    input2 <- forAll $ list (Range.linear 0 20) choiceGen
    let choices = mergeChoices input2 []
    let r = mergeChoices input choices
    let keys = map fst r
    Hedgehog.assert (length r <= length input + length choices)
    when (length r >= 2) $ do
        -- check choices are partially ordered
        Hedgehog.assert $ all (\((lid, _), (rid, _)) -> lid <= rid) (slide keys)
        -- check choices are unique
        Hedgehog.assert $ List.nub keys == keys


checkEqValue :: Property
checkEqValue = property $ do
    let bounds = Bounds
            { choiceBounds = Map.fromList [(IdentChoice 1, (400, 444)), (IdentChoice 2, (500, 555))]
            , oracleBounds = Map.singleton pubKey3 (200, 333)
            }

    let value = boundedValue (Set.fromList [pubKey1, pubKey2]) (Set.fromList [IdentCC 1]) bounds
    a <- forAll value
    b <- forAll value
    c <- forAll value
    Hedgehog.assert (eqValue a a)
    Hedgehog.assert (eqValue a b == eqValue b a)
    Hedgehog.assert (if eqValue a b && eqValue b c then eqValue a c else True)

checkEqObservation :: Property
checkEqObservation = property $ do
    let bounds = Bounds
            { choiceBounds = Map.fromList [(IdentChoice 1, (400, 444)), (IdentChoice 2, (500, 555))]
            , oracleBounds = Map.singleton pubKey3 (200, 333)
            }

    let observation = boundedObservation (Set.fromList [pubKey1, pubKey2]) (Set.fromList [IdentCC 1]) bounds
    a <- forAll observation
    b <- forAll observation
    c <- forAll observation
    Hedgehog.assert (eqObservation a a)
    Hedgehog.assert (eqObservation a b == eqObservation b a)
    Hedgehog.assert (if eqObservation a b && eqObservation b c then eqObservation a c else True)

checkEqContract :: Property
checkEqContract = property $ do
    let bounds = Bounds
            { choiceBounds = Map.fromList [(IdentChoice 1, (400, 444)), (IdentChoice 2, (500, 555))]
            , oracleBounds = Map.singleton pubKey3 (200, 333)
            }

    let contract = boundedContract (Set.fromList [pubKey1, pubKey2]) (Set.fromList [IdentCC 1]) bounds
    a <- forAll contract
    b <- forAll contract
    c <- forAll contract
    Hedgehog.assert (eqContract a a)
    Hedgehog.assert (eqContract a b == eqContract b a)
    Hedgehog.assert (if eqContract a b && eqContract b c then eqContract a c else True)

duplicateIdentCC :: Property
duplicateIdentCC = property $ do
    let contract = CommitCash (IdentCC 1) (pubKey1) (Value 100) 128 256
            (CommitCash (IdentCC 1) (pubKey1) (Value 100) 128 256 Null Null)
            Null

        contractIsValid = validContract (State [] []) contract (Slot 1) (Ada.fromInt 12)
    Hedgehog.assert (not contractIsValid)

checkValidateContract :: Property
checkValidateContract = property $ do
    let bounds = Bounds
            { choiceBounds = Map.fromList [(IdentChoice 1, (400, 444)), (IdentChoice 2, (500, 555))]
            , oracleBounds = Map.singleton pubKey3 (200, 333)
            }

    let contract = boundedContract (Set.fromList [pubKey1, pubKey2]) (Set.fromList [IdentCC 1]) bounds
    a <- forAll contract
    let r = validContract (State [] []) a (Slot 1) (Ada.fromInt 12)
    Hedgehog.assert (r || not r)

notEnoughMoney :: IO ()
notEnoughMoney = do
    let commits =   [(IdentCC 1, (pubKey1, NotRedeemed 60 100))
                    , (IdentCC 1, (pubKey1, NotRedeemed 40 200))]
    let test = validContract (State commits []) Null
    let enoughOk = test (Slot 100) (Ada.fromInt 100)
    let enoughFail = test (Slot 1) (Ada.fromInt 99)
    let firstCommitTimedOutOk = test (Slot 101) (Ada.fromInt 45)
    let firstCommitTimedOutFail = test (Slot 101) (Ada.fromInt 39)
    enoughOk @?= True
    enoughFail @?= False
    firstCommitTimedOutOk @?= True
    firstCommitTimedOutFail @?= False


checkInterpretObsTotality :: Property
checkInterpretObsTotality = property $ do
    let bounds = Bounds
            { choiceBounds = Map.fromList [(IdentChoice 1, (400, 444)), (IdentChoice 2, (500, 555))]
            , oracleBounds = Map.singleton pubKey3 (200, 333)
            }

    let observation = boundedObservation (Set.fromList [pubKey1, pubKey2]) (Set.fromList [IdentCC 1]) bounds
    a <- forAll observation
    let oracleValue = OracleValue pubKey3 (Slot 1) 256
    let r = interpretObs [oracleValue] 1 emptyState a
    Hedgehog.assert (r || not r)


oraclePayment :: Property
oraclePayment = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (pubKey1, Ada.adaValueOf 1000), (pubKey2, Ada.adaValueOf 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        alicePk = pubKey1
        bob = Wallet 2
        bobPk = pubKey2
        oraclePk = pubKey3
        update = updateAll [alice, bob]
    update

    let contract = CommitCash (IdentCC 1) bobPk (ValueFromOracle oraclePk (Value 0)) 128 256
            (Pay (IdentPay 1) bobPk alicePk (Committed (IdentCC 1)) 256 Null)
            Null

    let oracleValue = OracleValue oraclePk (Slot 2) 100
    let validator = marloweValidator alicePk

    void $ walletAction bob $ startWatching (Ledger.pubKeyAddress alicePk)
    void $ walletAction bob $ startWatching (Ledger.scriptAddress validator)

    withContract [alice, bob] contract $ \tx validator -> do
        tx <- bob `performs` commit'
            alicePk
            tx
            validator
            [oracleValue] []
            (IdentCC 1)
            100
            emptyState
            contract

        tx <- alice `performs` receivePayment tx
            validator
            [] []
            (IdentPay 1)
            100
            (State [] [])
            Null
        return (tx, State [] [])

    assertOwnFundsEq alice (Ada.adaValueOf 1100)
    assertOwnFundsEq bob (Ada.adaValueOf 677)
    return ()

cantCommitAfterStartTimeout :: Property
cantCommitAfterStartTimeout = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (pubKey1, Ada.adaValueOf 1000), (pubKey2, Ada.adaValueOf 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        update = updateAll [alice, bob]
    update

    let contract = CommitCash (IdentCC 1) (pubKey2) (Value 100) 128 256 Null Null

    withContract [alice, bob] contract $ \tx validator -> do

        addBlocksAndNotify [alice, bob] 200

        walletAction bob $ commit
            tx
            validator
            [] []
            (IdentCC 1)
            100
            (State [(IdentCC 1, (pubKey2, NotRedeemed 100 256))] [])
            Null
        update
        return (tx, State [] [])

    assertOwnFundsEq alice (Ada.adaValueOf 1000)
    assertOwnFundsEq bob (Ada.adaValueOf 777)
    return ()

redeemAfterCommitExpired :: Property
redeemAfterCommitExpired = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (pubKey1, Ada.adaValueOf 1000), (pubKey2, Ada.adaValueOf 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        update = updateAll [alice, bob]
        identCC = (IdentCC 1)
    update
    let contract = CommitCash identCC (pubKey2) (Value 100) 128 256 Null Null
    withContract [alice, bob] contract $ \tx validator -> do

        tx <- bob `performs` commit
            tx
            validator
            [] []
            (IdentCC 1)
            100
            (State [(identCC, (pubKey2, NotRedeemed 100 256))] [])
            Null

        addBlocksAndNotify [alice, bob] 300

        tx <- bob `performs` redeem
            tx validator [] [] identCC 100 (State [] []) Null
        return (tx, State [] [])

    assertOwnFundsEq alice (Ada.adaValueOf 1000)
    assertOwnFundsEq bob (Ada.adaValueOf 777)
    return ()

escrowTest :: Property
escrowTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (pubKey1, Ada.adaValueOf 1000), (pubKey2, Ada.adaValueOf 777), (pubKey3, Ada.adaValueOf 555)  ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        alicePk = toPublicKey privateKey1
        aliceId = IdentChoice 1
        bob = Wallet 2
        bobPk = toPublicKey privateKey2
        bobId = IdentChoice 2
        carol = Wallet 3
        carolPk = toPublicKey privateKey3
        carolId = IdentChoice 3
        update = updateAll [alice, bob, carol]
    update

    let contract = Escrow.escrowContract

    withContract [alice, bob, carol] contract $ \tx validator -> do
        tx <- alice `performs` commit
            tx
            validator
            [] []
            (IdentCC 1)
            450
            (State [(IdentCC 1, (alicePk, NotRedeemed 450 100))] [])
            (When (OrObs (twoChose aliceId alicePk bobId bobPk carolId carolPk 0)
                                 (twoChose aliceId alicePk bobId bobPk carolId carolPk 1))
                          90
                          (Choice (twoChose aliceId alicePk bobId bobPk carolId carolPk 1)
                                  (Pay iP1 alicePk bobPk
                                       (Committed iCC1)
                                       100
                                       Null)
                                  redeemOriginal)
                          redeemOriginal)

        addBlocks 50

        let choices = [((aliceId, alicePk), 1), ((bobId, bobPk), 1), ((carolId, carolPk), 1)]
        tx <- bob `performs` receivePayment tx
            validator
            []
            choices
            (IdentPay 1)
            450
            (State [] choices)
            Null
        return (tx, (State [] choices))

    assertOwnFundsEq alice (Ada.adaValueOf 550)
    assertOwnFundsEq bob (Ada.adaValueOf 1227)
    assertOwnFundsEq carol (Ada.adaValueOf 555)


-- | A futures contract in Marlowe.

futuresTest :: Property
futuresTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (alicePk, Ada.adaValueOf 1000000), (bobPk, Ada.adaValueOf 1000000) ] }) $ do
    -- Init a contract
    update

    let penalty = 1000
    let forwardPrice = 1123
    let units = 187
    let deliveryDate = 100
    let endTimeout = deliveryDate + 50
    let startTimeout = 10
    let oraclePk = pubKey3
    let initialMargin = penalty + (units * forwardPrice `div` 20) -- 5%, 11500
    let forwardPriceV = Value forwardPrice
    let minus a b = AddValue a (MulValue (Value (-1)) b)
    let spotPrice = 1124
    let spotPriceV = ValueFromOracle oraclePk (Value forwardPrice)
    let delta d = MulValue (Value units) d
    let redeems = Both (RedeemCC (IdentCC 1) Null) (RedeemCC (IdentCC 2) Null)
    let contract =  CommitCash (IdentCC 1) alicePk (Value initialMargin) startTimeout endTimeout
                        (CommitCash (IdentCC 2) bobPk (Value initialMargin) startTimeout endTimeout
                            (When FalseObs deliveryDate Null
                                (Choice (AndObs (ValueGE spotPriceV forwardPriceV)
                                                (ValueGE forwardPriceV spotPriceV))
                                    redeems
                                    (Choice (ValueGE spotPriceV forwardPriceV)
                                        (Pay (IdentPay 1) bobPk alicePk
                                            (delta (minus spotPriceV forwardPriceV)) endTimeout redeems)
                                        (Choice (ValueGE forwardPriceV spotPriceV)
                                            (Pay (IdentPay 2) alicePk bobPk
                                                (delta (minus forwardPriceV spotPriceV)) endTimeout redeems)
                                            redeems))))
                            (RedeemCC (IdentCC 1) Null))
                        Null

    withContract [alice, bob] contract $ \tx validator -> do
        tx <- alice `performs` commit
            tx
            validator
            [] []
            (IdentCC 1)
            initialMargin
            (State [(IdentCC 1, (alicePk, NotRedeemed initialMargin endTimeout))] [])
            (CommitCash (IdentCC 2) bobPk (Value initialMargin) startTimeout endTimeout
                (When FalseObs deliveryDate Null
                    (Choice (AndObs (ValueGE spotPriceV forwardPriceV)
                                    (ValueGE forwardPriceV spotPriceV))
                        redeems
                        (Choice (ValueGE spotPriceV forwardPriceV)
                            (Pay (IdentPay 1) bobPk alicePk
                                (delta (minus spotPriceV forwardPriceV)) endTimeout redeems)
                            (Choice (ValueGE forwardPriceV spotPriceV)
                                (Pay (IdentPay 2) alicePk bobPk
                                    (delta (minus forwardPriceV spotPriceV)) endTimeout redeems)
                                redeems))))
                (RedeemCC (IdentCC 1) Null))

        update

        tx <- bob `performs` commit
            tx
            validator
            [] []
            (IdentCC 2)
            initialMargin
            (State [ (IdentCC 1, (alicePk, NotRedeemed initialMargin endTimeout)),
                     (IdentCC 2, (bobPk, NotRedeemed initialMargin endTimeout))] [])
            (When FalseObs deliveryDate Null
                (Choice (AndObs (ValueGE spotPriceV forwardPriceV)
                                (ValueGE forwardPriceV spotPriceV))
                    redeems
                    (Choice (ValueGE spotPriceV forwardPriceV)
                        (Pay (IdentPay 1) bobPk alicePk
                            (delta (minus spotPriceV forwardPriceV)) endTimeout redeems)
                        (Choice (ValueGE forwardPriceV spotPriceV)
                            (Pay (IdentPay 2) alicePk bobPk
                                (delta (minus forwardPriceV spotPriceV)) endTimeout redeems)
                            redeems))))

        addBlocksAndNotify [alice, bob] deliveryDate

        let oracleValue = OracleValue oraclePk (Slot (deliveryDate + 4)) spotPrice
        tx <- alice `performs` receivePayment tx
            validator
            [oracleValue] []
            (IdentPay 1)
            187
            (State [ (IdentCC 1, (alicePk, NotRedeemed initialMargin endTimeout)),
                     (IdentCC 2, (bobPk, NotRedeemed (initialMargin - 187) endTimeout))] [])
            redeems

        tx <- alice `performs` redeem tx
            validator
            [] []
            (IdentCC 1)
            initialMargin
            (State [(IdentCC 2, (bobPk, NotRedeemed (initialMargin - 187) endTimeout))] [])
            (RedeemCC (IdentCC 2) Null)

        tx <- bob `performs` redeem tx
            validator
            [] []
            (IdentCC 2)
            (initialMargin - 187)
            (State [] [])
            Null
        return (tx, State [] [])


    assertOwnFundsEq alice (Ada.adaValueOf 1000187)
    assertOwnFundsEq bob   (Ada.adaValueOf  999813)
    return ()
  where
    alice = Wallet 1
    alicePk = toPublicKey privateKey1
    bob = Wallet 2
    bobPk = toPublicKey privateKey2
    update = updateAll [alice, bob]
