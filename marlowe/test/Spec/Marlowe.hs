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
                                                )
import           Language.Marlowe.Escrow        as Escrow
import           Language.Marlowe.Actus

newtype MarloweScenario = MarloweScenario { mlInitialBalances :: Map.Map PubKey Ledger.Value }
data Bounds = Bounds {
    oracleBounds :: Map PubKey (Integer, Integer),
    choiceBounds :: Map IdentChoice (Integer, Integer)
}

emptyBounds :: Bounds
emptyBounds = Bounds Map.empty Map.empty


tests :: TestTree
tests = testGroup "Marlowe" [validatorTests, contractsTests]

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
    testProperty "can't commit' after timeout" cantCommitAfterStartTimeout,
    testProperty "redeem after commit' expired" redeemAfterCommitExpired
    ]

positiveAmount :: Gen Int
positiveAmount = int $ Range.linear 0 100

commitGen :: Gen Commit
commitGen = do
    person <- PubKey <$> int (Range.linear 0 10)
    cash <- int (Range.linear 1 10000)
    timeout <- int (Range.linear 1 50)
    return (IdentCC 123, (person, NotRedeemed cash timeout))

choiceGen :: Gen Choice
choiceGen = do
    ident <- int (Range.linear 1 50)
    person <- PubKey <$> int (Range.linear 0 10)
    return ((IdentChoice ident, person), 123)

boundedValue :: Set Person -> Set IdentCC -> Bounds -> Gen Value
boundedValue participants commits bounds = sized $ boundedValueAux participants commits bounds

boundedValueAux :: Set Person -> Set IdentCC -> Bounds -> Size -> Gen Value
boundedValueAux participants commits bounds (Size s) = do
    let committed = Set.toList commits
    let parties   = Set.toList participants
    let choices   = Map.keys $ choiceBounds bounds
    let oracles   = Map.keys $ oracleBounds bounds
    let go s       = boundedValueAux participants commits bounds (Size s)
    case compare s 0 of
        GT -> choice [ Committed <$> element committed
                    , (AddValue <$> go (s `div` 2)) <*> go (s `div` 2)
                    , (MulValue <$> go (s `div` 2)) <*> go (s `div` 2)
                    , (DivValue <$> go (s `div` 2)) <*> go (s `div` 2) <*> go (s `div` 2)
                    , Value <$> positiveAmount
                    , ValueFromChoice <$> element choices <*> element parties <*> go (s - 1)
                    , ValueFromOracle <$> element oracles <*> go (s - 1) ]
        EQ -> choice [ Committed <$> element committed
                    , Value <$> positiveAmount ]
        LT -> error "Negative size in boundedValue"

boundedObservationAux :: Set Person -> Set IdentCC -> Bounds -> Size -> Gen Observation
boundedObservationAux participants commits bounds (Size s) = do
    let parties   = Set.toList participants
    let choices   = Map.keys $ choiceBounds bounds
    let concreteChoices = map (\(IdentChoice id) -> id) choices
    let go s      = boundedObservationAux participants commits bounds (Size s)
    case compare s 0 of
        GT -> choice
            [ BelowTimeout <$> positiveAmount
            , AndObs <$> go (s `div` 2) <*> go (s `div` 2)
            , OrObs <$> go (s `div` 2) <*> go (s `div` 2)
            , NotObs <$> go (s `div` 2)
            , PersonChoseThis <$> element choices <*> element parties <*> element concreteChoices
            , PersonChoseSomething <$> element choices <*> element parties
            , ValueGE
                <$> boundedValueAux participants commits bounds (Size (s `div` 2))
                <*> boundedValueAux participants commits bounds (Size(s `div` 2))
            , pure TrueObs
            , pure FalseObs
            ]
        EQ -> choice
            [ BelowTimeout <$> positiveAmount
            , PersonChoseThis <$> element choices <*> element parties <*> element concreteChoices
            , PersonChoseSomething <$> element choices <*> element parties
            , pure TrueObs
            , pure FalseObs
            ]
        LT -> error "Negative size in boundedContract"

boundedObservation :: Set Person -> Set IdentCC -> Bounds -> Gen Observation
boundedObservation participants commits bounds = sized $ boundedObservationAux participants commits bounds

boundedContractAux :: Set Person -> Set IdentCC -> Bounds -> Size -> Gen Contract
boundedContractAux participants commits bounds (Size s) = do
    let committed       = Set.toList commits
    let parties         = Set.toList participants
    let go s            = boundedContractAux participants commits bounds $ Size (s `div` 2)

    case compare s 0 of
        GT -> do
            let commitCash = do
                    ident <- positiveAmount
                    let  identCC = IdentCC ident
                    person <- element parties
                    value <- boundedValueAux participants (Set.insert identCC commits) bounds $ Size (s - 1)
                    timeout1 <- positiveAmount
                    timeout2 <- positiveAmount
                    contract1 <- go s
                    contract2 <- go s
                    return $ CommitCash identCC person value timeout1 timeout2 contract1 contract2

            choice   [ pure Null
                    , commitCash
                    , RedeemCC <$> element committed <*> go s
                    , (Pay . IdentPay)
                        <$> positiveAmount
                        <*> element parties
                        <*> element parties
                        <*> boundedValueAux participants commits bounds (Size (s - 1))
                        <*> positiveAmount
                        <*> go s
                    , Both
                        <$> go s
                        <*> go s
                    , Choice
                        <$> boundedObservationAux participants commits bounds (Size (s - 1))
                        <*> go s
                        <*> go s
                    , When
                        <$> boundedObservationAux participants commits bounds (Size (s - 1))
                        <*> positiveAmount
                        <*> go s
                        <*> go s
                    ]
        EQ -> element [Null]
        LT -> error "Negative size in boundedContract"

boundedContract :: Set Person -> Set IdentCC -> Bounds -> Gen Contract
boundedContract participants commits bounds = sized $ boundedContractAux participants commits bounds


eqValue :: Value -> Value -> Bool
eqValue = $$(equalValue)

eqObservation :: Observation -> Observation -> Bool
eqObservation = $$(equalObservation) eqValue

eqContract :: Contract -> Contract -> Bool
eqContract = $$(equalContract) eqValue eqObservation

validContract :: State -> Contract -> Slot -> Ada -> Bool
validContract = $$(Marlowe.validateContract)

evalValue :: Slot -> [OracleValue Int] -> State -> Value -> Int
evalValue pendingTxBlockHeight inputOracles = $$(evaluateValue) pendingTxBlockHeight inputOracles

interpretObs :: [OracleValue Int] -> Int -> State -> Observation -> Bool
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

money :: Commit -> Int
money (_, (_, NotRedeemed m _)) = m

{-| Slide across a list with 2 elements window
    >>> slide [1,2,3]
    [(1,2), (2,3)]
-}
slide :: [a] -> [(a, a)]
slide [a, b] = [(a, b)]
slide (a:b:rest) = (a, b) : slide (b:rest)
slide _ = error "at least 2 elements"

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
            let r = discountFromPairList (PubKey 1) (Slot 2) (Ada.fromInt 10) []
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
    let commits =   [ (IdentCC 1, (PubKey 1, NotRedeemed 12 10))
                    , (IdentCC 2, (PubKey 1, NotRedeemed 22 10))
                    , (IdentCC 2, (PubKey 1, NotRedeemed 33 10))]
    let r = $$(Marlowe.findAndRemove) (\(IdentCC id, _) -> id == 2) commits
    r @?= Just  [ (IdentCC 1, (PubKey 1, NotRedeemed 12 10))
                , (IdentCC 2, (PubKey 1, NotRedeemed 33 10))]


checkMergeChoices :: IO ()
checkMergeChoices = do
    let r1 = mergeChoices [((IdentChoice 2, PubKey 1), 22)] []
    r1 @?= [((IdentChoice 2, PubKey 1), 22)]
    let r2 = mergeChoices [((IdentChoice 2, PubKey 2), 33)] r1
    r2 @?= [((IdentChoice 2, PubKey 1), 22), ((IdentChoice 2, PubKey 2), 33)]
    let r3 = mergeChoices [((IdentChoice 1, PubKey 1), 10)] r2
    r3 @?=  [ ((IdentChoice 1, PubKey 1), 10)
            , ((IdentChoice 2, PubKey 1), 22)
            , ((IdentChoice 2, PubKey 2), 33)]
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
            , oracleBounds = Map.singleton (PubKey 42) (200, 333)
            }

    let value = boundedValue (Set.fromList [PubKey 1, PubKey 2]) (Set.fromList [IdentCC 1]) bounds
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
            , oracleBounds = Map.singleton (PubKey 42) (200, 333)
            }

    let observation = boundedObservation (Set.fromList [PubKey 1, PubKey 2]) (Set.fromList [IdentCC 1]) bounds
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
            , oracleBounds = Map.singleton (PubKey 42) (200, 333)
            }

    let contract = boundedContract (Set.fromList [PubKey 1, PubKey 2]) (Set.fromList [IdentCC 1]) bounds
    a <- forAll contract
    b <- forAll contract
    c <- forAll contract
    Hedgehog.assert (eqContract a a)
    Hedgehog.assert (eqContract a b == eqContract b a)
    Hedgehog.assert (if eqContract a b && eqContract b c then eqContract a c else True)

duplicateIdentCC :: Property
duplicateIdentCC = property $ do
    let contract = CommitCash (IdentCC 1) (PubKey 1) (Value 100) 128 256
            (CommitCash (IdentCC 1) (PubKey 1) (Value 100) 128 256 Null Null)
            Null

        contractIsValid = validContract (State [] []) contract (Slot 1) (Ada.fromInt 12)
    Hedgehog.assert (not contractIsValid)

checkValidateContract :: Property
checkValidateContract = property $ do
    let bounds = Bounds
            { choiceBounds = Map.fromList [(IdentChoice 1, (400, 444)), (IdentChoice 2, (500, 555))]
            , oracleBounds = Map.singleton (PubKey 42) (200, 333)
            }

    let contract = boundedContract (Set.fromList [PubKey 1, PubKey 2]) (Set.fromList [IdentCC 1]) bounds
    a <- forAll contract
    let r = validContract (State [] []) a (Slot 1) (Ada.fromInt 12)
    Hedgehog.assert (r || not r)

notEnoughMoney :: IO ()
notEnoughMoney = do
    let commits =   [(IdentCC 1, (PubKey 1, NotRedeemed 60 100))
                    , (IdentCC 1, (PubKey 1, NotRedeemed 40 200))]
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
            , oracleBounds = Map.singleton (PubKey 42) (200, 333)
            }

    let observation = boundedObservation (Set.fromList [PubKey 1, PubKey 2]) (Set.fromList [IdentCC 1]) bounds
    a <- forAll observation
    let oracleValue = OracleValue (PubKey 42) (Slot 1) 256
    let r = interpretObs [oracleValue] 1 emptyState a
    Hedgehog.assert (r || not r)


-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkMarloweTrace :: MarloweScenario -> Trace MockWallet () -> Property
checkMarloweTrace MarloweScenario{mlInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = mlInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == _txPool st)


updateAll :: [Wallet] -> Trace MockWallet ()
updateAll wallets = processPending >>= void . walletsNotifyBlock wallets

getScriptOutFromTx :: Tx -> (TxOut, TxOutRef)
getScriptOutFromTx tx = head . filter (isPayToScriptOut . fst) . txOutRefs $ tx

performs :: Wallet -> m () -> Trace m (TxOut, TxOutRef)
performs actor action = do
    [tx] <- walletAction actor action
    processPending >>= void . walletsNotifyBlock [actor]
    assertIsValidated tx
    return $ getScriptOutFromTx tx

withContract
    :: [Wallet]
    -> Contract
    -> ((TxOut, TxOutRef) -> ValidatorScript -> Trace MockWallet ((TxOut, TxOutRef), State))
    -> Trace MockWallet ()
withContract wallets contract f = do
    let validator = marloweValidator creatorPK
    [tx] <- walletAction creator (createContract validator contract 12)
    let txOut = getScriptOutFromTx tx
    update
    assertIsValidated tx

    (tx1Out, state) <- f txOut validator

    [tx] <- walletAction creator (spendDeposit tx1Out validator state)
    update
    assertIsValidated tx
  where
    creator = head wallets
    creatorPK = let Wallet id = creator in PubKey id
    update  = updateAll wallets

oraclePayment :: Property
oraclePayment = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, Ada.adaValueOf 1000), (PubKey 2, Ada.adaValueOf 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        oracle = PubKey 42
        update = updateAll [alice, bob]
    update

    let contract = CommitCash (IdentCC 1) (PubKey 2) (ValueFromOracle oracle (Value 0)) 128 256
            (Pay (IdentPay 1) (PubKey 2) (PubKey 1) (Committed (IdentCC 1)) 256 Null)
            Null

    let oracleValue = OracleValue oracle (Slot 2) 100
    let validator = marloweValidator (PubKey 1)

    void $ walletAction bob $ startWatching (Ledger.pubKeyAddress $ PubKey 1)
    void $ walletAction bob $ startWatching (Ledger.scriptAddress validator)

    withContract [alice, bob] contract $ \txOut validator -> do
        txOut <- bob `performs` commit
            txOut
            validator
            [oracleValue] []
            (IdentCC 1)
            100
            emptyState
            contract

        txOut <- alice `performs` receivePayment txOut
            validator
            [] []
            (IdentPay 1)
            100
            (State [] [])
            Null
        return (txOut, State [] [])

    assertOwnFundsEq alice (Ada.adaValueOf 1100)
    assertOwnFundsEq bob (Ada.adaValueOf 677)
    return ()

cantCommitAfterStartTimeout :: Property
cantCommitAfterStartTimeout = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, Ada.adaValueOf 1000), (PubKey 2, Ada.adaValueOf 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        update = updateAll [alice, bob]
    update

    let contract = CommitCash (IdentCC 1) (PubKey 2) (Value 100) 128 256 Null Null

    withContract [alice, bob] contract $ \txOut validator -> do

        addBlocksAndNotify [alice, bob] 200

        walletAction bob $ commit'
            txOut
            validator
            [] []
            (IdentCC 1)
            100
            (State [(IdentCC 1, (PubKey 2, NotRedeemed 100 256))] [])
            Null
        update
        return (txOut, State [] [])

    assertOwnFundsEq alice (Ada.adaValueOf 1000)
    assertOwnFundsEq bob (Ada.adaValueOf 777)
    return ()

redeemAfterCommitExpired :: Property
redeemAfterCommitExpired = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, Ada.adaValueOf 1000), (PubKey 2, Ada.adaValueOf 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        update = updateAll [alice, bob]
        identCC = (IdentCC 1)
    update
    let contract = CommitCash identCC (PubKey 2) (Value 100) 128 256 Null Null
    withContract [alice, bob] contract $ \txOut validator -> do

        txOut <- bob `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 1)
            100
            (State [(identCC, (PubKey 2, NotRedeemed 100 256))] [])
            Null

        addBlocksAndNotify [alice, bob] 300

        txOut <- bob `performs` redeem
            txOut validator [] [] identCC 100 (State [] []) Null
        return (txOut, State [] [])

    assertOwnFundsEq alice (Ada.adaValueOf 1000)
    assertOwnFundsEq bob (Ada.adaValueOf 777)
    return ()

escrowTest :: Property
escrowTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, Ada.adaValueOf 1000), (PubKey 2, Ada.adaValueOf 777), (PubKey 3, Ada.adaValueOf 555)  ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        alicePk = PubKey 1
        bob = Wallet 2
        bobPk = PubKey 2
        carol = Wallet 3
        carolPk = PubKey 3
        update = updateAll [alice, bob, carol]
    update

    let contract = Escrow.escrowContract

    withContract [alice, bob, carol] contract $ \txOut validator -> do
        txOut <- alice `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 1)
            450
            (State [(IdentCC 1, (PubKey 1, NotRedeemed 450 100))] [])
            (When (OrObs (twoChose alicePk bobPk carolPk 0)
                                 (twoChose alicePk bobPk carolPk 1))
                          90
                          (Choice (twoChose alicePk bobPk carolPk 1)
                                  (Pay iP1 alicePk bobPk
                                       (Committed iCC1)
                                       100
                                       Null)
                                  redeemOriginal)
                          redeemOriginal)

        addBlocks 50

        let choices = [((IdentChoice 1, alicePk), 1), ((IdentChoice 2, bobPk), 1), ((IdentChoice 3, carolPk), 1)]
        txOut <- bob `performs` receivePayment txOut
            validator
            []
            choices
            (IdentPay 1)
            450
            (State [] choices)
            Null
        return (txOut, (State [] choices))

    assertOwnFundsEq alice (Ada.adaValueOf 550)
    assertOwnFundsEq bob (Ada.adaValueOf 1227)
    assertOwnFundsEq carol (Ada.adaValueOf 555)


-- | A futures contract in Marlowe.

futuresTest :: Property
futuresTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, Ada.adaValueOf 1000000), (PubKey 2, Ada.adaValueOf 1000000) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        alicePk = PubKey 1
        bob = Wallet 2
        bobPk = PubKey 2
        update = updateAll [alice, bob]
    update

    let penalty = 1000
    let forwardPrice = 1123
    let units = 187
    let deliveryDate = 100
    let endTimeout = deliveryDate + 50
    let startTimeout = 10
    let oracle = PubKey 17
    let initialMargin = penalty + (units * forwardPrice `div` 20) -- 5%, 11500
    let forwardPriceV = Value forwardPrice
    let minus a b = AddValue a (MulValue (Value (-1)) b)
    let spotPrice = 1124
    let spotPriceV = ValueFromOracle oracle (Value forwardPrice)
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

    withContract [alice, bob] contract $ \txOut validator -> do
        txOut <- alice `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 1)
            initialMargin
            (State [(IdentCC 1, (PubKey 1, NotRedeemed initialMargin endTimeout))] [])
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

        txOut <- bob `performs` commit'
            txOut
            validator
            [] []
            (IdentCC 2)
            initialMargin
            (State [ (IdentCC 1, (PubKey 1, NotRedeemed initialMargin endTimeout)),
                     (IdentCC 2, (PubKey 2, NotRedeemed initialMargin endTimeout))] [])
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

        let oracleValue = OracleValue oracle (Slot (deliveryDate + 4)) spotPrice
        txOut <- alice `performs` receivePayment txOut
            validator
            [oracleValue] []
            (IdentPay 1)
            187
            (State [ (IdentCC 1, (PubKey 1, NotRedeemed initialMargin endTimeout)),
                     (IdentCC 2, (PubKey 2, NotRedeemed (initialMargin - 187) endTimeout))] [])
            redeems

        txOut <- alice `performs` redeem txOut
            validator
            [] []
            (IdentCC 1)
            initialMargin
            (State [(IdentCC 2, (PubKey 2, NotRedeemed (initialMargin - 187) endTimeout))] [])
            (RedeemCC (IdentCC 2) Null)

        txOut <- bob `performs` redeem txOut
            validator
            [] []
            (IdentCC 2)
            (initialMargin - 187)
            (State [] [])
            Null
        return (txOut, State [] [])


    assertOwnFundsEq alice (Ada.adaValueOf 1000187)
    assertOwnFundsEq bob   (Ada.adaValueOf  999813)
    return ()


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
