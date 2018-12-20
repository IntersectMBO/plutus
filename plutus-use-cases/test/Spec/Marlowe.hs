{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns
-fno-warn-name-shadowing
-fno-warn-unused-do-bind #-}
module Spec.Marlowe(tests) where

import           Data.Either                    ( isRight )
import           Control.Monad                  ( void )
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import           Hedgehog                       ( Gen, Property, Size(..)
                                                , forAll
                                                , property
                                                )
import qualified Hedgehog.Range as Range
import Hedgehog.Gen (element, int, choice, sized)
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog            ( testProperty
                                                , HedgehogTestLimit(..)
                                                )

import           Ledger                  hiding ( Value )
import qualified Ledger
import           Ledger.Validation              ( OracleValue(..) )
import           Wallet                         ( PubKey(..) )
import           Wallet.Emulator
import qualified Wallet.Generators             as Gen
import           Language.Marlowe.Compiler     as Marlowe
import           Language.Marlowe.Common       as Marlowe
import           Language.Marlowe.Escrow       as Escrow

newtype MarloweScenario = MarloweScenario { mlInitialBalances :: Map.Map PubKey Ledger.Value }
data Bounds = Bounds {
    oracleBounds :: Map PubKey (Integer, Integer),
    choiceBounds :: Map IdentChoice (Integer, Integer)
}

emptyBounds :: Bounds
emptyBounds = Bounds Map.empty Map.empty


tests :: TestTree
tests = localOption (HedgehogTestLimit $ Just 3) $ testGroup "Marlowe" [
        testProperty "eqValue is reflective, symmetric, and transitive" checkEqValue,
        testProperty "eqObservation is reflective, symmetric, and transitive" checkEqObservation,
        testProperty "Oracle Commit/Pay works" oraclePayment
        -- testProperty "Escrow Contract" escrowTest,
        -- testProperty "Futures" futuresTest,
        -- testProperty "invalid contract: duplicate IdentCC" duplicateIdentCC,
        -- testProperty "can't commit after timeout" cantCommitAfterStartTimeout,
        -- testProperty "redeem after commit expired" redeemAfterCommitExpired
        ]

positiveAmount :: Gen Int
positiveAmount = int $ Range.linear 0 100


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

eqValue :: Value -> Value -> Bool
eqValue = $$(equalValue)

eqObservation :: Observation -> Observation -> Bool
eqObservation = $$(equalObservation) eqValue

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

getScriptOutFromTx :: Tx -> (TxOut', TxOutRef')
getScriptOutFromTx tx = head . filter (isPayToScriptOut . fst) . txOutRefs $ tx

performs :: Wallet -> m () -> Trace m (TxOut', TxOutRef')
performs actor action = do
    [tx] <- walletAction actor action
    processPending >>= void . walletsNotifyBlock [actor]
    assertIsValidated tx
    return $ getScriptOutFromTx tx

withContract
    :: [Wallet]
    -> Contract
    -> ((TxOut', TxOutRef') -> Trace MockWallet ((TxOut', TxOutRef'), State))
    -> Trace MockWallet ()
withContract wallets contract f = do
    [tx] <- walletAction creator (createContract contract 12)
    let txOut = getScriptOutFromTx tx
    update
    assertIsValidated tx

    (tx1Out, state) <- f txOut

    [tx] <- walletAction creator (endContract tx1Out state)
    update
    assertIsValidated tx
  where
    creator = head wallets
    update  = updateAll wallets

oraclePayment :: Property
oraclePayment = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000), (PubKey 2, 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        oracle = PubKey 42
        update = updateAll [alice, bob]
    update

    let contract = CommitCash (IdentCC 1) (PubKey 2) (ValueFromOracle oracle (Value 0)) 128 256
            (Pay (IdentPay 1) (PubKey 2) (PubKey 1) (Committed (IdentCC 1)) 256 Null)
            Null

    let oracleValue = OracleValue oracle (Height 2) 100

    withContract [alice, bob] contract $ \txOut -> do
        txOut <- bob `performs` commit
            txOut
            [oracleValue] []
            (IdentCC 1)
            100
            (State [(IdentCC 1, (PubKey 2, NotRedeemed 100 256))] [])
            (Pay (IdentPay 1) (PubKey 2) (PubKey 1) (Committed (IdentCC 1)) 256 Null)

        txOut <- alice `performs` receivePayment txOut
            [] []
            (IdentPay 1)
            100
            (State [] [])
            Null
        return (txOut, State [] [])

    assertOwnFundsEq alice 1100
    assertOwnFundsEq bob 677
    return ()

cantCommitAfterStartTimeout :: Property
cantCommitAfterStartTimeout = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000), (PubKey 2, 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        update = updateAll [alice, bob]
    update

    let contract = CommitCash (IdentCC 1) (PubKey 2) (Value 100) 128 256 Null Null

    withContract [alice, bob] contract $ \txOut -> do

        addBlocks 200

        walletAction bob $ commit
            txOut
            [] []
            (IdentCC 1)
            100
            (State [(IdentCC 1, (PubKey 2, NotRedeemed 100 256))] [])
            Null
        update
        return (txOut, State [] [])

    assertOwnFundsEq alice 1000
    assertOwnFundsEq bob 777
    return ()

duplicateIdentCC :: Property
duplicateIdentCC = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000), (PubKey 2, 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        update = updateAll [alice, bob]
    update

    let contract = CommitCash (IdentCC 1) (PubKey 1) (Value 100) 128 256
            (CommitCash (IdentCC 1) (PubKey 1) (Value 100) 128 256 Null Null)
            Null

    withContract [alice, bob] contract $ \txOut -> return (txOut, State [] [])

    assertOwnFundsEq alice 1000
    assertOwnFundsEq bob 777
    return ()

redeemAfterCommitExpired :: Property
redeemAfterCommitExpired = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000), (PubKey 2, 777) ] }) $ do
    -- Init a contract
    let alice = Wallet 1
        bob = Wallet 2
        update = updateAll [alice, bob]
        identCC = (IdentCC 1)
    update
    let contract = CommitCash identCC (PubKey 2) (Value 100) 128 256 Null Null
    withContract [alice, bob] contract $ \txOut -> do

        txOut <- bob `performs` commit
            txOut
            [] []
            (IdentCC 1)
            100
            (State [(identCC, (PubKey 2, NotRedeemed 100 256))] [])
            Null

        addBlocks 300

        txOut <- bob `performs` redeem
            txOut [] [] identCC 100 (State [] []) Null
        return (txOut, State [] [])

    assertOwnFundsEq alice 1000
    assertOwnFundsEq bob 777
    return ()

escrowTest :: Property
escrowTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000), (PubKey 2, 777), (PubKey 3, 555)  ] }) $ do
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

    withContract [alice, bob, carol] contract $ \txOut -> do
        txOut <- alice `performs` commit
            txOut
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
            []
            choices
            (IdentPay 1)
            450
            (State [] choices)
            Null
        return (txOut, (State [] choices))

    assertOwnFundsEq alice 550
    assertOwnFundsEq bob 1227
    assertOwnFundsEq carol 555


-- | A futures contract in Marlowe.

futuresTest :: Property
futuresTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList [ (PubKey 1, 1000000), (PubKey 2, 1000000) ] }) $ do
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

    withContract [alice, bob] contract $ \txOut -> do
        txOut <- alice `performs` commit
            txOut
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

        txOut <- bob `performs` commit
            txOut
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

        addBlocks deliveryDate

        let oracleValue = OracleValue oracle (Height (deliveryDate + 4)) spotPrice
        txOut <- alice `performs` receivePayment txOut
            [oracleValue] []
            (IdentPay 1)
            187
            (State [ (IdentCC 1, (PubKey 1, NotRedeemed initialMargin endTimeout)),
                     (IdentCC 2, (PubKey 2, NotRedeemed (initialMargin - 187) endTimeout))] [])
            redeems

        txOut <- alice `performs` redeem txOut
            [] []
            (IdentCC 1)
            initialMargin
            (State [(IdentCC 2, (PubKey 2, NotRedeemed (initialMargin - 187) endTimeout))] [])
            (RedeemCC (IdentCC 2) Null)

        txOut <- bob `performs` redeem txOut
            [] []
            (IdentCC 2)
            (initialMargin - 187)
            (State [] [])
            Null
        return (txOut, State [] [])


    assertOwnFundsEq alice 1000187
    assertOwnFundsEq bob    999813
    return ()
