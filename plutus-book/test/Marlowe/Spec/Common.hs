{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns
-fno-warn-name-shadowing
-fno-warn-unused-do-bind #-}
module Marlowe.Spec.Common where

import           Control.Monad                   (void)
import           Data.Either                     (isRight)
import           Data.Map.Strict                 (Map)
import qualified Data.Map.Strict                 as Map
import           Data.Set                        (Set)
import qualified Data.Set                        as Set

import           Hedgehog                        (Gen, Property, Size (..), forAll, property)
import qualified Hedgehog
import           Hedgehog.Gen                    (choice, element, integral, sized)
import qualified Hedgehog.Range                  as Range

import           Ledger                          hiding (Value)
import qualified Ledger
import           Marlowe.Language.Marlowe        hiding (discountFromPairList, insertCommit, mergeChoices)
import           Marlowe.Language.Marlowe.Client (createContract, marloweValidator, spendDeposit)
import           Wallet                          (PubKey (..))
import           Wallet.Emulator
import qualified Wallet.Emulator.Generators      as Gen
import qualified Wallet.Generators               as Gen

newtype MarloweScenario = MarloweScenario { mlInitialBalances :: Map.Map PubKey Ledger.Value }
data Bounds = Bounds {
    oracleBounds :: Map PubKey (Integer, Integer),
    choiceBounds :: Map IdentChoice (Integer, Integer)
}

emptyBounds :: Bounds
emptyBounds = Bounds Map.empty Map.empty

positiveAmount :: Gen Integer
positiveAmount = integral $ Range.linear 0 100

pubKeyGen :: Gen PubKey
pubKeyGen = toPublicKey . (knownPrivateKeys !!) <$> integral (Range.linear 0 10)

commitGen :: Gen Commit
commitGen = do
    person <- pubKeyGen
    cash <- integral (Range.linear 1 10000)
    timeout <- integral (Range.linear 1 50)
    return (IdentCC 123, (person, NotRedeemed cash timeout))

choiceGen :: Gen Choice
choiceGen = do
    ident <- integral (Range.linear 1 50)
    person <- pubKeyGen
    return ((IdentChoice ident, person), 123)

boundedValue :: Set Person -> Set IdentCC -> Bounds -> Gen Value
boundedValue participants commits bounds = sized $ boundedValueAux participants commits bounds

{-# ANN boundedValueAux ("HLint: ignore Avoid restricted function" :: String) #-}
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

{-# ANN boundedObservationAux ("HLint: ignore Avoid restricted function" :: String) #-}
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

{-# ANN boundedContractAux ("HLint: ignore Avoid restricted function" :: String) #-}
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
                    , Pay . IdentPay
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

-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkMarloweTrace :: MarloweScenario -> Trace MockWallet () -> Property
checkMarloweTrace MarloweScenario{mlInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = mlInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert (null (_txPool st))


updateAll :: [Wallet] -> Trace MockWallet ()
updateAll wallets = processPending >>= void . walletsNotifyBlock wallets

performs :: Wallet -> m () -> Trace m Tx
performs actor action = do
    tx <- head <$> walletAction actor action
    processPending >>= void . walletsNotifyBlock [actor]
    assertIsValidated tx
    return tx

withContract
    :: [Wallet]
    -> Contract
    -> (Tx -> Validator -> Trace MockWallet (Tx, State))
    -> Trace MockWallet ()
withContract wallets contract f = do
    let validator = marloweValidator (walletPubKey creator)
    tx <- head <$> walletAction creator (createContract validator contract 12)
    update
    assertIsValidated tx

    (tx1, state) <- f tx validator

    tx <- head <$> walletAction creator (spendDeposit tx1 validator state)
    update
    assertIsValidated tx
  where
    creator = head wallets
    update  = updateAll wallets
