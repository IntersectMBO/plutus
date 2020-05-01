{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns
-fno-warn-name-shadowing
-fno-warn-unused-do-bind
-fno-warn-unused-top-binds #-}
module Spec.Marlowe.Marlowe
    ( tests
    )
where

import           Control.Lens               (view)
import           Control.Monad              (void)
import qualified Control.Monad.Freer        as Eff
import           Data.Aeson                 (decode, encode)
import qualified Data.ByteString            as BS
import           Data.Either                (isRight)
import qualified Data.Map.Strict            as Map
import           Data.Ratio                 ((%))
import           Data.String

import qualified Codec.CBOR.Write           as Write
import qualified Codec.Serialise            as Serialise
import           Hedgehog                   (Gen, Property, forAll, property, (===))
import qualified Hedgehog
import           Hedgehog.Gen               (integral)
import qualified Hedgehog.Gen               as Gen
import qualified Hedgehog.Range             as Range
import           Language.Marlowe
import qualified Language.PlutusTx.Prelude  as P
import           Ledger                     hiding (Value)
import           Ledger.Ada                 (adaValueOf)
import qualified Ledger.Generators          as Gen
import qualified Ledger.Value               as Val
import           Spec.Marlowe.Common
import           Test.Tasty
import           Test.Tasty.Hedgehog        (HedgehogTestLimit (..), testProperty)
import           Test.Tasty.HUnit
import           Wallet.Emulator
import qualified Wallet.Emulator.Generators as Gen
import           Wallet.Emulator.MultiAgent (EmulatedWalletEffects)

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
{-# ANN module ("HLint: ignore Redundant if" :: String) #-}

limitedProperty :: TestName -> Property -> TestTree
limitedProperty a b = localOption (HedgehogTestLimit $ Just 3) $ testProperty a b

tests :: TestTree
tests = testGroup "Marlowe"
    [ testCase "Contracts with different creators have different hashes" uniqueContractHash
    , testCase "Pangram Contract serializes into valid JSON" pangramContractSerialization
    , testCase "Validator size is reasonable" validatorSize
    , testProperty "Value equality is reflexive, symmetric, and transitive" checkEqValue
    , testProperty "Value double negation" doubleNegation
    , testProperty "Values form abelian group" valuesFormAbelianGroup
    , testProperty "Values can be serialized to JSON" valueSerialization
    , testProperty "Scale Value multiplies by a constant rational" scaleMulTest
    , testProperty "Scale rounding" scaleRoundingTest
    , limitedProperty "Zero Coupon Bond Contract" zeroCouponBondTest
    , limitedProperty "Zero Coupon Bond w/ Roles Contract" zeroCouponBondRolesTest
    , limitedProperty "Trust Fund Contract" trustFundTest
    , limitedProperty "Make progress Contract" makeProgressTest
    ]


alice, bob, carol :: Wallet
alice = Wallet 1
bob = Wallet 2
carol = Wallet 3


zeroCouponBondTest :: Property
zeroCouponBondTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList
        [ (walletPubKey alice, adaValueOf 1000), (walletPubKey bob, adaValueOf 1000) ] }) $ do
    -- Init a contract
    let alicePk = PK $ (pubKeyHash $ walletPubKey alice)
        aliceAcc = AccountId 0 alicePk
        bobPk = PK $ (pubKeyHash $ walletPubKey bob)
        update = updateAll [alice, bob]
    update

    let params = defaultMarloweParams

    let zeroCouponBond = When [ Case
            (Deposit aliceAcc alicePk ada (Constant 850_000_000))
            (Pay aliceAcc (Party bobPk) ada (Constant 850_000_000)
                (When
                    [ Case (Deposit aliceAcc bobPk ada (Constant 1000_000_000))
                        (Pay aliceAcc (Party alicePk) ada (Constant 1000_000_000)
                        Close)
                    ] (Slot 200) Close
                ))] (Slot 100) Close

    let performs = performNotify [alice, bob]
    (md, tx) <- alice `performs` createContract params zeroCouponBond
    (md, tx) <- alice `performs` deposit tx params md aliceAcc ada 850_000_000
    bob `performs` deposit tx params md aliceAcc ada 1000_000_000

    assertOwnFundsEq alice (adaValueOf 1150)
    assertOwnFundsEq bob (adaValueOf 850)


aliceToken :: Val.Value
aliceToken = Val.singleton "11" "alice" 1


bobToken :: Val.Value
bobToken = Val.singleton "11" "bob" 1


zeroCouponBondRolesTest :: Property
zeroCouponBondRolesTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList
        [ (walletPubKey alice, adaValueOf 1000 <> aliceToken)
        , (walletPubKey bob, adaValueOf 1000 <> bobToken) ] }) $ do
    -- Init a contract
    let aliceRole = Role "alice"
        aliceAcc = AccountId 0 aliceRole
        bobRole = Role "bob"
        update = updateAll [alice, bob]
    update

    let params = marloweParams "11"

    let zeroCouponBond = When [ Case
            (Deposit aliceAcc aliceRole ada (Constant 850_000_000))
            (Pay aliceAcc (Party bobRole) ada (Constant 850_000_000)
                (When
                    [ Case (Deposit aliceAcc bobRole ada (Constant 1000_000_000))
                        (Pay aliceAcc (Party aliceRole) ada (Constant 1000_000_000)
                        Close)
                    ] (Slot 200) Close
                ))] (Slot 100) Close
    let performs = performNotify [alice, bob]
    (md, tx) <- alice `performs` createContract params zeroCouponBond
    (md, tx) <- alice `performs` applyInputs tx params md [IDeposit aliceAcc aliceRole ada 850_000_000]
    bob `performs` applyInputs tx params md [IDeposit aliceAcc bobRole ada 1000_000_000]

    assertOwnFundsEq alice (adaValueOf 150 <> aliceToken)
    assertOwnFundsEq bob (adaValueOf 0 <> bobToken)


trustFundTest :: Property
trustFundTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList
        [ (walletPubKey alice, adaValueOf 1000), (walletPubKey bob, adaValueOf 1000) ] }) $ do
    -- Init a contract
    let alicePk = PK $ (pubKeyHash $ walletPubKey alice)
        aliceAcc = AccountId 0 alicePk
        bobPk = PK $ (pubKeyHash $ walletPubKey bob)
        update = updateAll [alice, bob]
    update

    let params = defaultMarloweParams
    let chId = ChoiceId "1" alicePk

    let contract = When [
            Case (Choice chId [Bound 100_000000 1500_000000])
                (When [Case
                    (Deposit aliceAcc alicePk ada (ChoiceValue chId (Constant 0)))
                        (When [Case (Notify (SlotIntervalStart `ValueGE` Constant 150))
                            (Pay aliceAcc (Party bobPk) ada
                                (ChoiceValue chId (Constant 0)) Close)]
                        (Slot 300) Close)
                    ] (Slot 200) Close)
            ] (Slot 100) Close

    let performs = performNotify [alice, bob]
    (md, tx) <- alice `performs` createContract params contract
    (md, tx) <- alice `performs` applyInputs tx params md
        [ IChoice chId 256_000000
        , IDeposit aliceAcc alicePk ada 256_000000]
    addBlocksAndNotify [alice, bob] 150
    bob `performs` notify tx params md

    assertOwnFundsEq alice (adaValueOf 744)
    assertOwnFundsEq bob (adaValueOf 1256)


makeProgressTest :: Property
makeProgressTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList
        [ (walletPubKey alice, adaValueOf 1000), (walletPubKey bob, adaValueOf 1000) ] }) $ do
    -- Init a contract
    let alicePk = PK $ (pubKeyHash $ walletPubKey alice)
        aliceAcc = AccountId 0 alicePk
        bobPk = PK $ (pubKeyHash $ walletPubKey bob)
        update = updateAll [alice, bob]
    update

    let params = defaultMarloweParams

    let contract = If (SlotIntervalStart `ValueLT` Constant 10)
            (When [Case (Deposit aliceAcc alicePk ada (Constant 500_000000))
                    (Pay aliceAcc (Party bobPk) ada
                        (AvailableMoney aliceAcc ada) Close)
                  ] (Slot 100) Close)
            Close

    let performs = performNotify [alice, bob]
    (md, tx) <- alice `performs` createContract params contract
    addBlocksAndNotify [alice, bob] 5
    (md, tx) <- alice `performs` makeProgress tx params md
    void $ alice `performs` deposit tx params md aliceAcc ada 500_000000

    assertOwnFundsEq alice (adaValueOf 500)
    assertOwnFundsEq bob (adaValueOf 1500)


pubKeyGen :: Gen PubKey
pubKeyGen = toPublicKey . (knownPrivateKeys !!) <$> integral (Range.linear 0 9)


uniqueContractHash :: IO ()
uniqueContractHash = do
    let params cs = MarloweParams
            { rolesCurrency = cs
            , rolePayoutValidatorHash = validatorHash rolePayoutScript }

    let hash1 = validatorHash $ validatorScript (params "11")
    let hash2 = validatorHash $ validatorScript (params "22")
    let hash3 = validatorHash $ validatorScript (params "22")
    assertBool "Hashes must be different" (hash1 /= hash2)
    assertBool "Hashes must be same" (hash2 == hash3)


validatorSize :: IO ()
validatorSize = do
    let validator = validatorScript defaultMarloweParams
    let vsize = BS.length $ Write.toStrictByteString (Serialise.encode validator)
    assertBool "Validator is too large" (vsize < 800000)


-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkMarloweTrace :: MarloweScenario -> Eff.Eff EmulatorEffs () -> Property
checkMarloweTrace MarloweScenario{mlInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = mlInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert (null (view (chainState . txPool) st))


updateAll :: [Wallet] -> Eff.Eff EmulatorEffs ()
updateAll wallets = processPending >>= void . walletsNotifyBlock wallets


performNotify :: [Wallet] -> Wallet -> Eff.Eff EmulatedWalletEffects (MarloweData, Tx) -> Eff.Eff EmulatorEffs (MarloweData, Tx)
performNotify wallets actor action = do
    (md, tx) <- walletAction actor action
    processPending >>= void . walletsNotifyBlock wallets
    assertIsValidated tx
    return (md, tx)


checkEqValue :: Property
checkEqValue = property $ do
    pk1 <- pubKeyHash <$> forAll pubKeyGen
    pk2 <- pubKeyHash <$> forAll pubKeyGen
    let value = boundedValue [PK pk1, PK pk2] []
    a <- forAll value
    b <- forAll value
    c <- forAll value
    Hedgehog.assert (a P.== a) -- reflective
    Hedgehog.assert (a P.== b == b P.== a) -- symmetric
    -- transitive
    Hedgehog.assert (if a P.== b && b P.== c then a P.== c else True)


doubleNegation :: Property
doubleNegation = property $ do
    pk1 <- pubKeyHash <$> forAll pubKeyGen
    pk2 <- pubKeyHash <$> forAll pubKeyGen
    let value = boundedValue [PK pk1, PK pk2] []
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    a <- forAll value
    eval (NegValue (NegValue a)) === eval a


valuesFormAbelianGroup :: Property
valuesFormAbelianGroup = property $ do
    let pk1 = pubKeyHash $ toPublicKey privateKey1
    let pk2 = pubKeyHash $ toPublicKey privateKey2
    let value = boundedValue [PK pk1, PK pk2] []
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    a <- forAll value
    b <- forAll value
    c <- forAll value
    -- associativity of addition
    eval (AddValue (AddValue a b) c) === eval (AddValue a (AddValue b c))
    -- commutativity of addition
    eval (AddValue a b) === eval (AddValue b a)
    -- additive identity
    eval (AddValue a (Constant 0)) === eval a
    -- additive inverse
    eval (AddValue a (NegValue a)) === 0
    -- substraction works
    eval (SubValue (AddValue a b) b) === eval a


scaleRoundingTest :: Property
scaleRoundingTest = property $ do
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    -- test half-even rounding
    n <- forAll amount
    d <- forAll (Gen.filter (/= 0) amount)
    eval (Scale (n P.% d) (Constant 1)) === round (n % d)


scaleMulTest :: Property
scaleMulTest = property $ do
    let pk1 = pubKeyHash $ toPublicKey privateKey1
    let pk2 = pubKeyHash $ toPublicKey privateKey2
    let value = boundedValue [PK pk1, PK pk2] []
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    a <- forAll value
    eval (Scale (0 P.% 1) a) === 0
    eval (Scale (1 P.% 1) a) === eval a


valueSerialization :: Property
valueSerialization = property $ do
    let pk1 = pubKeyHash $ toPublicKey privateKey1
    let pk2 = pubKeyHash $ toPublicKey privateKey2
    let value = boundedValue [PK pk1, PK pk2] []
    a <- forAll value
    case (decode $ encode a) of
        Just decoded -> a === decoded
        Nothing      -> Hedgehog.failure

pangramContractSerialization :: IO ()
pangramContractSerialization = do
    contract <- readFile "test/contract.json"
    let decoded :: Maybe Contract
        decoded = decode (fromString contract)
    case decoded of
        Just cont -> Just cont @=? (decode $ encode cont)
        _         -> assertFailure "Nope"
