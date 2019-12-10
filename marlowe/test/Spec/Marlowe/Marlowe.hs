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
import qualified Control.Monad.Freer.Error  as Eff
import qualified Data.ByteString            as BS
import           Data.Either                (isRight)
import qualified Data.Map.Strict            as Map
import           Data.String

import qualified Codec.CBOR.Write           as Write
import qualified Codec.Serialise            as Serialise
import           Hedgehog                   (Gen, Property, forAll, property)
import qualified Hedgehog
import           Hedgehog.Gen               (integral)
import qualified Hedgehog.Range             as Range
import           Language.Marlowe
import qualified Language.PlutusTx.AssocMap as AssocMap
import qualified Language.PlutusTx.Prelude  as P
import           Ledger                     hiding (Value)
import qualified Ledger.Ada                 as Ada
import           Spec.Marlowe.Common
import           Test.Tasty
import           Test.Tasty.Hedgehog        (HedgehogTestLimit (..), testProperty)
import           Test.Tasty.HUnit
import           Wallet                     (PubKey (..), WalletAPIError)
import           Wallet.Emulator
import qualified Wallet.Emulator.Generators as Gen
import           Wallet.Emulator.NodeClient
import           Wallet.Emulator.Wallet
import qualified Wallet.Generators          as Gen

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
{-# ANN module ("HLint: ignore Redundant if" :: String) #-}


tests :: TestTree
tests = localOption (HedgehogTestLimit $ Just 3) $ testGroup "Marlowe"
    [ testCase "Contracts with different creators have different hashes" uniqueContractHash
    , testCase "Pretty/Show/Read stuff" showReadStuff
    , testCase "Validator size is reasonable" validatorSize
    , testCase "getSignatures collects correct signatures" getSignaturesTest
    , testProperty "Value equality is reflexive, symmetric, and transitive" checkEqValue
    , testProperty "Value double negation" doubleNegation
    , testProperty "Values form abelian group" valuesFormAbelianGroup
    , testProperty "Zero Coupon Bond Contract" zeroCouponBondTest
    , testProperty "Trust Fund Contract" trustFundTest
    , testProperty "Make progress Contract" makeProgressTest
    ]


alice, bob, carol :: Wallet
alice = Wallet 1
bob = Wallet 2
carol = Wallet 3


getSignaturesTest :: IO ()
getSignaturesTest = do
    let alicePk = walletPubKey alice
    let bobPk = walletPubKey bob
    let deposit pk = IDeposit (AccountId 0 alicePk) pk (Ada.adaOf 256)
    let choice pk = IChoice (ChoiceId "choice" pk) 23
    let sigs = AssocMap.toList . getSignatures
    [] @=? sigs []
    [] @=? sigs [INotify]
    [(alicePk, True)] @=? sigs [deposit alicePk]
    [(alicePk, True)] @=? sigs [choice alicePk]
    [(alicePk, True)] @=? sigs [deposit alicePk, choice alicePk]
    [(alicePk, True), (bobPk, True)] @=? sigs [deposit alicePk, choice bobPk]


zeroCouponBondTest :: Property
zeroCouponBondTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList
        [ (walletPubKey alice, Ada.adaValueOf 1000), (walletPubKey bob, Ada.adaValueOf 1000) ] }) $ do
    -- Init a contract
    let alicePk = walletPubKey alice
        aliceAcc = AccountId 0 alicePk
        bobPk = walletPubKey bob
        update = updateAll [alice, bob]
    update

    let zeroCouponBond = When [ Case (Deposit aliceAcc alicePk (Constant 850_000_000))
            (Pay aliceAcc (Party bobPk) (Constant 850_000_000)
                (When
                    [ Case (Deposit aliceAcc bobPk (Constant 1000_000_000))
                        (Pay aliceAcc (Party alicePk) (Constant 1000_000_000) Close)
                    ] (Slot 200) Close
                ))] (Slot 100) Close

    let performs = performNotify [alice, bob]
    (md, tx) <- alice `performs` createContract zeroCouponBond
    (md, tx) <- alice `performs` deposit tx md aliceAcc (Ada.adaOf 850)
    bob `performs` deposit tx md aliceAcc (Ada.adaOf 1000)

    assertOwnFundsEq alice (Ada.adaValueOf 1150)
    assertOwnFundsEq bob (Ada.adaValueOf 850)


trustFundTest :: Property
trustFundTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList
        [ (walletPubKey alice, Ada.adaValueOf 1000), (walletPubKey bob, Ada.adaValueOf 1000) ] }) $ do
    -- Init a contract
    let alicePk = walletPubKey alice
        aliceAcc = AccountId 0 alicePk
        bobPk = walletPubKey bob
        update = updateAll [alice, bob]
    update

    let chId = ChoiceId "1" alicePk

    let contract = When [
            Case (Choice chId [Bound 100_000000 1500_000000])
                (When [
                    Case (Deposit aliceAcc alicePk (ChoiceValue chId (Constant 0)))
                        (When [Case (Notify (SlotIntervalStart `ValueGE` Constant 150))
                            (Pay aliceAcc (Party bobPk) (ChoiceValue chId (Constant 0)) Close)]
                        (Slot 300) Close)
                    ] (Slot 200) Close)
            ] (Slot 100) Close

    let performs = performNotify [alice, bob]
    (md, tx) <- alice `performs` createContract contract
    (md, tx) <- alice `performs` applyInputs tx md
        [ IChoice chId 256_000000
        , IDeposit aliceAcc alicePk (Ada.adaOf 256)]
    addBlocksAndNotify [alice, bob] 150
    bob `performs` notify tx md

    assertOwnFundsEq alice (Ada.adaValueOf 744)
    assertOwnFundsEq bob (Ada.adaValueOf 1256)


makeProgressTest :: Property
makeProgressTest = checkMarloweTrace (MarloweScenario {
    mlInitialBalances = Map.fromList
        [ (walletPubKey alice, Ada.adaValueOf 1000), (walletPubKey bob, Ada.adaValueOf 1000) ] }) $ do
    -- Init a contract
    let alicePk = walletPubKey alice
        aliceAcc = AccountId 0 alicePk
        bobPk = walletPubKey bob
        update = updateAll [alice, bob]
    update

    let contract = If (SlotIntervalStart `ValueLT` Constant 10)
            (When [Case (Deposit aliceAcc alicePk (Constant 500_000000))
                    (Pay aliceAcc (Party bobPk) (AvailableMoney aliceAcc) Close)]
                        (Slot 100) Close)
            Close

    let performs = performNotify [alice, bob]
    (md, tx) <- alice `performs` createContract contract
    addBlocksAndNotify [alice, bob] 5
    (md, tx) <- alice `performs` makeProgress tx md
    void $ alice `performs` deposit tx md aliceAcc (Ada.adaOf 500)

    assertOwnFundsEq alice (Ada.adaValueOf 500)
    assertOwnFundsEq bob (Ada.adaValueOf 1500)


pubKeyGen :: Gen PubKey
pubKeyGen = toPublicKey . (knownPrivateKeys !!) <$> integral (Range.linear 0 10)


uniqueContractHash :: IO ()
uniqueContractHash = do
    let pk1 = toPublicKey privateKey1
    let pk2 = toPublicKey privateKey2
    let hash1 = validatorHash $ validatorScript pk1
    let hash2 = validatorHash $ validatorScript pk2
    assertBool "Hashes must be different" (hash1 /= hash2)


validatorSize :: IO ()
validatorSize = do
    let pk1 = toPublicKey privateKey1
    let vsize = BS.length $ Write.toStrictByteString (Serialise.encode $ validatorScript pk1)
    assertBool "Validator is too large" (vsize < 600000)


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


performNotify :: [Wallet] -> Wallet -> Eff.Eff '[WalletEffect, Eff.Error WalletAPIError, NodeClientEffect] (MarloweData, Tx) -> Eff.Eff EmulatorEffs (MarloweData, Tx)
performNotify wallets actor action = do
    (md, tx) <- walletAction actor action
    processPending >>= void . walletsNotifyBlock wallets
    assertIsValidated tx
    return (md, tx)


checkEqValue :: Property
checkEqValue = property $ do
    pk1 <- forAll pubKeyGen
    pk2 <- forAll pubKeyGen
    let value = boundedValue [pk1, pk2] []
    a <- forAll value
    b <- forAll value
    c <- forAll value
    Hedgehog.assert (a P.== a) -- reflective
    Hedgehog.assert (a P.== b == b P.== a) -- symmetric
    -- transitive
    Hedgehog.assert (if a P.== b && b P.== c then a P.== c else True)


doubleNegation :: Property
doubleNegation = property $ do
    pk1 <- forAll pubKeyGen
    pk2 <- forAll pubKeyGen
    let value = boundedValue [pk1, pk2] []
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    a <- forAll value
    Hedgehog.assert (eval (NegValue (NegValue a)) == eval a)


valuesFormAbelianGroup :: Property
valuesFormAbelianGroup = property $ do
    pk1 <- forAll pubKeyGen
    pk2 <- forAll pubKeyGen
    let value = boundedValue [pk1, pk2] []
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    a <- forAll value
    b <- forAll value
    c <- forAll value
    -- associativity of addition
    Hedgehog.assert (eval (AddValue (AddValue a b) c) == eval (AddValue a (AddValue b c)))
    -- commutativity of addition
    Hedgehog.assert (eval (AddValue a b) == eval (AddValue b a))
    -- additive identity
    Hedgehog.assert (eval (AddValue a (Constant 0)) == eval a)
    -- additive inverse
    Hedgehog.assert (eval (AddValue a (NegValue a)) == 0)
    -- substraction works
    Hedgehog.assert (eval (SubValue (AddValue a b) b) == eval a)


showReadStuff :: IO ()
showReadStuff = do
    assertEqual "alice" (fromString "alice" :: PubKey) (read "\"alice\"")
    assertEqual "slot" (Slot 123) (read "123")
    let contractString = "When [(Case (Deposit (AccountId 0 \"investor\") \"investor\" \
        \(Constant 850)) (Pay (AccountId 0 \"investor\") (Party \"issuer\") (Constant 850) \
        \(When [ (Case (Deposit (AccountId 0 \"investor\") \"issuer\" (Constant 1000)) \
        \(Pay (AccountId 0 \"investor\") (Party \"investor\") (Constant 1000) Close))] \
        \20 Close)))] 10 Close"
    let contract :: Contract = read contractString
    let contract2 :: Contract = Let (ValueId "id") (Constant 12) Close
    assertEqual "Contract" contract ((read . show . pretty) contract)
    assertEqual "ValueId"  contract2 (read "Let \"id\" (Constant 12) Close")
    assertEqual "ValueId"  contract2 ((read . show . pretty) contract2)
