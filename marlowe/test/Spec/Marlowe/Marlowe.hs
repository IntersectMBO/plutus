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

import           Control.Lens                   (view)
import           Control.Monad                  (void)
import qualified Control.Monad.Freer            as Eff
import qualified Control.Monad.Freer.Error      as Eff
import qualified Data.ByteString                as BS
import           Data.Either                    (isRight)
import qualified Data.Map.Strict                as Map
import           Data.String

import qualified Codec.CBOR.Write               as Write
import qualified Codec.Serialise                as Serialise
import           Hedgehog                       (Gen, Property, forAll, property)
import qualified Hedgehog
import           Hedgehog.Gen                   (integral)
import qualified Hedgehog.Range                 as Range
import           Language.Marlowe
import qualified Language.PlutusTx.Prelude      as P
import           Ledger                         hiding (Value)
import           Ledger.Ada                     (adaValueOf)
import qualified Ledger.Value                   as Val
import           Spec.Marlowe.Common
import           Test.Tasty
import           Test.Tasty.Hedgehog            (HedgehogTestLimit (..), testProperty)
import           Test.Tasty.HUnit
import           Wallet                         (PubKey (..), WalletAPIError)
import           Wallet.Emulator
import           Wallet.Emulator.ChainIndex     (ChainIndexEffect)
import qualified Wallet.Emulator.Generators     as Gen
import           Wallet.Emulator.NodeClient
import           Wallet.Emulator.SigningProcess (SigningProcessEffect)
import           Wallet.Emulator.Wallet
import qualified Wallet.Generators              as Gen

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
{-# ANN module ("HLint: ignore Redundant if" :: String) #-}


tests :: TestTree
tests = localOption (HedgehogTestLimit $ Just 3) $ testGroup "Marlowe"
    [ testCase "Contracts with different creators have different hashes" uniqueContractHash
    , testCase "Pretty/Show/Read stuff" showReadStuff
    , testCase "Validator size is reasonable" validatorSize
    , testProperty "Value equality is reflexive, symmetric, and transitive" checkEqValue
    , testProperty "Value double negation" doubleNegation
    , testProperty "Values form abelian group" valuesFormAbelianGroup
    , testProperty "Zero Coupon Bond Contract" zeroCouponBondTest
    , testProperty "Zero Coupon Bond w/ Roles Contract" zeroCouponBondRolesTest
    , testProperty "Trust Fund Contract" trustFundTest
    , testProperty "Make progress Contract" makeProgressTest
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
pubKeyGen = toPublicKey . (knownPrivateKeys !!) <$> integral (Range.linear 0 10)


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


performNotify :: [Wallet] -> Wallet -> Eff.Eff '[WalletEffect, Eff.Error WalletAPIError, NodeClientEffect, ChainIndexEffect, SigningProcessEffect] (MarloweData, Tx) -> Eff.Eff EmulatorEffs (MarloweData, Tx)
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
    Hedgehog.assert (eval (NegValue (NegValue a)) == eval a)


valuesFormAbelianGroup :: Property
valuesFormAbelianGroup = property $ do
    pk1 <- pubKeyHash <$> forAll pubKeyGen
    pk2 <- pubKeyHash <$> forAll pubKeyGen
    let value = boundedValue [PK pk1, PK pk2] []
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
    assertEqual "alice" (Role "alice") (fromString "alice" :: Party)
    assertEqual "alice" (Role "alice") (read "Role \"alice\"")
    assertEqual "slot" (Slot 123) (read "123")
    let
        investor :: Party
        investor = "investor"
        issuer :: Party
        issuer = "issuer"
        contract = When [Case
            (Deposit (AccountId 0 investor) investor ada (Constant 850))
            (Pay (AccountId 0 investor) (Party issuer) ada (Constant 850)
                (When [Case
                    (Deposit (AccountId 0 investor) issuer ada (Constant 1000))
                    (Pay (AccountId 0 investor) (Party investor) ada
                        (Constant 1000) Close)] 20 Close))] 10 Close

    let contract2 :: Contract = Let (ValueId "id") (Constant 12) Close
    assertEqual "Contract" contract ((read . show . pretty) contract)
    assertEqual "ValueId"  contract2 (read "Let \"id\" (Constant 12) Close")
    assertEqual "ValueId"  contract2 ((read . show . pretty) contract2)
