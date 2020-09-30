{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -w #-}
module Spec.Marlowe.Marlowe
    ( prop_noFalsePositives, tests, prop_showWorksForContracts, runManuallySameAsOldImplementation, prop_jsonLoops
    )
where

import           Control.Exception                     (SomeException, catch)
import           Data.Maybe                            (isJust)
import           Language.Marlowe.Analysis.FSSemantics
import           Language.Marlowe.Client
import           Language.Marlowe.Semantics
import           Language.Marlowe.Util
import qualified OldAnalysis.FSSemantics               as OldAnalysis
import           System.IO.Unsafe                      (unsafePerformIO)

import           Data.Aeson                            (decode, encode)
import qualified Data.ByteString                       as BS
import           Data.Either                           (isRight)
import           Data.Ratio                            ((%))
import           Data.String

import qualified Codec.CBOR.Write                      as Write
import qualified Codec.Serialise                       as Serialise
import           Language.Haskell.Interpreter          (Extension (OverloadedStrings), MonadInterpreter,
                                                        OptionVal ((:=)), as, interpret, languageExtensions,
                                                        runInterpreter, set, setImports)
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice

import qualified Language.PlutusTx.Prelude             as P
import           Ledger                                hiding (Value)
import           Ledger.Ada                            (lovelaceValueOf)
import           Ledger.Typed.Scripts                  (scriptHash, validatorScript)
import           Spec.Marlowe.Common
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
{-# ANN module ("HLint: ignore Redundant if" :: String) #-}

tests :: TestTree
tests = testGroup "Marlowe"
    [ testCase "Contracts with different creators have different hashes" uniqueContractHash
    , testCase "Token Show instance respects HEX and Unicode" tokenShowTest
    , testCase "Pangram Contract serializes into valid JSON" pangramContractSerialization
    , testCase "State serializes into valid JSON" stateSerialization
    , testCase "Validator size is reasonable" validatorSize
    , testCase "Mul analysis" mulAnalysisTest
    , testProperty "Value equality is reflexive, symmetric, and transitive" checkEqValue
    , testProperty "Value double negation" doubleNegation
    , testProperty "Values form abelian group" valuesFormAbelianGroup
    , testProperty "Values can be serialized to JSON" valueSerialization
    , testProperty "Scale Value multiplies by a constant rational" scaleMulTest
    , testProperty "Multiply by zero" mulTest
    , testProperty "Scale rounding" scaleRoundingTest
    , zeroCouponBondTest
    , trustFundTest
    ]


alice, bob :: Wallet
alice = Wallet 1
bob = Wallet 2


zeroCouponBondTest :: TestTree
zeroCouponBondTest = checkPredicate @MarloweSchema @MarloweError "Zero Coupon Bond Contract" marlowePlutusContract
    (assertNoFailedTransactions
    -- /\ emulatorLog (const False) ""
    /\ assertDone alice (const True) "contract should close"
    /\ assertDone bob (const True) "contract should close"
    /\ walletFundsChange alice (lovelaceValueOf (150))
    /\ walletFundsChange bob (lovelaceValueOf (-150))
    ) $ do
    -- Init a contract
    let alicePk = PK $ (pubKeyHash $ walletPubKey alice)
        aliceAcc = AccountId 0 alicePk
        bobPk = PK $ (pubKeyHash $ walletPubKey bob)

    let params = defaultMarloweParams

    let zeroCouponBond = When [ Case
            (Deposit aliceAcc alicePk ada (Constant 850))
            (Pay aliceAcc (Party bobPk) ada (Constant 850)
                (When
                    [ Case (Deposit aliceAcc bobPk ada (Constant 1000)) Close] (Slot 200) Close
                ))] (Slot 100) Close
    callEndpoint @"create" alice (params, zeroCouponBond)
    handleBlockchainEvents alice
    addBlocks 1
    handleBlockchainEvents alice

    callEndpoint @"wait" bob (params)
    handleBlockchainEvents bob

    callEndpoint @"apply-inputs" alice (params, [IDeposit aliceAcc alicePk ada 850])
    handleBlockchainEvents alice
    addBlocks 1
    handleBlockchainEvents alice

    callEndpoint @"wait" alice (params)

    handleBlockchainEvents bob

    callEndpoint @"apply-inputs" bob (params, [IDeposit aliceAcc bobPk ada 1000])

    handleBlockchainEvents alice
    handleBlockchainEvents bob
    addBlocks 1
    handleBlockchainEvents alice
    handleBlockchainEvents bob


trustFundTest :: TestTree
trustFundTest = checkPredicate @MarloweSchema @MarloweError "Trust Fund Contract" marlowePlutusContract
    (assertNoFailedTransactions
    -- /\ emulatorLog (const False) ""
    /\ assertDone alice (const True) "contract should close"
    /\ assertDone bob (const True) "contract should close"
    /\ walletFundsChange alice (lovelaceValueOf (-256))
    /\ walletFundsChange bob (lovelaceValueOf (256))
    ) $ do
    -- Init a contract
    let alicePk = PK $ pubKeyHash $ walletPubKey alice
        aliceAcc = AccountId 0 alicePk
        bobPk = PK $ pubKeyHash $ walletPubKey bob

    let params = defaultMarloweParams
    let chId = ChoiceId "1" alicePk

    let contract = When [
            Case (Choice chId [Bound 100 1500])
                (When [Case
                    (Deposit aliceAcc alicePk ada (ChoiceValue chId))
                        (When [Case (Notify (SlotIntervalStart `ValueGE` Constant 150))
                            (Pay aliceAcc (Party bobPk) ada
                                (ChoiceValue chId) Close)]
                        (Slot 300) Close)
                    ] (Slot 200) Close)
            ] (Slot 100) Close

    callEndpoint @"create" alice (params, contract)
    handleBlockchainEvents alice
    addBlocks 1
    handleBlockchainEvents alice

    callEndpoint @"wait" bob (params)
    handleBlockchainEvents bob

    callEndpoint @"apply-inputs" alice (params,
        [ IChoice chId 256
        , IDeposit aliceAcc alicePk ada 256
        ])
    handleBlockchainEvents alice
    addBlocks 150
    handleBlockchainEvents alice

    callEndpoint @"wait" alice (params)

    handleBlockchainEvents bob

    callEndpoint @"apply-inputs" bob (params, [INotify])

    handleBlockchainEvents alice
    handleBlockchainEvents bob
    addBlocks 1
    handleBlockchainEvents alice
    handleBlockchainEvents bob


uniqueContractHash :: IO ()
uniqueContractHash = do
    let params cs = MarloweParams
            { rolesCurrency = cs
            , rolePayoutValidatorHash = validatorHash rolePayoutScript }

    let hash1 = scriptHash $ scriptInstance (params "11")
    let hash2 = scriptHash $ scriptInstance (params "22")
    let hash3 = scriptHash $ scriptInstance (params "22")
    assertBool "Hashes must be different" (hash1 /= hash2)
    assertBool "Hashes must be same" (hash2 == hash3)


validatorSize :: IO ()
validatorSize = do
    let validator = validatorScript $ scriptInstance defaultMarloweParams
    let vsize = BS.length $ Write.toStrictByteString (Serialise.encode validator)
    assertBool ("Validator is too large " <> show vsize) (vsize < 1100000)


checkEqValue :: Property
checkEqValue = property $ do
    let gen = do
            a <- valueGen
            b <- valueGen
            c <- valueGen
            return (a, b, c)
    forAll gen $ \(a, b, c) ->
        (a P.== a) -- reflective
            .&&. (a P.== b == b P.== a) -- symmetric
            .&&. (if a P.== b && b P.== c then a P.== c else True) -- transitive


doubleNegation :: Property
doubleNegation = property $ do
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    forAll valueGen $ \a -> eval (NegValue (NegValue a)) === eval a


valuesFormAbelianGroup :: Property
valuesFormAbelianGroup = property $ do
    let gen = do
            a <- valueGen
            b <- valueGen
            c <- valueGen
            return (a, b, c)
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    forAll gen $ \(a, b, c) ->
        -- associativity of addition
        eval (AddValue (AddValue a b) c) === eval (AddValue a (AddValue b c)) .&&.
        -- commutativity of addition
        eval (AddValue a b) === eval (AddValue b a) .&&.
        -- additive identity
        eval (AddValue a (Constant 0)) === eval a .&&.
        -- additive inverse
        eval (AddValue a (NegValue a)) === 0 .&&.
        -- substraction works
        eval (SubValue (AddValue a b) b) === eval a


scaleRoundingTest :: Property
scaleRoundingTest = property $ do
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    -- test half-even rounding
    let gen = do
            n <- amount
            d <- suchThat amount (/= 0)
            return (n, d)
    forAll gen $ \(n, d) -> eval (Scale (n P.% d) (Constant 1)) === halfAwayRound (n % d)
    where
      halfAwayRound fraction = let (n,f) = properFraction fraction in n + round (f + 1) - 1


scaleMulTest :: Property
scaleMulTest = property $ do
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    forAll valueGen $ \a ->
        eval (Scale (0 P.% 1) a) === 0 .&&. eval (Scale (1 P.% 1) a) === eval a


mulTest :: Property
mulTest = property $ do
    let eval = evalValue (Environment (Slot 10, Slot 1000)) (emptyState (Slot 10))
    forAll valueGen $ \a ->
        eval (MulValue (Constant 0) a) === 0


valueSerialization :: Property
valueSerialization = property $
    forAll valueGen $ \a ->
        let decoded :: Maybe (Value Observation)
            decoded = decode $ encode a
        in Just a === decoded


mulAnalysisTest :: IO ()
mulAnalysisTest = do
    let muliply = foldl (\a _ -> MulValue (UseValue $ ValueId "a") a) (Constant 1) [1..100]
        alicePk = PK $ pubKeyHash $ walletPubKey alice
        aliceAcc = AccountId 0 alicePk
        contract = If (muliply `ValueGE` Constant 10000) Close (Pay aliceAcc (Party alicePk) ada (Constant (-100)) Close)
    result <- warningsTrace contract
    --print result
    assertBool "Analysis ok" $ isRight result


pangramContractSerialization :: IO ()
pangramContractSerialization = do
    contract <- readFile "test/contract.json"
    let decoded :: Maybe Contract
        decoded = decode (fromString contract)
    case decoded of
        Just cont -> Just cont @=? (decode $ encode cont)
        _         -> assertFailure "Nope"


tokenShowTest :: IO ()
tokenShowTest = do
    -- SCP-834, CurrencySymbol is HEX encoded ByteString,
    -- and TokenSymbol as UTF8 encoded Unicode string
    let actual :: Value Observation
        actual = AvailableMoney (AccountId 1 (Role "alice")) (Token "00010afF" "ÚSD©")

    show actual @=? "AvailableMoney (AccountId 1 \"alice\") (Token \"00010aff\" \"ÚSD©\")"


stateSerialization :: IO ()
stateSerialization = do
    state <- readFile "test/state.json"
    let decoded :: Maybe State
        decoded = decode (fromString state)
    case decoded of
        Just st ->
            case decode $ encode st of
                Just st' -> assertBool "Should be equal" (st P.== st')
                Nothing  -> assertFailure "Nope"
        Nothing -> assertFailure "Nope"

prop_showWorksForContracts :: Property
prop_showWorksForContracts = forAllShrink contractGen shrinkContract showWorksForContract


showWorksForContract :: Contract -> Property
showWorksForContract contract = unsafePerformIO $ do
  res <- runInterpreter $ setImports ["Language.Marlowe"]
                        >> set [ languageExtensions := [ OverloadedStrings ] ]
                        >> interpretContractString (show contract)
  return (case res of
            Right x  -> x === contract
            Left err -> counterexample (show err) False)


interpretContractString :: MonadInterpreter m => String -> m Contract
interpretContractString contractStr = interpret contractStr (as :: Contract)


noFalsePositivesForContract :: Contract -> Property
noFalsePositivesForContract cont =
  unsafePerformIO (do res <- catch (wrapLeft $ warningsTrace cont)
                                   (\exc -> return $ Left (Left (exc :: SomeException)))
                      return (case res of
                                Left err -> counterexample (show err) False
                                Right answer ->
                                   tabulate "Has counterexample" [show (isJust answer)]
                                   (case answer of
                                      Nothing ->
                                         tabulate "Is empty contract" [show (cont == Close)]
                                                  True
                                      Just (is, li, warns) ->
                                         counterexample ("Trace: " ++ show (is, li)) $
                                         tabulate "Number of warnings" [show (length warns)]
                                                  (warns =/= []))))


wrapLeft :: IO (Either a b) -> IO (Either (Either c a) b)
wrapLeft r = do tempRes <- r
                return (case tempRes of
                          Left x  -> Left (Right x)
                          Right y -> Right y)


prop_noFalsePositives :: Property
prop_noFalsePositives = forAllShrink contractGen shrinkContract noFalsePositivesForContract


sameAsOldImplementation :: Contract -> Property
sameAsOldImplementation cont =
  unsafePerformIO (do res <- catch (wrapLeft $ warningsTrace cont)
                                   (\exc -> return $ Left (Left (exc :: SomeException)))
                      res2 <- catch (wrapLeft $ OldAnalysis.warningsTrace cont)
                                    (\exc -> return $ Left (Left (exc :: SomeException)))
                      return (case (res, res2) of
                                 (Right Nothing, Right Nothing) ->
                                    label "No counterexample" True
                                 (Right (Just _), Right Nothing) ->
                                    label "Old version couldn't see counterexample" True
                                 (Right (Just _), Right (Just _)) ->
                                    label "Both versions found counterexample" True
                                 (Left _, Left _) ->
                                    label "Both solvers failed" True
                                 (Left _, _) ->
                                    label "Solver for new version failed" True
                                 (_, Left _) ->
                                    label "Solver for old version failed" True
                                 problems -> counterexample (show problems) False))


runManuallySameAsOldImplementation :: Property
runManuallySameAsOldImplementation =
  forAllShrink contractGen shrinkContract sameAsOldImplementation

jsonLoops :: Contract -> Property
jsonLoops cont = decode (encode cont) === Just cont

prop_jsonLoops :: Property
prop_jsonLoops = withMaxSuccess 1000 $ forAllShrink contractGen shrinkContract jsonLoops

