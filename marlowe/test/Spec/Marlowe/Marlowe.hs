{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -w #-}
module Spec.Marlowe.Marlowe
    ( prop_noFalsePositives, tests, prop_showWorksForContracts, runManuallySameAsOldImplementation, prop_jsonLoops
    )
where

import           Control.Exception                     (SomeException, catch)
import qualified Data.ByteString.Lazy                  as BSL
import           Data.Maybe                            (isJust)
import           Language.Marlowe.Analysis.FSSemantics
import           Language.Marlowe.Client
import           Language.Marlowe.Semantics
import           Language.Marlowe.Util
import qualified Language.PlutusTx                     as PlutusTx
import           Ledger                                (pubKeyHash)
import qualified OldAnalysis.FSSemantics               as OldAnalysis
import           System.IO.Unsafe                      (unsafePerformIO)

import           Data.Aeson                            (decode, encode)
import qualified Data.ByteString                       as BS
import           Data.Either                           (isRight)
import qualified Data.Map.Strict                       as Map
import           Data.Ratio                            ((%))
import qualified Data.Set                              as S
import           Data.String

import qualified Codec.CBOR.Write                      as Write
import qualified Codec.Serialise                       as Serialise
import           Language.Haskell.Interpreter          (Extension (OverloadedStrings), MonadInterpreter,
                                                        OptionVal ((:=)), as, interpret, languageExtensions,
                                                        runInterpreter, set, setImports)
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice

import qualified Language.PlutusTx.AssocMap            as AssocMap
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
    [ testGroup "Cases"
        [ testCase "Contracts with different creators have different hashes" uniqueContractHash
        , testCase "Token Show instance respects HEX and Unicode" tokenShowTest
        , testCase "Pangram Contract serializes into valid JSON" pangramContractSerialization
        , testCase "State serializes into valid JSON" stateSerialization
        , testCase "Validator size is reasonable" validatorSize
        ]
    , testGroup "Properties"
        [ testProperty "Value equality is reflexive, symmetric, and transitive" checkEqValue
        , testProperty "Value double negation" doubleNegation
        , testProperty "Values form abelian group" valuesFormAbelianGroup
        , testProperty "Values can be serialized to JSON" valueSerialization
        , testProperty "Scale Value multiplies by a constant rational" scaleMulTest
        , testProperty "Multiply by zero" mulTest
        , testProperty "Scale rounding" scaleRoundingTest
        ]
    , testGroup "Contracts"
        [ zeroCouponBondTest
        , trustFundTest
        ]
    , testGroup "Static Analysis"
        [ testCase "Close is valid" closeIsValidTest
        , testCase "Mul analysis" mulAnalysisTest
        , testCase "FFI Test" ffiTest
        , testCase "Negative payment issues a warning" payNegativeGivesWarningTest
        , testProperty "No false positives" prop_noFalsePositives
        ]
    , testGroup "Marlowe JSON"
        [ testProperty "Serialise deserialise loops" prop_jsonLoops
        ]
    ]


alice, bob :: Wallet
alice = Wallet 1
bob = Wallet 2

alicePk = PK $ (pubKeyHash $ walletPubKey alice)
aliceAcc = AccountId 0 alicePk
bobPk = PK $ (pubKeyHash $ walletPubKey bob)


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

    let hash1 = scriptHash $ defaultScriptInstance (params "11")
    let hash2 = scriptHash $ defaultScriptInstance (params "22")
    let hash3 = scriptHash $ defaultScriptInstance (params "22")
    assertBool "Hashes must be different" (hash1 /= hash2)
    assertBool "Hashes must be same" (hash2 == hash3)



validatorSize :: IO ()
validatorSize = do
    let validator = validatorScript $ defaultScriptInstance defaultMarloweParams
    let vsize = BS.length $ Write.toStrictByteString (Serialise.encode validator)
    assertBool ("Validator is too large " <> show vsize) (vsize < 1500000)


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


{-# INLINABLE dummyFFI #-}
dummyFFI :: State -> Integer
dummyFFI _ = 42


doubleNegation :: Property
doubleNegation = property $ do
    let eval = evalValue
                (Environment { slotInterval = (Slot 10, Slot 1000), marloweFFI = defaultMarloweFFI })
                (emptyState (Slot 10))
                Close
    forAll valueGen $ \a -> eval (NegValue (NegValue a)) === eval a


valuesFormAbelianGroup :: Property
valuesFormAbelianGroup = property $ do
    let gen = do
            a <- valueGen
            b <- valueGen
            c <- valueGen
            return (a, b, c)
    let eval = evalValue
                    (Environment { slotInterval = (Slot 10, Slot 1000), marloweFFI = defaultMarloweFFI })
                    (emptyState (Slot 10))
                    Close
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
    let eval = evalValue
                (Environment { slotInterval = (Slot 10, Slot 1000), marloweFFI = defaultMarloweFFI })
                (emptyState (Slot 10))
                Close
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
    let eval = evalValue
                    (Environment { slotInterval = (Slot 10, Slot 1000), marloweFFI = defaultMarloweFFI })
                    (emptyState (Slot 10))
                    Close
    forAll valueGen $ \a ->
        eval (Scale (0 P.% 1) a) === 0 .&&. eval (Scale (1 P.% 1) a) === eval a


mulTest :: Property
mulTest = property $ do
    let eval = evalValue
                (Environment { slotInterval = (Slot 10, Slot 1000), marloweFFI = defaultMarloweFFI })
                (emptyState (Slot 10))
                Close
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
    let muliply = MulValue (Constant 500) (Constant 500)
        contract = If (muliply `ValueGE` Constant 10000)
                    Close
                    (Pay aliceAcc (Party alicePk) ada (Constant (-100)) Close)
    result <- warningsTrace defaultMarloweFFIInfo contract
    assertBool "Analysis ok" $ isContractValid result


ffiTest :: IO ()
ffiTest = do
    assertEqual "" 42 $ eval (emptyState (Slot 10)) Close (Call 0 [ArgInteger 42])
    assertEqual "Should be out of bounds"  12 $ eval (emptyState (Slot 10)) Close (Call 0 [ArgInteger 50])
    let contract = When [Case (Deposit aliceAcc alicePk ada (Constant 41))
                         (Pay aliceAcc (Party "bob") ada (Call 0 []) Close)] 123 Close
    res <- warningsTrace (marloweFFIInfoFromMarloweFFI testFFI) contract
    case res of
        CounterExample MkCounterExample{ceFFIValues} -> assertEqual "" 42 (ceFFIValues Map.! 0)
        _                                            -> assertFailure "Must find counterexample"
  where
    eval = evalValue (Environment { slotInterval = (Slot 10, Slot 1000), marloweFFI = testFFI })


{-# INLINABLE testFFI #-}
testFFI :: MarloweFFI
testFFI = MarloweFFI (AssocMap.fromList
    [ (0, (identity, FFInfo {ffiRangeBounds = [Bound 40 42], ffiOutOfBoundsValue = 12 }))
    ])


testCompiledFFI :: CompiledFFI
testCompiledFFI = (testFFI, $$(PlutusTx.compile [|| testFFI ||]))


{-# INLINABLE identity #-}
identity :: State -> Contract -> [FFArg] -> Integer
identity _ _ [ArgInteger x] = x
identity _ _ _              = 0


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


analyseContract :: Contract -> IO AnalysisResult
analyseContract contract = do
    res <- catch (warningsTrace defaultMarloweFFIInfo contract)
        (\exc -> return $ AnalysisError (show (exc :: SomeException)))
    return res


closeIsValidTest :: IO ()
closeIsValidTest = do
    result <- analyseContract Close
    case result of
        ValidContract -> return ()
        err           -> assertFailure (show err)


payNegativeGivesWarningTest :: IO ()
payNegativeGivesWarningTest = do
    let contract =
            When [Case (Deposit aliceAcc alicePk ada (Constant 10))
                  (Pay aliceAcc (Party "bob") ada (Constant (-10)) Close)] 123 Close
    result <- analyseContract contract
    case result of
        CounterExample MkCounterExample{ceWarnings=[TransactionNonPositivePay _ _ _ _]} -> return ()
        _ -> assertFailure $ "Contract must issue TransactionNonPositivePay warning: " <> show contract


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


hasCounterExample :: AnalysisResult -> Bool
hasCounterExample (CounterExample _) = True
hasCounterExample _                  = False

noFalsePositivesForContract :: Contract -> Property
noFalsePositivesForContract cont = unsafePerformIO $ do
    res <- analyseContract cont
    case res of
        AnalysisError err -> return $ counterexample err False
        answer -> return $ tabulate "Has counterexample" [show (hasCounterExample answer)]
                (case answer of
                    ValidContract ->
                        tabulate "Is empty contract" [show (cont == Close)]
                                True
                    CounterExample (MkCounterExample{ceInitialSlot,ceTransactionInputs,ceWarnings}) ->
                        counterexample ("Trace: " ++ show (ceInitialSlot, ceTransactionInputs)) $
                            tabulate "Number of warnings" [show (length ceWarnings)] (ceWarnings =/= []))


wrapLeft :: IO (Either a b) -> IO (Either (Either c a) b)
wrapLeft r = do
    tempRes <- r
    return (case tempRes of
                Left x  -> Left (Right x)
                Right y -> Right y)


prop_noFalsePositives :: Property
prop_noFalsePositives = forAllShrink contractGen shrinkContract noFalsePositivesForContract


sameAsOldImplementation :: Contract -> Property
sameAsOldImplementation cont = unsafePerformIO $ do
    res <- analyseContract cont
    res2 <- catch (wrapLeft $ OldAnalysis.warningsTrace cont)
            (\exc -> return $ Left (Left (exc :: SomeException)))
    let result = case (res, res2) of
            (ValidContract, Right Nothing)     -> label "No counterexample" True
            (CounterExample _, Right Nothing)  -> label "Old version couldn't see counterexample" True
            (CounterExample _, Right (Just _)) -> label "Both versions found counterexample" True
            (AnalysisError _, Left _)          -> label "Both solvers failed" True
            (AnalysisError _, _)               -> label "Solver for new version failed" True
            (_, Left _)                        -> label "Solver for old version failed" True
            problems                           -> counterexample (show problems) False
    return result


runManuallySameAsOldImplementation :: Property
runManuallySameAsOldImplementation =
  forAllShrink contractGen shrinkContract sameAsOldImplementation

jsonLoops :: Contract -> Property
jsonLoops cont = decode (encode cont) === Just cont

prop_jsonLoops :: Property
prop_jsonLoops = withMaxSuccess 1000 $ forAllShrink contractGen shrinkContract jsonLoops
