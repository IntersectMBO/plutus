module Marlowe.LintTests where

import Prelude
import Data.Array (singleton)
import Data.Either (Either(..))
import Data.Set (toUnfoldable)
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\), (/\))
import Marlowe.Linter (lint, State(..))
import Marlowe.Parser (parseContract)
import Test.Unit (TestSuite, Test, suite, test, failure)
import Test.Unit.Assert as Assert

all :: TestSuite
all = do
  suite "Marlowe.Linter reports simplification" do
    test "in Let construct" $ letSimplifies
    test "in Deposit construct" $ depositSimplifies
    test "in Pay construct" $ paySimplifies
    test "in AddValue" $ addValueSimplifies
    test "of AddValue with 0 constant" $ addValueSimplifiesWithZero
    test "in SubValue" $ subValueSimplifies
    test "of SubValue with 0 constant" $ subValueSimplifiesWithZero
    test "in If construct" $ ifSimplifies
    test "in Notify construct" $ notifySimplifies
    test "in Assert construct" $ assertSimplifies
    test "in AndObs" $ andObsSimplifies
    test "of AndObs with True constant" $ andObsSimplifiesWithTrue
    test "in OrObs" $ orObsSimplifies
    test "of OrObs with False constant" $ orObsSimplifiesWithFalse
    test "of non-reduced Scale" $ nonReducedScaleSimplified
    test "of Scale with constant" $ scaleConstantSimplified
    test "of Scale with constant expression" $ scaleConstantExpressionSimplified
  suite "Marlowe.Linter reports bad pratices" do
    test "Let shadowing" $ letShadowing
    test "Non-increasing timeouts" $ nonIncreasingTimeouts
  suite "Marlowe.Linter reports unreachable code" do
    test "Unreachable If branch (then)" $ unreachableThen
    test "Unreachable If branch (else)" $ unreachableElse
    test "Unreachable Case (Notify)" $ unreachableCaseNotify
    test "Unreachable Case (empty Choice list)" $ unreachableCaseEmptyChoiceList
  suite "Marlowe.Linter reports bad contracts" do
    test "Undefined Let" $ undefinedLet
    test "Non-positive Deposit" $ nonPositiveDeposit
    test "Non-positive Pay" $ nonPositivePay
    test "Pay before deposit" $ payBeforeWarning
    test "Pay before deposit in branch" $ payBeforeWarningBranch
  suite "Marlowe.Linter does not report good contracts" do
    test "Defined Let" $ undefinedLet
    test "Positive Deposit" $ positiveDeposit
    test "Positive Pay" $ positivePay
    test "Pay to hole" payToHole

letContract :: String -> String
letContract subExpression = "Let \"simplifiableValue\" " <> subExpression <> " Close"

addContract :: String -> String
addContract subExpression = "Let \"simplifiableValue\" (AddValue SlotIntervalEnd " <> subExpression <> ") Close"

subContract :: String -> String
subContract subExpression = "Let \"simplifiableValue\" (SubValue SlotIntervalEnd " <> subExpression <> ") Close"

depositContract :: String -> String
depositContract subExpression = "When [Case (Deposit (AccountId 0 (Role \"role\")) (Role \"role\") (Token \"\" \"\") " <> subExpression <> ") Close] 10 Close"

payContract :: String -> String
payContract subExpression = "When [Case (Deposit (AccountId 0 (Role \"role\") ) (Role \"role\") (Token \"\" \"\") (Constant 100)) (Pay (AccountId 0 (Role \"role\")) (Party (Role \"role\")) (Token \"\" \"\") " <> subExpression <> " Close)] 10 Close"

notifyContract :: String -> String
notifyContract subExpression = "When [Case (Notify " <> subExpression <> ") Close] 10 Close"

assertContract :: String -> String
assertContract subExpression = "Assert " <> subExpression <> " Close"

ifContract :: String -> String
ifContract subExpression = "If " <> subExpression <> " Close Close"

andContract :: String -> String
andContract subExpression = "If (AndObs (ValueLE SlotIntervalEnd (Constant 20)) " <> subExpression <> ") Close Close"

orContract :: String -> String
orContract subExpression = "If (OrObs (ValueGE SlotIntervalEnd (Constant 5)) " <> subExpression <> ") Close Close"

makeValueSimplificationWarning :: String -> String -> String
makeValueSimplificationWarning simplifiableExpression simplification = "The value \"" <> simplifiableExpression <> "\" can be simplified to \"" <> simplification <> "\""

makeObservationSimplificationWarning :: String -> String -> String
makeObservationSimplificationWarning simplifiableExpression simplification = "The observation \"" <> simplifiableExpression <> "\" can be simplified to \"" <> simplification <> "\""

unCurry2 :: forall a b c. (a -> b -> c) -> (a /\ b) -> c
unCurry2 f (a /\ b) = f a b

testWarning :: forall a. (a -> Array String) -> (a -> String) -> a -> Test
testWarning makeWarning composeExpression expression = case parseContract $ composeExpression expression of
  Right contractTerm -> do
    let
      State st = lint contractTerm
    Assert.equal (makeWarning expression) $ map show $ toUnfoldable $ st.warnings
  Left err -> failure (show err)

testSimplificationWarning :: (String -> String -> String) -> (String -> String) -> String -> String -> Test
testSimplificationWarning f g simplifiableExpression simplification = testWarning (singleton <<< unCurry2 f) (g <<< fst) (simplifiableExpression /\ simplification)

testValueSimplificationWarning :: (String -> String) -> String -> String -> Test
testValueSimplificationWarning = testSimplificationWarning makeValueSimplificationWarning

testObservationSimplificationWarning :: (String -> String) -> String -> String -> Test
testObservationSimplificationWarning = testSimplificationWarning makeObservationSimplificationWarning

testWarningSimple :: String -> String -> Test
testWarningSimple expression warning = testWarning (const [ warning ]) (const expression) unit

testNoWarning :: String -> Test
testNoWarning expression = testWarning (const []) (const expression) unit

letSimplifies :: Test
letSimplifies =
  let
    simplifiableExpression = "(AddValue (SubValue (Constant 6) (NegValue (Constant -3))) (Constant -5))"

    simplification = "(Constant -2)"
  in
    testValueSimplificationWarning letContract simplifiableExpression simplification

depositSimplifies :: Test
depositSimplifies =
  let
    simplifiableExpression = "(AddValue (SubValue (Constant 3) (Constant -5)) (NegValue (Constant 7)))"

    simplification = "(Constant 1)"
  in
    testValueSimplificationWarning depositContract simplifiableExpression simplification

paySimplifies :: Test
paySimplifies =
  let
    simplifiableExpression = "(AddValue (SubValue (Constant 6) (Constant -1)) (NegValue (Constant 6)))"

    simplification = "(Constant 1)"
  in
    testValueSimplificationWarning payContract simplifiableExpression simplification

addValueSimplifies :: Test
addValueSimplifies =
  let
    simplifiableExpression = "(AddValue (NegValue (SubValue (Constant -1) (Constant 5))) (Constant -5))"

    simplification = "(Constant 1)"
  in
    testValueSimplificationWarning addContract simplifiableExpression simplification

addValueSimplifiesWithZero :: Test
addValueSimplifiesWithZero =
  let
    simplifiableExpression = "(AddValue SlotIntervalEnd (AddValue (NegValue (SubValue (Constant -1) (Constant 4))) (Constant -5)))"

    simplification = "SlotIntervalEnd"
  in
    testValueSimplificationWarning letContract simplifiableExpression simplification

subValueSimplifies :: Test
subValueSimplifies =
  let
    simplifiableExpression = "(SubValue (NegValue (SubValue (Constant -1) (Constant 5))) (Constant -2))"

    simplification = "(Constant 8)"
  in
    testValueSimplificationWarning subContract simplifiableExpression simplification

subValueSimplifiesWithZero :: Test
subValueSimplifiesWithZero =
  let
    simplifiableExpression = "(SubValue (AddValue (NegValue (SubValue (Constant -1) (Constant 4))) (Constant -5)) SlotIntervalEnd)"

    simplification = "(NegValue SlotIntervalEnd)"
  in
    testValueSimplificationWarning letContract simplifiableExpression simplification

notifySimplifies :: Test
notifySimplifies =
  let
    simplifiableExpression = "(OrObs (ValueLT SlotIntervalEnd (Constant 34)) (OrObs (NotObs (ValueEQ (AddValue (NegValue (Constant 2)) (Constant 5)) (Constant 3))) (NotObs (OrObs TrueObs FalseObs))))"

    simplification = "(ValueLT SlotIntervalEnd (Constant 34))"
  in
    testObservationSimplificationWarning notifyContract simplifiableExpression simplification

assertSimplifies :: Test
assertSimplifies =
  let
    simplifiableExpression = "(AndObs (ValueGT (Constant 14) SlotIntervalEnd) (AndObs (ValueEQ (AddValue (NegValue (Constant 2)) (Constant 5)) (Constant 3)) (OrObs FalseObs TrueObs)))"

    simplification = "(ValueGT (Constant 14) SlotIntervalEnd)"
  in
    testObservationSimplificationWarning assertContract simplifiableExpression simplification

ifSimplifies :: Test
ifSimplifies =
  let
    simplifiableExpression = "(OrObs (ValueGE SlotIntervalEnd (Constant 5)) (AndObs (NotObs (OrObs FalseObs (ValueEQ (AddValue (Constant -2) (Constant 3)) (Constant 1)))) TrueObs))"

    simplification = "(ValueGE SlotIntervalEnd (Constant 5))"
  in
    testObservationSimplificationWarning ifContract simplifiableExpression simplification

andObsSimplifies :: Test
andObsSimplifies =
  let
    simplifiableExpression = "(OrObs FalseObs (ValueEQ SlotIntervalEnd (Constant 2)))"

    simplification = "(ValueEQ SlotIntervalEnd (Constant 2))"
  in
    testObservationSimplificationWarning andContract simplifiableExpression simplification

andObsSimplifiesWithTrue :: Test
andObsSimplifiesWithTrue =
  let
    simplifiableExpression = "(AndObs TrueObs (ValueLE SlotIntervalEnd (Constant 6)))"

    simplification = "(ValueLE SlotIntervalEnd (Constant 6))"
  in
    testObservationSimplificationWarning ifContract simplifiableExpression simplification

orObsSimplifies :: Test
orObsSimplifies =
  let
    simplifiableExpression = "(AndObs TrueObs (ValueEQ SlotIntervalEnd (Constant 12)))"

    simplification = "(ValueEQ SlotIntervalEnd (Constant 12))"
  in
    testObservationSimplificationWarning orContract simplifiableExpression simplification

orObsSimplifiesWithFalse :: Test
orObsSimplifiesWithFalse =
  let
    simplifiableExpression = "(OrObs FalseObs (ValueGE SlotIntervalEnd (Constant 3)))"

    simplification = "(ValueGE SlotIntervalEnd (Constant 3))"
  in
    testObservationSimplificationWarning ifContract simplifiableExpression simplification

nonReducedScaleSimplified :: Test
nonReducedScaleSimplified =
  let
    simplifiableExpression = "(Scale (362%194) SlotIntervalStart)"

    simplification = "(Scale (181%97) SlotIntervalStart)"
  in
    testValueSimplificationWarning letContract simplifiableExpression simplification

scaleConstantSimplified :: Test
scaleConstantSimplified =
  let
    simplifiableExpression = "(Scale (7%3) (Constant 21))"

    simplification = "(Constant 49)"
  in
    testValueSimplificationWarning letContract simplifiableExpression simplification

scaleConstantExpressionSimplified :: Test
scaleConstantExpressionSimplified =
  let
    simplifiableExpression = "(Scale (1%3) (AddValue (Constant 9) (Constant 12)))"

    simplification = "(Constant 7)"
  in
    testValueSimplificationWarning letContract simplifiableExpression simplification

letShadowing :: Test
letShadowing = testWarningSimple "Let \"value\" (Constant 1) (Let \"value\" (Constant 1) Close)" "Let is redefining a ValueId that already exists"

nonIncreasingTimeouts :: Test
nonIncreasingTimeouts = testWarningSimple "When [] 5 (When [] 5 Close)" "Timeouts should always increase in value"

unreachableThen :: Test
unreachableThen = testWarningSimple "If FalseObs Close Close" "This contract is unreachable"

unreachableElse :: Test
unreachableElse = testWarningSimple "If TrueObs Close Close" "This contract is unreachable"

unreachableCaseNotify :: Test
unreachableCaseNotify =
  testWarningSimple "When [Case (Notify FalseObs) Close] 10 Close"
    "This case will never be used, because the Observation is always false"

unreachableCaseEmptyChoiceList :: Test
unreachableCaseEmptyChoiceList =
  testWarningSimple "When [Case (Choice (ChoiceId \"choice\" (Role \"alice\")) []) Close] 10 Close"
    "This case will never be used, because there are no options to choose"

undefinedLet :: Test
undefinedLet = testWarningSimple (letContract "(UseValue \"simplifiableValue\")") "The contract tries to Use a ValueId that has not been defined in a Let"

nonPositiveDeposit :: Test
nonPositiveDeposit = testWarningSimple (depositContract "(Constant 0)") "The contract can make a non-positive deposit"

negativeDeposit :: Test
negativeDeposit = testWarningSimple (depositContract "(Constant -1)") "The contract can make a non-positive deposit"

nonPositivePay :: Test
nonPositivePay = testWarningSimple (payContract "(Constant 0)") "The contract can make a non-positive payment"

negativePay :: Test
negativePay = testWarningSimple (payContract "(Constant -1)") "The contract can make a non-positive payment"

payBeforeWarning :: Test
payBeforeWarning = testWarningSimple contract "The contract makes a payment to account (AccountId 0 (Role \"role\")) before a deposit has been made"
  where
  contract = "When [Case (Deposit (AccountId 1 (Role \"role\") ) (Role \"role\") (Token \"\" \"\") (Constant 100)) (Pay (AccountId 0 (Role \"role\")) (Party (Role \"role\")) (Token \"\" \"\") (Constant 1) Close)] 10 Close"

payBeforeWarningBranch :: Test
payBeforeWarningBranch = testWarningSimple contract "The contract makes a payment to account (AccountId 1 (Role \"role\")) before a deposit has been made"
  where
  contract = "When [Case (Deposit (AccountId 1 (Role \"role\")) (Role \"role\") (Token \"\" \"\") (Constant 10)) Close] 2 (Pay (AccountId 1 (Role \"role\")) (Party (Role \"role\")) (Token \"\" \"\") (Constant 10) Close)"

payToHole :: Test
payToHole = testNoWarning contract
  where
  contract = "When [Case (Deposit (AccountId 1 (Role \"role\") ) (Role \"role\") (Token \"\" \"\") (Constant 100)) (Pay (AccountId 0 ?party) (Party (Role \"role\")) (Token \"\" \"\") (Constant 1) Close)] 10 Close"

normalLet :: Test
normalLet = testNoWarning "Let \"a\" (Constant 0) (Let \"b\" (UseValue \"a\") Close)"

positiveDeposit :: Test
positiveDeposit = testNoWarning (depositContract "(Constant 1)")

positivePay :: Test
positivePay = testNoWarning (payContract "(Constant 1)")
