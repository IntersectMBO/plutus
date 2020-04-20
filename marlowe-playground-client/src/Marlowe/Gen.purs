module Marlowe.Gen where

import Prelude
import Control.Lazy (class Lazy, defer)
import Control.Monad.Gen (class MonadGen, chooseInt, resize, suchThat, unfoldable)
import Control.Monad.Gen as Gen
import Control.Monad.Reader (class MonadAsk, ask)
import Control.Monad.Rec.Class (class MonadRec)
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Char.Gen (genAlpha, genDigitChar)
import Data.Foldable (class Foldable)
import Data.NonEmpty (NonEmpty, foldl1, (:|))
import Data.String.CodeUnits (fromCharArray)
import Marlowe.Holes (AccountId(..), Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Observation(..), Party(..), Payee(..), Term(..), TermWrapper(..), Token(..), Value(..), ValueId(..))
import Marlowe.Semantics (Rational(..), CurrencySymbol, Input(..), PubKey, Slot(..), SlotInterval(..), TokenName, TransactionInput(..), TransactionWarning(..))
import Marlowe.Semantics as S
import Text.Parsing.StringParser (Pos)
import Type.Proxy (Proxy(..))

oneOf ::
  forall m a f.
  Foldable f =>
  MonadGen m =>
  NonEmpty f (m a) ->
  m a
oneOf = foldl1 Gen.choose

genBigInteger :: forall m. MonadGen m => MonadRec m => m BigInteger
genBigInteger = BigInteger.fromInt <$> chooseInt bottom top

genRational :: forall m. MonadGen m => MonadRec m => m Rational
genRational = do
  n <- genBigInteger
  d <- genBigInteger
  pure $ Rational n d

genSlot :: forall m. MonadGen m => MonadRec m => m Slot
genSlot = Slot <$> genBigInteger

genTimeout :: forall m. MonadGen m => MonadRec m => m (TermWrapper Slot)
genTimeout = TermWrapper <$> genSlot <*> pure { row: 0, column: 0 }

genValueId :: forall m. MonadGen m => MonadRec m => MonadAsk Boolean m => m ValueId
genValueId = ValueId <$> genString

genAlphaNum :: forall m. MonadGen m => MonadRec m => m Char
genAlphaNum = oneOf $ genAlpha :| [ genDigitChar ]

genString :: forall m. MonadGen m => MonadRec m => m String
genString = fromCharArray <$> resize (_ - 1) (unfoldable genAlphaNum)

genPubKey :: forall m. MonadGen m => MonadRec m => m PubKey
genPubKey = genString

genTokenName :: forall m. MonadGen m => MonadRec m => m TokenName
genTokenName = genString

genParty :: forall m. MonadGen m => MonadRec m => MonadAsk Boolean m => m Party
genParty = oneOf $ pk :| [ role ]
  where
  pk = PK <$> genPubKey

  role = Role <$> genTokenName

genCurrencySymbol :: forall m. MonadGen m => MonadRec m => m CurrencySymbol
genCurrencySymbol = genString

genSlotInterval :: forall m. MonadGen m => MonadRec m => m Slot -> m SlotInterval
genSlotInterval gen = do
  from <- gen
  to <- suchThat gen (\v -> v > from)
  pure $ SlotInterval from to

genBound :: forall m. MonadGen m => MonadRec m => MonadAsk Boolean m => m Bound
genBound = do
  from <- genBigInteger
  to <- suchThat genBigInteger (\v -> v > from)
  pure $ Bound from to

genPosition :: forall m. MonadGen m => MonadRec m => m Pos
genPosition = chooseInt 0 1000

genHole :: forall m a. MonadGen m => MonadRec m => m (Term a)
genHole = do
  name <- suchThat genString (\s -> s /= "")
  proxy <- pure (Proxy :: Proxy a)
  row <- genPosition
  column <- genPosition
  pure $ Hole name proxy { row, column }

genTerm :: forall m a. MonadGen m => MonadRec m => MonadAsk Boolean m => m a -> m (Term a)
genTerm g = do
  withHoles <- ask
  oneOf $ (Term <$> g <*> pure { row: 0, column: 0 }) :| (if withHoles then [ genHole ] else [])

genTermWrapper :: forall m a. MonadGen m => MonadRec m => MonadAsk Boolean m => m a -> m (TermWrapper a)
genTermWrapper g = do
  TermWrapper <$> g <*> pure { row: 0, column: 0 }

genAccountId :: forall m. MonadGen m => MonadRec m => MonadAsk Boolean m => m AccountId
genAccountId = do
  accountNumber <- genBigInteger
  accountOwner <- genTerm genParty
  pure $ AccountId accountNumber accountOwner

genToken :: forall m. MonadGen m => MonadRec m => MonadAsk Boolean m => m Token
genToken = do
  currencySymbol <- genCurrencySymbol
  tokenName <- genTokenName
  pure $ Token currencySymbol tokenName

genChoiceId :: forall m. MonadGen m => MonadRec m => MonadAsk Boolean m => m ChoiceId
genChoiceId = do
  choiceName <- genString
  choiceOwner <- genTerm genParty
  pure $ ChoiceId choiceName choiceOwner

genPayee :: forall m. MonadGen m => MonadRec m => MonadAsk Boolean m => m Payee
genPayee = oneOf $ (Account <$> genTerm genAccountId) :| [ Party <$> genTerm genParty ]

genAction :: forall m. MonadGen m => MonadRec m => Lazy (m Observation) => Lazy (m Value) => MonadAsk Boolean m => Int -> m Action
genAction size =
  oneOf
    $ (Deposit <$> genTerm genAccountId <*> genTerm genParty <*> genTerm genToken <*> genTerm (genValue' size))
    :| [ Choice <$> genTerm genChoiceId <*> resize (_ - 1) (unfoldable (genTerm genBound))
      , Notify <$> genTerm (genObservation' size)
      ]

genCase ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Value) =>
  Lazy (m Observation) =>
  Lazy (m Contract) =>
  MonadAsk Boolean m =>
  Int ->
  m Case
genCase size = do
  let
    newSize = size - 1
  action <- genTerm $ genAction newSize
  contract <- genTerm $ genContract' newSize
  pure (Case action contract)

genCases ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Value) =>
  Lazy (m Observation) =>
  Lazy (m Contract) =>
  MonadAsk Boolean m =>
  Int ->
  m (Array (Term Case))
genCases size = resize (_ - 1) (unfoldable (genTerm (genCase size)))

genValue :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => MonadAsk Boolean m => m Value
genValue = genValue' 5

genValue' ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Value) =>
  MonadAsk Boolean m =>
  Int ->
  m Value
genValue' size
  | size > 1 =
    defer \_ ->
      let
        newSize = (size - 1)

        genNewValue = genTerm $ genValue' newSize
      in
        oneOf $ pure SlotIntervalStart
          :| [ pure SlotIntervalEnd
            , AvailableMoney <$> genTerm genAccountId <*> genTerm genToken
            , Constant <$> genBigInteger
            , NegValue <$> genNewValue
            , AddValue <$> genNewValue <*> genNewValue
            , SubValue <$> genNewValue <*> genNewValue
            , Scale <$> genTerm genRational <*> genNewValue
            , ChoiceValue <$> genTerm genChoiceId <*> genNewValue
            , UseValue <$> genTermWrapper genValueId
            ]
  | otherwise =
    oneOf $ pure SlotIntervalStart
      :| [ pure SlotIntervalEnd
        , AvailableMoney <$> genTerm genAccountId <*> genTerm genToken
        , Constant <$> genBigInteger
        , UseValue <$> genTermWrapper genValueId
        ]

genObservation ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  MonadAsk Boolean m =>
  m Observation
genObservation = genObservation' 5

genObservation' ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  MonadAsk Boolean m =>
  Int ->
  m Observation
genObservation' size
  | size > 1 =
    defer \_ ->
      let
        newSize = (size - 1)

        genNewValue = genTerm $ genValue' newSize

        genNewObservation = genTerm $ genObservation' newSize
      in
        oneOf
          $ (AndObs <$> genNewObservation <*> genNewObservation)
          :| [ OrObs <$> genNewObservation <*> genNewObservation
            , NotObs <$> genNewObservation
            , ChoseSomething <$> genTerm genChoiceId
            , ValueGE <$> genNewValue <*> genNewValue
            , ValueGT <$> genNewValue <*> genNewValue
            , ValueLT <$> genNewValue <*> genNewValue
            , ValueLE <$> genNewValue <*> genNewValue
            , ValueEQ <$> genNewValue <*> genNewValue
            ]
  | otherwise = genLeaf
    where
    genLeaf ::
      m Observation
    genLeaf = ChoseSomething <$> genTerm genChoiceId

genContract ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Contract) =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  MonadAsk Boolean m =>
  m Contract
genContract = genContract' 3

genContract' ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Contract) =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  MonadAsk Boolean m =>
  Int ->
  m Contract
genContract' size
  | size > 1 =
    defer \_ ->
      let
        newSize = (size - 1)

        genNewValue = genTerm $ genValue' newSize

        genNewObservation = genTerm $ genObservation' newSize

        genNewContract = genTerm $ genContract' newSize
      in
        oneOf $ pure Close
          :| [ Pay <$> genTerm genAccountId <*> genTerm genPayee <*> genTerm genToken <*> genNewValue <*> genNewContract
            , If <$> genNewObservation <*> genNewContract <*> genNewContract
            , When <$> genCases newSize <*> genTimeout <*> genNewContract
            , Let <$> genTermWrapper genValueId <*> genNewValue <*> genNewContract
            ]
  | otherwise = genLeaf
    where
    genLeaf ::
      m Contract
    genLeaf = pure Close

----------------------------------------------------------------- Semantics Generators ---------------------------------
genTokenNameValue :: forall m. MonadGen m => MonadRec m => m S.TokenName
genTokenNameValue = genString

genCurrencySymbolValue :: forall m. MonadGen m => MonadRec m => m S.CurrencySymbol
genCurrencySymbolValue = genString

genTokenValue :: forall m. MonadGen m => MonadRec m => m S.Token
genTokenValue = do
  currencySymbol <- genCurrencySymbolValue
  tokenName <- genTokenName
  pure $ S.Token currencySymbol tokenName

genPartyValue :: forall m. MonadGen m => MonadRec m => m S.Party
genPartyValue = oneOf $ pk :| [ role ]
  where
  pk = S.PK <$> genPubKey

  role = S.Role <$> genTokenNameValue

genAccountIdValue :: forall m. MonadGen m => MonadRec m => m S.AccountId
genAccountIdValue = do
  accountNumber <- genBigInteger
  accountOwner <- genPartyValue
  pure $ S.AccountId accountNumber accountOwner

genPayeeValue :: forall m. MonadGen m => MonadRec m => m S.Payee
genPayeeValue = oneOf $ (S.Account <$> genAccountIdValue) :| [ S.Party <$> genPartyValue ]

genValueIdValue :: forall m. MonadGen m => MonadRec m => m S.ValueId
genValueIdValue = S.ValueId <$> genString

genChoiceIdValue :: forall m. MonadGen m => MonadRec m => m S.ChoiceId
genChoiceIdValue = do
  choiceName <- genString
  choiceOwner <- genPartyValue
  pure $ S.ChoiceId choiceName choiceOwner

genInput ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  m S.Input
genInput =
  oneOf
    $ (IDeposit <$> genAccountIdValue <*> genPartyValue <*> genTokenValue <*> genBigInteger)
    :| [ IChoice <$> genChoiceIdValue <*> genBigInteger
      , pure INotify
      ]

genTransactionInput ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  m S.TransactionInput
genTransactionInput = do
  interval <- genSlotInterval genSlot
  inputs <- unfoldable genInput
  pure $ TransactionInput { interval, inputs }

genTransactionWarning ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  m TransactionWarning
genTransactionWarning =
  oneOf
    $ (TransactionNonPositiveDeposit <$> genPartyValue <*> genAccountIdValue <*> genTokenValue <*> genBigInteger)
    :| [ TransactionNonPositivePay <$> genAccountIdValue <*> genPayeeValue <*> genTokenValue <*> genBigInteger
      , TransactionPartialPay <$> genAccountIdValue <*> genPayeeValue <*> genTokenValue <*> genBigInteger <*> genBigInteger
      , TransactionShadowing <$> genValueIdValue <*> genBigInteger <*> genBigInteger
      ]
