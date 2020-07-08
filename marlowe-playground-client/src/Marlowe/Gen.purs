module Marlowe.Gen where

import Prelude
import Control.Lazy (class Lazy, defer)
import Control.Monad.Gen (class MonadGen, chooseInt, resize, suchThat, unfoldable)
import Control.Monad.Gen as Gen
import Control.Monad.Reader (class MonadReader, ask, local)
import Control.Monad.Rec.Class (class MonadRec)
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Char.Gen (genAlpha, genDigitChar)
import Data.Foldable (class Foldable)
import Data.NonEmpty (NonEmpty, foldl1, (:|))
import Data.String.CodeUnits (fromCharArray)
import Marlowe.Holes (AccountId(..), Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), MarloweType(..), Observation(..), Party(..), Payee(..), Term(..), TermWrapper(..), Token(..), Value(..), ValueId(..), mkArgName)
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
  pure
    -- we need to do this because in tests where we wrap a Rational in a Term or TermWrapper
    
    -- when we have two negative values then the column position of the term will different
    
    -- to if we have two positive values, even though the rationals themselves are equal
    
    $ if d > zero then
        Rational n d
      else
        Rational (-n) (-d)

genSlot :: forall m. MonadGen m => MonadRec m => m Slot
genSlot = Slot <$> genBigInteger

genTimeout :: forall m. MonadGen m => MonadRec m => m (TermWrapper Slot)
genTimeout = TermWrapper <$> genSlot <*> pure { row: 0, column: 0 }

genValueId :: forall m. MonadGen m => MonadRec m => MonadReader Boolean m => m ValueId
genValueId = ValueId <$> genString

genAlphaNum :: forall m. MonadGen m => MonadRec m => m Char
genAlphaNum = oneOf $ genAlpha :| [ genDigitChar ]

genString :: forall m. MonadGen m => MonadRec m => m String
genString = fromCharArray <$> resize (_ - 1) (unfoldable genAlphaNum)

genPubKey :: forall m. MonadGen m => MonadRec m => m PubKey
genPubKey = genString

genTokenName :: forall m. MonadGen m => MonadRec m => m TokenName
genTokenName = genString

genParty :: forall m. MonadGen m => MonadRec m => MonadReader Boolean m => m Party
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

genBound :: forall m. MonadGen m => MonadRec m => MonadReader Boolean m => m Bound
genBound = do
  from <- genBigInteger
  to <- suchThat genBigInteger (\v -> v > from)
  pure $ Bound from to

genPosition :: forall m. MonadGen m => MonadRec m => m Pos
genPosition = chooseInt 0 1000

genHole :: forall m a. MonadGen m => MonadRec m => String -> m (Term a)
genHole name = do
  -- name <- suchThat genString (\s -> s /= "")
  proxy <- pure (Proxy :: Proxy a)
  row <- genPosition
  column <- genPosition
  pure $ Hole name proxy { row, column }

genTerm :: forall m a. MonadGen m => MonadRec m => MonadReader Boolean m => String -> m a -> m (Term a)
genTerm name g = do
  withHoles <- ask
  oneOf $ (Term <$> g <*> pure { row: 0, column: 0 }) :| (if withHoles then [ genHole name ] else [])

genTermWrapper :: forall m a. MonadGen m => MonadRec m => MonadReader Boolean m => m a -> m (TermWrapper a)
genTermWrapper g = do
  TermWrapper <$> g <*> pure { row: 0, column: 0 }

genAccountId :: forall m. MonadGen m => MonadRec m => MonadReader Boolean m => m AccountId
genAccountId = do
  accountNumber <- genBigInteger
  accountOwner <- genTerm (mkArgName PartyType) genParty
  pure $ AccountId accountNumber accountOwner

genToken :: forall m. MonadGen m => MonadRec m => MonadReader Boolean m => m Token
genToken = oneOf $ (pure $ Token "" "") :| [ Token <$> genCurrencySymbol <*> genTokenName ]

genChoiceId :: forall m. MonadGen m => MonadRec m => MonadReader Boolean m => m ChoiceId
genChoiceId = do
  choiceName <- genString
  choiceOwner <- genTerm (mkArgName PartyType) genParty
  pure $ ChoiceId choiceName choiceOwner

genPayee :: forall m. MonadGen m => MonadRec m => MonadReader Boolean m => m Payee
genPayee = oneOf $ (Account <$> genAccountId) :| [ Party <$> genTerm (mkArgName PartyType) genParty ]

genAction :: forall m. MonadGen m => MonadRec m => Lazy (m Observation) => Lazy (m Value) => MonadReader Boolean m => Int -> m Action
genAction size =
  oneOf
    $ (Deposit <$> genAccountId <*> genTerm "from_party" genParty <*> genTerm (mkArgName TokenType) genToken <*> genTerm (mkArgName ValueType) (genValue' size))
    :| [ Choice <$> genChoiceId <*> resize (_ - 1) (unfoldable (genTerm (mkArgName BoundType) genBound))
      , Notify <$> genTerm (mkArgName ObservationType) (genObservation' size)
      ]

genCase ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Value) =>
  Lazy (m Observation) =>
  Lazy (m Contract) =>
  MonadReader Boolean m =>
  Int ->
  m Case
genCase size = do
  let
    newSize = size - 1
  action <- genTerm (mkArgName ActionType) $ genAction newSize
  contract <- genTerm (mkArgName ContractType) $ genContract' newSize
  pure (Case action contract)

genCases ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Value) =>
  Lazy (m Observation) =>
  Lazy (m Contract) =>
  MonadReader Boolean m =>
  Int ->
  m (Array (Term Case))
genCases size = resize (_ - 1) (unfoldable (local (const false) (genTerm "case" (genCase size))))

genValue :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => MonadReader Boolean m => m Value
genValue = genValue' 5

genValue' ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Value) =>
  MonadReader Boolean m =>
  Int ->
  m Value
genValue' size
  | size > 1 =
    defer \_ ->
      let
        newSize = (size - 1)

        genNewValue = genTerm (mkArgName ValueType) $ genValue' newSize

        genNewValueIndexed i = genTerm ((mkArgName ValueType) <> show i) $ genValue' newSize
      in
        oneOf $ pure SlotIntervalStart
          :| [ pure SlotIntervalEnd
            , AvailableMoney <$> genAccountId <*> genTerm (mkArgName TokenType) genToken
            , Constant <$> genBigInteger
            , NegValue <$> genNewValue
            , AddValue <$> genNewValueIndexed 1 <*> genNewValueIndexed 2
            , SubValue <$> genNewValueIndexed 1 <*> genNewValueIndexed 2
            , MulValue <$> genNewValueIndexed 1 <*> genNewValueIndexed 2
            , Scale <$> genTermWrapper genRational <*> genNewValue
            , ChoiceValue <$> genChoiceId
            , UseValue <$> genTermWrapper genValueId
            ]
  | otherwise =
    oneOf $ pure SlotIntervalStart
      :| [ pure SlotIntervalEnd
        , AvailableMoney <$> genAccountId <*> genTerm (mkArgName TokenType) genToken
        , Constant <$> genBigInteger
        , UseValue <$> genTermWrapper genValueId
        ]

genObservation ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  MonadReader Boolean m =>
  m Observation
genObservation = genObservation' 5

genObservation' ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  MonadReader Boolean m =>
  Int ->
  m Observation
genObservation' size
  | size > 1 =
    defer \_ ->
      let
        newSize = (size - 1)

        genNewValue i = genTerm ((mkArgName ValueType) <> show i) $ genValue' newSize

        genNewObservationIndexed i = genTerm ((mkArgName ObservationType) <> show i) $ genObservation' newSize

        genNewObservation = genTerm (mkArgName ObservationType) $ genObservation' newSize
      in
        oneOf
          $ (AndObs <$> genNewObservationIndexed 1 <*> genNewObservationIndexed 2)
          :| [ OrObs <$> genNewObservationIndexed 1 <*> genNewObservationIndexed 2
            , NotObs <$> genNewObservation
            , ChoseSomething <$> genChoiceId
            , ValueGE <$> genNewValue 1 <*> genNewValue 2
            , ValueGT <$> genNewValue 1 <*> genNewValue 2
            , ValueLT <$> genNewValue 1 <*> genNewValue 2
            , ValueLE <$> genNewValue 1 <*> genNewValue 2
            , ValueEQ <$> genNewValue 1 <*> genNewValue 2
            ]
  | otherwise = genLeaf
    where
    genLeaf ::
      m Observation
    genLeaf = ChoseSomething <$> genChoiceId

genContract ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Contract) =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  MonadReader Boolean m =>
  m Contract
genContract = genContract' 3

genContract' ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Contract) =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  MonadReader Boolean m =>
  Int ->
  m Contract
genContract' size
  | size > 1 =
    defer \_ ->
      let
        newSize = (size - 1)

        genNewValue = genTerm (mkArgName ValueType) $ genValue' newSize

        genNewObservation = genTerm (mkArgName ObservationType) $ genObservation' newSize

        genNewContractIndexed i = genTerm ((mkArgName ContractType) <> show i) $ genContract' newSize

        genNewContract = genTerm (mkArgName ContractType) $ genContract' newSize
      in
        oneOf $ pure Close
          :| [ Pay <$> genAccountId <*> genTerm (mkArgName PayeeType) genPayee <*> genTerm (mkArgName TokenType) genToken <*> genNewValue <*> genNewContract
            , If <$> genNewObservation <*> genNewContractIndexed 1 <*> genNewContractIndexed 2
            , When <$> genCases newSize <*> genTimeout <*> genNewContract
            , Let <$> genTermWrapper genValueId <*> genNewValue <*> genNewContract
            , Assert <$> genNewObservation <*> genNewContract
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
