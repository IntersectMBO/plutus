module Marlowe.Gen where

import Prelude

import Control.Lazy (class Lazy, defer)
import Control.Monad.Gen (class MonadGen, chooseInt)
import Control.Monad.Gen as Gen
import Control.Monad.Rec.Class (class MonadRec)
import Data.BigInt (BigInt)
import Data.BigInt as BigInt
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Foldable (class Foldable)
import Data.Newtype (wrap)
import Data.NonEmpty (NonEmpty, foldl1, (:|))
import Marlowe.Types (BlockNumber(BlockNumber), Contract(..), IdAction(..), IdChoice, IdCommit(..), IdOracle(IdOracle), Observation(..), Person(Person), Timeout(Timeout), Value(..))

oneOf ::
  forall m a f.
  Foldable f =>
  MonadGen m =>
  NonEmpty f (m a) ->
  m a
oneOf = foldl1 Gen.choose

genBigInteger :: forall m. MonadGen m => MonadRec m => m BigInteger
genBigInteger = BigInteger.fromInt <$> chooseInt bottom top

genBigInt :: forall m. MonadGen m => MonadRec m => m BigInt
genBigInt = BigInt.fromInt <$> chooseInt bottom top

genBlockNumber :: forall m. MonadGen m => MonadRec m => m BlockNumber
genBlockNumber = BlockNumber <$> genBigInt

genTimeout :: forall m. MonadGen m => MonadRec m => m Timeout
genTimeout = (Timeout <<< BlockNumber) <$> genBigInt

genPerson :: forall m. MonadGen m => MonadRec m => m Person
genPerson = Person <$> genBigInt

genIdAction :: forall m. MonadGen m => MonadRec m => m IdAction
genIdAction = IdAction <$> genBigInteger

genIdCommit :: forall m. MonadGen m => MonadRec m => m IdCommit
genIdCommit = IdCommit <$> genBigInteger

genIdOracle :: forall m. MonadGen m => MonadRec m => m IdOracle
genIdOracle = IdOracle <$> genBigInteger

genIdChoice :: forall m. MonadGen m => MonadRec m => m IdChoice
genIdChoice = do
  choice <- genBigInteger
  person <- genPerson
  pure $ wrap { choice, person }

genValue :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => m Value
genValue = genValue' 5

genValue' ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Value) =>
  Int ->
  m Value
genValue' size
  | size > 1 = defer \_ ->
    let newSize = (size - 1)
    in oneOf $ pure CurrentBlock :| [ Committed <$> genIdCommit
                                    , Constant <$> genBigInteger
                                    , NegValue <$> genValue' newSize
                                    , AddValue <$> genValue' newSize <*> genValue' newSize
                                    , SubValue <$> genValue' newSize <*> genValue' newSize
                                    , MulValue <$> genValue' newSize <*> genValue' newSize
                                    , DivValue <$> genValue' newSize <*> genValue' newSize <*> genValue' newSize
                                    , ModValue <$> genValue' newSize <*> genValue' newSize <*> genValue' newSize
                                    , ValueFromChoice <$> genIdChoice <*> genValue' newSize
                                    , ValueFromOracle <$> genIdOracle <*> genValue' newSize
                                    ]
  | otherwise = oneOf $ pure CurrentBlock :| [ Committed <$> genIdCommit
                                             , Constant <$> genBigInteger
                                             ]

genObservation ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  m Observation
genObservation = genObservation' 5

genObservation' ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  Int ->
  m Observation
genObservation' size
  | size > 1 = defer \_ ->
    let newSize = (size - 1)
    in oneOf $ pure TrueObs :| [ pure FalseObs
                               , BelowTimeout <$> genTimeout
                               , ChoseThis <$> genIdChoice <*> genBigInteger
                               , ChoseSomething <$> genIdChoice
                               , AndObs <$> genObservation' newSize <*> genObservation' newSize
                               , OrObs <$> genObservation' newSize <*> genObservation' newSize
                               , NotObs <$> genObservation' newSize
                               , ValueGE <$> genValue' newSize <*> genValue' newSize
                               , ValueGT <$> genValue' newSize <*> genValue' newSize
                               , ValueLT <$> genValue' newSize <*> genValue' newSize
                               , ValueLE <$> genValue' newSize <*> genValue' newSize
                               , ValueEQ <$> genValue' newSize <*> genValue' newSize
                               ]
  | otherwise = genLeaf
    where
    genLeaf ::
      m Observation
    genLeaf = oneOf $ pure TrueObs :| [ pure FalseObs
                                      , BelowTimeout <$> genTimeout
                                      , ChoseThis <$> genIdChoice <*> genBigInteger
                                      , ChoseSomething <$> genIdChoice
                                      ]

genContract ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Contract) =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  m Contract
genContract = genContract' 3

genContract' ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Contract) =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  Int ->
  m Contract
genContract' size
  | size > 1 = defer \_ ->
    let newSize = (size - 1)
    in oneOf $ pure Null :| [ Use <$> genBigInteger
                            , Commit <$> genIdAction <*> genIdCommit <*> genPerson <*> genValue' newSize <*> genTimeout <*> genTimeout <*> genContract' newSize <*> genContract' newSize
                            , Pay <$> genIdAction <*> genIdCommit <*> genPerson <*> genValue' newSize <*> genTimeout <*> genContract' newSize <*> genContract' newSize
                            , Both <$> genContract' newSize <*> genContract' newSize
                            , Choice <$> genObservation <*> genContract' newSize <*> genContract' newSize
                            , When <$> genObservation <*> genTimeout <*> genContract' newSize <*> genContract' newSize
                            , While <$> genObservation <*> genTimeout <*> genContract' newSize <*> genContract' newSize
                            , Scale <$> genValue' newSize <*> genValue' newSize <*> genValue' newSize <*> genContract' newSize
                            , Let <$> genBigInteger <*> genContract' newSize <*> genContract' newSize
                            ]
  | otherwise = genLeaf
    where
    genLeaf ::
      m Contract
    genLeaf = oneOf $ pure Null :| [ Use <$> genBigInteger ]
