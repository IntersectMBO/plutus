module Marlowe.Gen where

import Prelude

import Control.Lazy (class Lazy, defer)
import Control.Monad.Gen (class MonadGen, chooseInt)
import Control.Monad.Rec.Class (class MonadRec)
import Data.BigInteger (BigInteger)
import Data.Newtype (wrap)
import Data.NonEmpty ((:|))
import Semantics (Contract(..), IdChoice, Observation(..), Value(..))

import Control.Monad.Gen as Gen
import Data.BigInteger as BigInteger

genBigInteger :: forall m. MonadGen m => MonadRec m => m BigInteger
genBigInteger = BigInteger.fromInt <$> chooseInt bottom top

genIdChoice :: forall m. MonadGen m => MonadRec m => m IdChoice
genIdChoice = do
  choice <- genBigInteger
  person <- genBigInteger
  pure $ wrap { choice, person }

lazyGenValue :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => m Value
lazyGenValue = defer \_ ->
  genValue

genValue :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => m Value
genValue = Gen.resize (min 5) $ Gen.sized genValue'
  where
  genValue' ::
    Int ->
    m Value
  genValue' size
    | size > 1 = Gen.resize (_ - 1) $ Gen.oneOf $ genLeaf :| [ NegValue <$> lazyGenValue
                                                             , AddValue <$> lazyGenValue <*> lazyGenValue
                                                             , SubValue <$> lazyGenValue <*> lazyGenValue
                                                             , MulValue <$> lazyGenValue <*> lazyGenValue
                                                             , DivValue <$> lazyGenValue <*> lazyGenValue <*> lazyGenValue
                                                             , ModValue <$> lazyGenValue <*> lazyGenValue <*> lazyGenValue
                                                             , ValueFromChoice <$> genIdChoice <*> lazyGenValue
                                                             , ValueFromOracle <$> genBigInteger <*> lazyGenValue
                                                             ]
    | otherwise = genLeaf
  genLeaf ::
    m Value
  genLeaf = Gen.oneOf $ pure CurrentBlock :| [ Committed <$> genBigInteger
                                             , Constant <$> genBigInteger
                                             ]

lazyGenObservation ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  m Observation
lazyGenObservation = defer \_ ->
  genObservation

genObservation ::
  forall m.
  MonadGen m =>
  MonadRec m =>
  Lazy (m Observation) =>
  Lazy (m Value) =>
  m Observation
genObservation = Gen.resize (min 5) $ Gen.sized genObservation'
  where
  genObservation' ::
    Int ->
    m Observation
  genObservation' size
    | size > 1 = Gen.resize (_ - 1) $ Gen.oneOf $ genLeaf :| [ AndObs <$> lazyGenObservation <*> lazyGenObservation
                                                             , OrObs <$> lazyGenObservation <*> lazyGenObservation
                                                             , NotObs <$> lazyGenObservation
                                                             , ValueGE <$> lazyGenValue <*> lazyGenValue
                                                             , ValueGT <$> lazyGenValue <*> lazyGenValue
                                                             , ValueLT <$> lazyGenValue <*> lazyGenValue
                                                             , ValueLE <$> lazyGenValue <*> lazyGenValue
                                                             , ValueEQ <$> lazyGenValue <*> lazyGenValue
                                                             ]
    | otherwise = genLeaf
  genLeaf ::
    m Observation
  genLeaf = Gen.oneOf $ pure TrueObs :| [ pure FalseObs
                                        , BelowTimeout <$> genBigInteger
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
genContract = Gen.resize (min 5) $ Gen.sized genContract'
  where
  genContract' ::
    Int ->
    m Contract
  genContract' size
    | size > 1 = Gen.resize (_ - 1) $ Gen.oneOf $ genLeaf :| [ Commit <$> genBigInteger <*> genBigInteger <*> genBigInteger <*> genValue <*> genBigInteger <*> genBigInteger <*> lazyGenContract <*> lazyGenContract
                                                             , Pay <$> genBigInteger <*> genBigInteger <*> genBigInteger <*> genValue <*> genBigInteger <*> lazyGenContract <*> lazyGenContract
                                                             , Both <$> lazyGenContract <*> lazyGenContract
                                                             , Choice <$> genObservation <*> lazyGenContract <*> lazyGenContract
                                                             , When <$> genObservation <*> genBigInteger <*> lazyGenContract <*> lazyGenContract
                                                             , While <$> genObservation <*> genBigInteger <*> lazyGenContract <*> lazyGenContract
                                                             , Scale <$> genValue <*> genValue <*> genValue <*> lazyGenContract
                                                             , Let <$> genBigInteger <*> lazyGenContract <*> lazyGenContract
                                                             ]
    | otherwise = genLeaf
  genLeaf ::
    m Contract
  genLeaf = Gen.oneOf $ pure Null :| [ Use <$> genBigInteger
                                     ]
  lazyGenContract ::
    m Contract
  lazyGenContract = defer \_ ->
    genContract
