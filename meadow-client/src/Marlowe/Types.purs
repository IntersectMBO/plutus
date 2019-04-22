module Marlowe.Types where

import Prelude

import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Newtype (class Newtype)
import Data.String (joinWith)
import Marlowe.Pretty (class Pretty, genericPretty)
import Text.PrettyPrint.Leijen (text)

type BlockNumber
  = BigInteger

type Timeout
  = BlockNumber

type Person
  = BigInteger

type Choice
  = BigInteger

type IdAction
  = BigInteger

type IdCommit
  = BigInteger

newtype IdChoice
  = IdChoice {choice :: BigInteger, person :: Person}

derive instance eqIdChoice :: Eq IdChoice

derive instance ordIdChoice :: Ord IdChoice

derive instance genericIdChoice :: Generic IdChoice _

derive instance newtypeIdChoice :: Newtype IdChoice _

instance showIdChoice :: Show IdChoice where
  show (IdChoice { choice, person }) = joinWith "" [ "("
                                                   , show choice
                                                   , ", "
                                                   , show person
                                                   , ")"
                                                   ]

instance prettyIdChoice :: Pretty IdChoice where
  prettyFragment a = text (show a)

data WIdChoice
  = WIdChoice IdChoice

derive instance eqWIdChoice :: Eq WIdChoice

derive instance ordWIdChoice :: Ord WIdChoice

type IdOracle
  = BigInteger

type LetLabel
  = BigInteger

data Value
  = CurrentBlock
  | Committed IdCommit
  | Constant BigInteger
  | NegValue Value
  | AddValue Value Value
  | SubValue Value Value
  | MulValue Value Value
  | DivValue Value Value Value
  | ModValue Value Value Value
  | ValueFromChoice IdChoice Value
  | ValueFromOracle IdOracle Value

derive instance eqValue :: Eq Value

derive instance ordValue :: Ord Value

derive instance genericValue :: Generic Value _

instance showValue :: Show Value where
  show v = genericShow v

instance prettyValue :: Pretty Value where
  prettyFragment a = genericPretty a

data Observation
  = BelowTimeout Timeout
  | AndObs Observation Observation
  | OrObs Observation Observation
  | NotObs Observation
  | ChoseThis IdChoice Choice
  | ChoseSomething IdChoice
  | ValueGE Value Value
  | ValueGT Value Value
  | ValueLT Value Value
  | ValueLE Value Value
  | ValueEQ Value Value
  | TrueObs
  | FalseObs

derive instance eqObservation :: Eq Observation

derive instance ordObservation :: Ord Observation

derive instance genericObservation :: Generic Observation _

instance showObservation :: Show Observation where
  show o = genericShow o

instance prettyObservation :: Pretty Observation where
  prettyFragment a = genericPretty a

data Contract
  = Null
  | Commit IdAction IdCommit Person Value Timeout Timeout Contract Contract
  | Pay IdAction IdCommit Person Value Timeout Contract Contract
  | Both Contract Contract
  | Choice Observation Contract Contract
  | When Observation Timeout Contract Contract
  | While Observation Timeout Contract Contract
  | Scale Value Value Value Contract
  | Let LetLabel Contract Contract
  | Use LetLabel

derive instance eqContract :: Eq Contract

derive instance ordContract :: Ord Contract

derive instance genericContract :: Generic Contract _

instance showContract :: Show Contract where
  show c = genericShow c

instance prettyContract :: Pretty Contract where
  prettyFragment a = genericPretty a