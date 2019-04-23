module Marlowe.Types where

import Prelude

import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Newtype (class Newtype)
import Data.String (joinWith)
import Marlowe.Pretty (class Pretty, genericPretty)
import Text.PrettyPrint.Leijen (text)
import Matryoshka.Class.Recursive (class Recursive)
import Matryoshka.Class.Corecursive (class Corecursive)

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

---------------------------- Value ----------------------------
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

data ValueF f
  = CurrentBlockF
  | CommittedF IdCommit
  | ConstantF BigInteger
  | NegValueF f
  | AddValueF f f
  | SubValueF f f
  | MulValueF f f
  | DivValueF f f f
  | ModValueF f f f
  | ValueFromChoiceF IdChoice f
  | ValueFromOracleF IdOracle f

derive instance functorValueF :: Functor ValueF
derive instance eqValueF :: Eq f => Eq (ValueF f)

instance recursiveValue :: Recursive Value ValueF where
  project CurrentBlock = CurrentBlockF
  project (Committed i) = CommittedF i
  project (Constant i) = ConstantF i
  project (NegValue v) = NegValueF v
  project (AddValue v1 v2) = AddValueF v1 v2
  project (SubValue v1 v2) = SubValueF v1 v2
  project (MulValue v1 v2) = MulValueF v1 v2
  project (DivValue v1 v2 v3) = DivValueF v1 v2 v3
  project (ModValue v1 v2 v3) = ModValueF v1 v2 v3
  project (ValueFromChoice i v) = ValueFromChoiceF i v
  project (ValueFromOracle i v) = ValueFromOracleF i v

instance corecursiveValue :: Corecursive Value ValueF where
  embed CurrentBlockF = CurrentBlock
  embed (CommittedF i) = Committed i
  embed (ConstantF i) = Constant i
  embed (NegValueF v) = NegValue v
  embed (AddValueF v1 v2) = AddValue v1 v2
  embed (SubValueF v1 v2) = SubValue v1 v2
  embed (MulValueF v1 v2) = MulValue v1 v2
  embed (DivValueF v1 v2 v3) = DivValue v1 v2 v3
  embed (ModValueF v1 v2 v3) = ModValue v1 v2 v3
  embed (ValueFromChoiceF i v) = ValueFromChoice i v
  embed (ValueFromOracleF i v) = ValueFromOracle i v
---------------------------- Observation ----------------------------
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

data ObservationF f
  = BelowTimeoutF Timeout
  | AndObsF f f
  | OrObsF f f
  | NotObsF f
  | ChoseThisF IdChoice Choice
  | ChoseSomethingF IdChoice
  | ValueGEF Value Value
  | ValueGTF Value Value
  | ValueLTF Value Value
  | ValueLEF Value Value
  | ValueEQF Value Value
  | TrueObsF
  | FalseObsF

derive instance functorObservationF :: Functor ObservationF
derive instance eqObservationF :: Eq f => Eq (ObservationF f)

instance recursiveObservation :: Recursive Observation ObservationF where
  project (BelowTimeout t) = BelowTimeoutF t
  project (AndObs o1 o2) = AndObsF o1 o2
  project (OrObs o1 o2) = OrObsF o1 o2
  project (NotObs o) = NotObsF o
  project (ChoseThis i c) = ChoseThisF i c
  project (ChoseSomething i) = ChoseSomethingF i
  project (ValueGE v1 v2) = ValueGEF v1 v2
  project (ValueGT v1 v2) = ValueGTF v1 v2
  project (ValueLT v1 v2) = ValueLTF v1 v2
  project (ValueLE v1 v2) = ValueLEF v1 v2
  project (ValueEQ v1 v2) = ValueEQF v1 v2
  project TrueObs = TrueObsF
  project FalseObs = FalseObsF

instance corecursiveObservation :: Corecursive Observation ObservationF where
  embed (BelowTimeoutF t) = BelowTimeout t
  embed (AndObsF o1 o2) = AndObs o1 o2
  embed (OrObsF o1 o2) = OrObs o1 o2
  embed (NotObsF o) = NotObs o
  embed (ChoseThisF i c) = ChoseThis i c
  embed (ChoseSomethingF i) = ChoseSomething i
  embed (ValueGEF v1 v2) = ValueGE v1 v2
  embed (ValueGTF v1 v2) = ValueGT v1 v2
  embed (ValueLTF v1 v2) = ValueLT v1 v2
  embed (ValueLEF v1 v2) = ValueLE v1 v2
  embed (ValueEQF v1 v2) = ValueEQ v1 v2
  embed TrueObsF = TrueObs
  embed FalseObsF = FalseObs

---------------------------- Contract ----------------------------
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

data ContractF f
  = NullF
  | CommitF IdAction IdCommit Person Value Timeout Timeout f f
  | PayF IdAction IdCommit Person Value Timeout f f
  | BothF f f
  | ChoiceF Observation f f
  | WhenF Observation Timeout f f
  | WhileF Observation Timeout f f
  | ScaleF Value Value Value f
  | LetF LetLabel f f
  | UseF LetLabel

derive instance functorContractF :: Functor ContractF
derive instance eqContractF :: Eq f => Eq (ContractF f)

instance recursiveContract :: Recursive Contract ContractF where
  project Null = NullF
  project (Commit ia ic p v t1 t2 c1 c2) = CommitF ia ic p v t1 t2 c1 c2
  project (Pay ia ic p v t c1 c2) = PayF ia ic p v t c1 c2
  project (Both c1 c2) = BothF c1 c2
  project (Choice o c1 c2) = ChoiceF o c1 c2
  project (When o t c1 c2) = WhenF o t c1 c2
  project (While o t c1 c2) = WhileF o t c1 c2
  project (Scale v1 v2 v3 c) = ScaleF v1 v2 v3 c
  project (Let l c1 c2) = LetF l c1 c2
  project (Use l) = UseF l

instance corecursiveContract :: Corecursive Contract ContractF where
  embed NullF = Null
  embed (CommitF ia ic p v t1 t2 c1 c2) = Commit ia ic p v t1 t2 c1 c2
  embed (PayF ia ic p v t c1 c2) = Pay ia ic p v t c1 c2
  embed (BothF c1 c2) = Both c1 c2
  embed (ChoiceF o c1 c2) = Choice o c1 c2
  embed (WhenF o t c1 c2) = When o t c1 c2
  embed (WhileF o t c1 c2) = While o t c1 c2
  embed (ScaleF v1 v2 v3 c) = Scale v1 v2 v3 c
  embed (LetF l c1 c2) = Let l c1 c2
  embed (UseF l) = Use l