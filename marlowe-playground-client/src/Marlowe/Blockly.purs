module Marlowe.Blockly where

import Prelude
import Blockly (AlignDirection(..), Arg(..), BlockDefinition(..), block, blockType, category, colour, defaultBlockDefinition, getBlockById, initializeWorkspace, name, render, style, x, xml, y)
import Blockly.Generator (NewBlockFunction, Generator, Input, clearWorkspace, connectToOutput, connectToPrevious, fieldName, fieldRow, getFieldValue, getInputWithName, inputList, inputName, insertGeneratorFunction, mkGenerator, setFieldText, statementToCode)
import Blockly.Types (Block, BlocklyState, Workspace)
import Control.Alternative ((<|>))
import Control.Monad.ST as ST
import Control.Monad.ST.Internal (ST, STRef)
import Control.Monad.ST.Ref as STRef
import Data.Array as Array
import Data.Bifunctor (lmap, rmap)
import Data.Either (Either)
import Data.Enum (class BoundedEnum, class Enum, upFromIncluding)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Bounded (genericBottom, genericTop)
import Data.Generic.Rep.Enum (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Generic.Rep.Show (genericShow)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Traversable (traverse_)
import Halogen.HTML (HTML)
import Halogen.HTML.Properties (id_)
import Marlowe.Parser as Parser
import Marlowe.Types (Contract(..), IdChoice(..), Observation(..), Value(..))
import Record (merge)
import Text.Parsing.Parser (Parser, runParser)
import Text.Parsing.Parser.Basic (parens)

data ContractType
  = NullContractType
  | CommitContractType
  | PayContractType
  | BothContractType
  | ChoiceContractType
  | WhenContractType
  | WhileContractType
  | ScaleContractType
  | LetContractType
  | UseContractType

derive instance genericContractType :: Generic ContractType _

instance showContractType :: Show ContractType where
  show = genericShow

instance eqContractType :: Eq ContractType where
  eq = genericEq

instance ordContractType :: Ord ContractType where
  compare = genericCompare

instance enumContractType :: Enum ContractType where
  succ = genericSucc
  pred = genericPred

instance boundedContractType :: Bounded ContractType where
  bottom = genericBottom
  top = genericTop

instance boundedEnumContractType :: BoundedEnum ContractType where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

contractTypes :: Array ContractType
contractTypes = upFromIncluding bottom

data ObservationType
  = BelowTimeoutObservationType
  | AndObservationType
  | OrObservationType
  | NotObservationType
  | ChoseThisObservationType
  | ChoseObservationType
  | ValueGEObservationType
  | ValueGObservationType
  | ValueLEObservationType
  | ValueLObservationType
  | ValueEqObservationType
  | TrueObservationType
  | FalseObservationType

derive instance genericObservationType :: Generic ObservationType _

instance showObservationType :: Show ObservationType where
  show = genericShow

instance eqObservationType :: Eq ObservationType where
  eq = genericEq

instance ordObservationType :: Ord ObservationType where
  compare = genericCompare

instance enumObservationType :: Enum ObservationType where
  succ = genericSucc
  pred = genericPred

instance boundedObservationType :: Bounded ObservationType where
  bottom = genericBottom
  top = genericTop

instance boundedEnumObservationType :: BoundedEnum ObservationType where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

observationTypes :: Array ObservationType
observationTypes = upFromIncluding bottom

data ValueType
  = CurrentBlockType
  | CommittedValueType
  | ConstValueType
  | NegValueType
  | AddValueType
  | SubValueType
  | MulValueType
  | DivValueType
  | ModValueType
  | FromChoiceValueType
  | FromOracleValueType

derive instance genericValueType :: Generic ValueType _

instance showValueType :: Show ValueType where
  show = genericShow

instance eqValueType :: Eq ValueType where
  eq = genericEq

instance ordValueType :: Ord ValueType where
  compare = genericCompare

instance enumValueType :: Enum ValueType where
  succ = genericSucc
  pred = genericPred

instance boundedValueType :: Bounded ValueType where
  bottom = genericBottom
  top = genericTop

instance boundedEnumValueType :: BoundedEnum ValueType where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

valueTypes :: Array ValueType
valueTypes = upFromIncluding bottom

data BlockType
  = BaseContractType
  | ContractType ContractType
  | ObservationType ObservationType
  | ValueType ValueType

derive instance genericBlockType :: Generic BlockType _

instance eqBlockType :: Eq BlockType where
  eq = genericEq

instance ordBlockType :: Ord BlockType where
  compare = genericCompare

instance enumBlockType :: Enum BlockType where
  succ = genericSucc
  pred = genericPred

instance boundedBlockType :: Bounded BlockType where
  bottom = genericBottom
  top = genericTop

instance boundedEnumBlockType :: BoundedEnum BlockType where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

instance showBlockType :: Show BlockType where
  show BaseContractType = "BaseContractType"
  show (ContractType c) = show c
  show (ObservationType ot) = show ot
  show (ValueType vt) = show vt

blockDefinitions :: Array BlockDefinition
blockDefinitions = map toDefinition (upFromIncluding bottom)

toDefinition :: BlockType -> BlockDefinition
toDefinition BaseContractType =
  BlockDefinition
    $ merge
        { type: show BaseContractType
        , message0: "%1 CONTRACT %2 %3"
        , args0:
          [ DummyRight
          , Statement {name: (show BaseContractType), check: (show BaseContractType), align: Right}
          , DummyRight
          ]
        , colour: "0"
        , inputsInline: Just false
        } defaultBlockDefinition

toDefinition (ContractType NullContractType) =
  BlockDefinition
    $ merge
        { type: show NullContractType
        , message0: "Null"
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        } defaultBlockDefinition

toDefinition (ContractType CommitContractType) =
  BlockDefinition
    $ merge
        { type: show CommitContractType
        , message0: "Commit %1 with action id %2 %3 and commit id %4 %5 person with id %6 %7 may deposit %8 redeemable on block %9 %10 or after, if money is committed before block %11 %12 continue as %13 otherwise continue as %14"
        , args0:
          [ DummyCentre
          , Number {name: "action_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , DummyRight
          , Number {name: "commit_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , DummyRight
          , Number {name: "person_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , DummyRight
          , Value {name: "ammount", check: "value", align: Right}
          , Number {name: "end_expiration", value: 0.0, min: Just 0.0, max: Nothing, precision: Nothing}
          , DummyRight
          , Number {name: "start_expiration", value: 0.0, min: Just 0.0, max: Nothing, precision: Nothing}
          , DummyRight
          , Statement {name: "contract1", check: (show BaseContractType), align: Right}
          , Statement {name: "contract2", check: (show BaseContractType), align: Right}
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        } defaultBlockDefinition

toDefinition (ContractType PayContractType) =
  BlockDefinition
    $ merge
        { type: show PayContractType
        , message0: "Pay %1 with id %2 %3 use money from commit %4 %5 to pay person %6 %7 the amount of %8 if claimed before block %9 continue as %10 else continue as %11"
        , args0:
          [ DummyCentre
          , Number {name: "action_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , DummyRight
          , Number {name: "commit_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , DummyRight
          , Number {name: "payee_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , DummyRight
          , Value {name: "ammount", check: "value", align: Right}
          , Number {name: "timeout", value: 0.0, min: Just 0.0, max: Nothing, precision: Nothing}
          , Statement {name: "contract1", check: (show BaseContractType), align: Right}
          , Statement {name: "contract2", check: (show BaseContractType), align: Right}
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        } defaultBlockDefinition

toDefinition (ContractType BothContractType) =
  BlockDefinition
    $ merge
        { type: show BothContractType
        , message0: "Both %1 enforce both %2 and %3"
        , args0:
          [ DummyCentre
          , Statement {name: "contract1", check: (show BaseContractType), align: Right}
          , Statement {name: "contract2", check: (show BaseContractType), align: Right}
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        } defaultBlockDefinition

toDefinition (ContractType ChoiceContractType) =
  BlockDefinition
    $ merge
        { type: show ChoiceContractType
        , message0: "Choice %1 if observation %2 then continue as %3 otherwise continue as %4"
        , args0:
          [ DummyCentre
          , Value {name: "observation", check: "observation", align: Right}
          , Statement {name: "contract1", check: (show BaseContractType), align: Right}
          , Statement {name: "contract2", check: (show BaseContractType), align: Right}
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        } defaultBlockDefinition

toDefinition (ContractType WhenContractType) =
  BlockDefinition
    $ merge
        { type: show WhenContractType
        , message0: "When observation %1 continue as %2 if block is %3 or higher continue as %4"
        , args0:
          [ Value {name: "observation", check: "observation", align: Right}
          , Statement {name: "contract1", check: (show BaseContractType), align: Right}
          , Number {name: "timeout", value: 0.0, min: Just 0.0, max: Nothing, precision: Nothing}
          , Statement {name: "contract2", check: (show BaseContractType), align: Right}
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        } defaultBlockDefinition

toDefinition (ContractType WhileContractType) =
  BlockDefinition
    $ merge
        { type: show WhileContractType
        , message0: "While observation %1 enforce %2 when block is %3 or higher continue as %4"
        , args0:
          [ Value {name: "observation", check: "observation", align: Right}
          , Statement {name: "contract1", check: (show BaseContractType), align: Right}
          , Number {name: "timeout", value: 0.0, min: Just 0.0, max: Nothing, precision: Nothing}
          , Statement {name: "contract2", check: (show BaseContractType), align: Right}
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        } defaultBlockDefinition

toDefinition (ContractType ScaleContractType) =
  BlockDefinition
    $ merge
        { type: show ScaleContractType
        , message0: "Scale %1 %2 %3 with %4"
        , args0:
          [ Value {name: "scale1", check: "value", align: Right}
          , Value {name: "scale2", check: "value", align: Right}
          , Value {name: "scale3", check: "value", align: Right}
          , Statement {name: "contract", check: (show BaseContractType), align: Right}
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        } defaultBlockDefinition

toDefinition (ContractType LetContractType) =
  BlockDefinition
    $ merge
        { type: show LetContractType
        , message0: "Let %1 be %2 continue as %3"
        , args0:
          [ Number {name: "let_label", value: 0.0, min: Just 0.0, max: Nothing, precision: Nothing}
          , Statement {name: "contract1", check: (show BaseContractType), align: Right}
          , Statement {name: "contract2", check: (show BaseContractType), align: Right}
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        } defaultBlockDefinition

toDefinition (ContractType UseContractType) =
  BlockDefinition
    $ merge
        { type: show UseContractType
        , message0: "Use %1"
        , args0:
          [ Number {name: "let_label", value: 0.0, min: Just 0.0, max: Nothing, precision: Nothing}
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        } defaultBlockDefinition

toDefinition (ObservationType BelowTimeoutObservationType) =
  BlockDefinition
    $ merge
        { type: show BelowTimeoutObservationType
        , message0: "Below Timeout %1"
        , args0:
          [ Number {name: "timeout", value: 0.0, min: Just 0.0, max: Nothing, precision: Nothing}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType AndObservationType) =
  BlockDefinition
    $ merge
        { type: show AndObservationType
        , message0: "%1 and %2"
        , args0:
          [ Value {name: "observation1", check: "observation", align: Right}
          , Value {name: "observation2", check: "observation", align: Right}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType OrObservationType) =
  BlockDefinition
    $ merge
        { type: show OrObservationType
        , message0: "%1 or %2"
        , args0:
          [ Value {name: "observation1", check: "observation", align: Right}
          , Value {name: "observation2", check: "observation", align: Right}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType NotObservationType) =
  BlockDefinition
    $ merge
        { type: show NotObservationType
        , message0: "Not %1"
        , args0:
          [ Value {name: "observation", check: "observation", align: Right}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType ChoseThisObservationType) =
  BlockDefinition
    $ merge
        { type: show ChoseThisObservationType
        , message0: "chose id %1 for person %2 choice %3"
        , args0:
          [ Number {name: "choice_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , Number {name: "person_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , Number {name: "choice", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType ChoseObservationType) =
  BlockDefinition
    $ merge
        { type: show ChoseObservationType
        , message0: "chose id %1 for person %2"
        , args0:
          [ Number {name: "choice_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , Number {name: "person_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType ValueGEObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueGEObservationType
        , message0: "value %1 is greater than or equal to %2"
        , args0:
          [ Value {name: "value1", check: "value", align: Right}
          , Value {name: "value2", check: "value", align: Right}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType ValueGObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueGObservationType
        , message0: "value %1 is greater than %2"
        , args0:
          [ Value {name: "value1", check: "value", align: Right}
          , Value {name: "value2", check: "value", align: Right}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType ValueLEObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueLEObservationType
        , message0: "value %1 is less than or equal to %2"
        , args0:
          [ Value {name: "value1", check: "value", align: Right}
          , Value {name: "value2", check: "value", align: Right}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType ValueLObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueLObservationType
        , message0: "value %1 is less than %2"
        , args0:
          [ Value {name: "value1", check: "value", align: Right}
          , Value {name: "value2", check: "value", align: Right}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType ValueEqObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueEqObservationType
        , message0: "value %1 is equal to %2"
        , args0:
          [ Value {name: "value1", check: "value", align: Right}
          , Value {name: "value2", check: "value", align: Right}
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType TrueObservationType) =
  BlockDefinition
    $ merge
        { type: show TrueObservationType
        , message0: "true"
        , lastDummyAlign0: Centre
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ObservationType FalseObservationType) =
  BlockDefinition
    $ merge
        { type: show FalseObservationType
        , message0: "false"
        , lastDummyAlign0: Centre
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType CurrentBlockType) =
  BlockDefinition
    $ merge
        { type: show CurrentBlockType
        , message0: "Current Block"
        , lastDummyAlign0: Centre
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType CommittedValueType) =
  BlockDefinition
    $ merge
        { type: show CommittedValueType
        , message0: "Committed Value %1"
        , args0:
          [ Number {name: "commit_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType ConstValueType) =
  BlockDefinition
    $ merge
        { type: show ConstValueType
        , message0: "Constant Value %1 ADA"
        , args0:
          [ Number {name: "constant", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType NegValueType) =
  BlockDefinition
    $ merge
        { type: show NegValueType
        , message0: "Negate Value %1"
        , args0:
          [ Value {name: "value", check: "value", align: Right}
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType AddValueType) =
  BlockDefinition
    $ merge
        { type: show AddValueType
        , message0: "%1 + %2"
        , args0:
          [ Value {name: "value1", check: "value", align: Right}
          , Value {name: "value2", check: "value", align: Right}
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType SubValueType) =
  BlockDefinition
    $ merge
        { type: show SubValueType
        , message0: "%1 - %2"
        , args0:
          [ Value {name: "value1", check: "value", align: Right}
          , Value {name: "value2", check: "value", align: Right}
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType MulValueType) =
  BlockDefinition
    $ merge
        { type: show MulValueType
        , message0: "%1 * %2"
        , args0:
          [ Value {name: "value1", check: "value", align: Right}
          , Value {name: "value2", check: "value", align: Right}
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType DivValueType) =
  BlockDefinition
    $ merge
        { type: show DivValueType
        , message0: "%1 / %2 with default %3"
        , args0:
          [ Value {name: "value1", check: "value", align: Right}
          , Value {name: "value2", check: "value", align: Right}
          , Value {name: "value3", check: "value", align: Right}
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType ModValueType) =
  BlockDefinition
    $ merge
        { type: show ModValueType
        , message0: "%1 % %2 with default %3"
        , args0:
          [ Value {name: "value1", check: "value", align: Right}
          , Value {name: "value2", check: "value", align: Right}
          , Value {name: "value3", check: "value", align: Right}
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType FromChoiceValueType) =
  BlockDefinition
    $ merge
        { type: show FromChoiceValueType
        , message0: "use value of choice with id: %1 chosen by participant with id: %2 if no choice was made use: %3"
        , args0:
          [ Number {name: "choice_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , Number {name: "person_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , Value {name: "value", check: "value", align: Right}
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toDefinition (ValueType FromOracleValueType) =
  BlockDefinition
    $ merge
        { type: show FromOracleValueType
        , message0: "use value of oracle with id: %1 if no oracle exists use: %2"
        , args0:
          [ Number {name: "oracle_id", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing}
          , Value {name: "value", check: "value", align: Right}
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        } defaultBlockDefinition

toolbox :: forall a b. HTML a b
toolbox =
  xml [id_ "blocklyToolbox", style "display:none"]
    [ category [name "Contracts", colour "0"] (map mkBlock contractTypes)
    , category [name "Observations", colour "230"] (map mkBlock observationTypes)
    , category [name "Values", colour "135"] (map mkBlock valueTypes)
    ]
  where
  mkBlock :: forall t. Show t => t -> _
  mkBlock t = block [blockType (show t)] []

workspaceBlocks :: forall a b. HTML a b
workspaceBlocks =
  xml [id_ "workspaceBlocks", style "display:none"]
    [ block [blockType (show BaseContractType), x "13", y "187", id_ "root_contract"] []
    ]

parse :: forall a. Parser String a -> String -> Either String a
parse p = lmap show <<< flip runParser (parens p <|> p)

buildGenerator :: BlocklyState -> Generator
buildGenerator blocklyState =
  ST.run
    ( do
      gRef <- mkGenerator blocklyState "Marlowe"
      g <- STRef.read gRef
      traverse_ (\t -> mkGenFun gRef t (baseContractDefinition g)) [BaseContractType]
      traverse_ (\t -> mkGenFun gRef t (blockDefinition t g)) contractTypes
      traverse_ (\t -> mkGenFun gRef t (blockDefinition t g)) observationTypes
      traverse_ (\t -> mkGenFun gRef t (blockDefinition t g)) valueTypes
      STRef.read gRef
    )

mkGenFun :: forall a r t. Show a => Show t => STRef r Generator -> t -> (Block -> Either String a) -> ST r Unit
mkGenFun generator blockType f = insertGeneratorFunction generator (show blockType) ((rmap show) <<< f)

class HasBlockDefinition a b | a -> b where
  blockDefinition :: a -> Generator -> Block -> Either String b

baseContractDefinition :: Generator -> Block -> Either String Contract
baseContractDefinition g block = parse Parser.contract =<< statementToCode g block (show BaseContractType)

instance hasBlockDefinitionContract :: HasBlockDefinition ContractType Contract where
  blockDefinition NullContractType _ _ = pure Null
  blockDefinition CommitContractType g block = do
    actionId <- parse Parser.idAction =<< getFieldValue block "action_id"
    commitId <- parse Parser.idCommit =<< getFieldValue block "commit_id"
    personId <- parse Parser.person =<< getFieldValue block "person_id"
    ammount <- parse Parser.value =<< statementToCode g block "ammount"
    endExpiration <- parse Parser.timeout =<< getFieldValue block "end_expiration"
    startExpiration <- parse Parser.timeout =<< getFieldValue block "start_expiration"
    contract1 <- parse Parser.contract =<< statementToCode g block "contract1"
    contract2 <- parse Parser.contract =<< statementToCode g block "contract2"
    pure (Commit actionId commitId personId ammount endExpiration startExpiration contract1 contract2)
  blockDefinition PayContractType g block = do
    actionId <- parse Parser.idAction =<< getFieldValue block "action_id"
    commitId <- parse Parser.idCommit =<< getFieldValue block "commit_id"
    payee <- parse Parser.person =<< getFieldValue block "payee_id"
    ammount <- parse Parser.value =<< statementToCode g block "ammount"
    timeout <- parse Parser.timeout =<< getFieldValue block "timeout"
    contract1 <- parse Parser.contract =<< statementToCode g block "contract1"
    contract2 <- parse Parser.contract =<< statementToCode g block "contract2"
    pure (Pay actionId commitId payee ammount timeout contract1 contract2)
  blockDefinition BothContractType g block = do
    contract1 <- parse Parser.contract =<< statementToCode g block "contract1"
    contract2 <- parse Parser.contract =<< statementToCode g block "contract2"
    pure (Both contract1 contract2)
  blockDefinition ChoiceContractType g block = do
    observation <- parse Parser.observation =<< statementToCode g block "observation"
    contract1 <- parse Parser.contract =<< statementToCode g block "contract1"
    contract2 <- parse Parser.contract =<< statementToCode g block "contract2"
    pure (Choice observation contract1 contract2)
  blockDefinition WhenContractType g block = do
    observation <- parse Parser.observation =<< statementToCode g block "observation"
    timeout <- parse Parser.timeout =<< getFieldValue block "timeout"
    contract1 <- parse Parser.contract =<< statementToCode g block "contract1"
    contract2 <- parse Parser.contract =<< statementToCode g block "contract2"
    pure (When observation timeout contract1 contract2)
  blockDefinition WhileContractType g block = do
    observation <- parse Parser.observation =<< statementToCode g block "observation"
    timeout <- parse Parser.timeout =<< getFieldValue block "timeout"
    contract1 <- parse Parser.contract =<< statementToCode g block "contract1"
    contract2 <- parse Parser.contract =<< statementToCode g block "contract2"
    pure (While observation timeout contract1 contract2)
  blockDefinition ScaleContractType g block = do
    scale1 <- parse Parser.value =<< statementToCode g block "scale1"
    scale2 <- parse Parser.value =<< statementToCode g block "scale2"
    scale3 <- parse Parser.value =<< statementToCode g block "scale3"
    contract <- parse Parser.contract =<< statementToCode g block "contract"
    pure (Scale scale1 scale2 scale3 contract)
  blockDefinition LetContractType g block = do
    letLabel <- parse Parser.bigInteger =<< getFieldValue block "let_label"
    contract1 <- parse Parser.contract =<< statementToCode g block "contract1"
    contract2 <- parse Parser.contract =<< statementToCode g block "contract2"
    pure (Let letLabel contract1 contract2)
  blockDefinition UseContractType g block = do
    letLabel <- parse Parser.bigInteger =<< getFieldValue block "let_label"
    pure (Use letLabel)

instance hasBlockDefinitionObservation :: HasBlockDefinition ObservationType Observation where
  blockDefinition BelowTimeoutObservationType g block = do
    timeout <- parse Parser.timeout =<< getFieldValue block "timeout"
    pure (BelowTimeout timeout)
  blockDefinition AndObservationType g block = do
    observation1 <- parse Parser.observation =<< statementToCode g block "observation1"
    observation2 <- parse Parser.observation =<< statementToCode g block "observation2"
    pure (AndObs observation1 observation2)
  blockDefinition OrObservationType g block = do
    observation1 <- parse Parser.observation =<< statementToCode g block "observation1"
    observation2 <- parse Parser.observation =<< statementToCode g block "observation2"
    pure (OrObs observation1 observation2)
  blockDefinition NotObservationType g block = do
    observation <- parse Parser.observation =<< statementToCode g block "observation"
    pure (NotObs observation)
  blockDefinition ChoseThisObservationType g block = do
    choiceId <- parse Parser.bigInteger =<< getFieldValue block "choice_id"
    personId <- parse Parser.person =<< getFieldValue block "person_id"
    choice <- parse Parser.choice =<< getFieldValue block "choice"
    let
      idChoice = IdChoice {choice: choiceId, person: personId}
    pure (ChoseThis idChoice choice)
  blockDefinition ChoseObservationType g block = do
    choiceId <- parse Parser.bigInteger =<< getFieldValue block "choice_id"
    personId <- parse Parser.person =<< getFieldValue block "person_id"
    let
      idChoice = IdChoice {choice: choiceId, person: personId}
    pure (ChoseSomething idChoice)
  blockDefinition ValueGEObservationType g block = do
    value1 <- parse Parser.value =<< statementToCode g block "value1"
    value2 <- parse Parser.value =<< statementToCode g block "value2"
    pure (ValueGE value1 value2)
  blockDefinition ValueGObservationType g block = do
    value1 <- parse Parser.value =<< statementToCode g block "value1"
    value2 <- parse Parser.value =<< statementToCode g block "value2"
    pure (ValueGT value1 value2)
  blockDefinition ValueLEObservationType g block = do
    value1 <- parse Parser.value =<< statementToCode g block "value1"
    value2 <- parse Parser.value =<< statementToCode g block "value2"
    pure (ValueLE value1 value2)
  blockDefinition ValueLObservationType g block = do
    value1 <- parse Parser.value =<< statementToCode g block "value1"
    value2 <- parse Parser.value =<< statementToCode g block "value2"
    pure (ValueLT value1 value2)
  blockDefinition ValueEqObservationType g block = do
    value1 <- parse Parser.value =<< statementToCode g block "value1"
    value2 <- parse Parser.value =<< statementToCode g block "value2"
    pure (ValueEQ value1 value2)
  blockDefinition TrueObservationType g block = pure TrueObs
  blockDefinition FalseObservationType g block = pure FalseObs

instance hasBlockDefinitionValue :: HasBlockDefinition ValueType Value where
  blockDefinition CurrentBlockType g block = pure CurrentBlock
  blockDefinition CommittedValueType g block = do
    commitId <- parse Parser.idCommit =<< getFieldValue block "commit_id"
    pure (Committed commitId)
  blockDefinition ConstValueType g block = do
    constant <- parse Parser.bigInteger =<< getFieldValue block "constant"
    pure (Constant constant)
  blockDefinition NegValueType g block = do
    value <- parse Parser.value =<< statementToCode g block "value"
    pure (NegValue value)
  blockDefinition AddValueType g block = do
    value1 <- parse Parser.value =<< statementToCode g block "value1"
    value2 <- parse Parser.value =<< statementToCode g block "value2"
    pure (AddValue value1 value2)
  blockDefinition SubValueType g block = do
    value1 <- parse Parser.value =<< statementToCode g block "value1"
    value2 <- parse Parser.value =<< statementToCode g block "value2"
    pure (SubValue value1 value2)
  blockDefinition MulValueType g block = do
    value1 <- parse Parser.value =<< statementToCode g block "value1"
    value2 <- parse Parser.value =<< statementToCode g block "value2"
    pure (MulValue value1 value2)
  blockDefinition DivValueType g block = do
    value1 <- parse Parser.value =<< statementToCode g block "value1"
    value2 <- parse Parser.value =<< statementToCode g block "value2"
    value3 <- parse Parser.value =<< statementToCode g block "value3"
    pure (DivValue value1 value2 value3)
  blockDefinition ModValueType g block = do
    value1 <- parse Parser.value =<< statementToCode g block "value1"
    value2 <- parse Parser.value =<< statementToCode g block "value2"
    value3 <- parse Parser.value =<< statementToCode g block "value3"
    pure (ModValue value1 value2 value3)
  blockDefinition FromChoiceValueType g block = do
    choiceId <- parse Parser.bigInteger =<< getFieldValue block "choice_id"
    personId <- parse Parser.person =<< getFieldValue block "person_id"
    value <- parse Parser.value =<< statementToCode g block "value"
    let
      idChoice = IdChoice {choice: choiceId, person: personId}
    pure (ValueFromChoice idChoice value)
  blockDefinition FromOracleValueType g block = do
    oracleId <- parse Parser.idOracle =<< getFieldValue block "oracle_id"
    value <- parse Parser.value =<< statementToCode g block "value"
    pure (ValueFromOracle oracleId value)

buildBlocks :: forall r. NewBlockFunction r -> BlocklyState -> Contract -> ST r Unit
buildBlocks newBlock bs contract = do
  workspaceRef <- STRef.new bs.workspace
  clearWorkspace workspaceRef
  initializeWorkspace bs.blockly workspaceRef
  let
    mContract = getBlockById bs.workspace "root_contract"
  rootBlock <- case mContract of
    Nothing -> do
      blockRef <- newBlock workspaceRef (show BaseContractType)
      STRef.read blockRef
    Just block -> pure block
  let
    inputs = inputList rootBlock

    mInput = getInputWithName inputs (show BaseContractType)
  case mInput of
    Nothing -> pure unit
    Just i -> do
      toBlockly newBlock workspaceRef i contract
      render workspaceRef

setField :: forall r. (STRef r Block) -> String -> String -> ST r Unit
setField blockRef name value = do
  block <- STRef.read blockRef
  let
    fields = inputList block >>= fieldRow
  case Array.find (\f -> fieldName f == name) fields of
    Nothing -> pure unit
    Just f -> do
      field <- STRef.new f
      setFieldText field value

inputToBlockly :: forall a r. ToBlockly a => NewBlockFunction r -> (STRef r Workspace) -> STRef r Block -> String -> a -> ST r Unit
inputToBlockly newBlock workspaceRef blockRef name value = do
  block <- STRef.read blockRef
  case Array.find (\i -> inputName i == name) (inputList block) of
    Nothing -> pure unit
    Just input -> toBlockly newBlock workspaceRef input value

class ToBlockly a where
  toBlockly :: forall r. NewBlockFunction r -> STRef r Workspace -> Input -> a -> ST r Unit

instance toBlocklyContract :: ToBlockly Contract where
  toBlockly newBlock workspace input Null = do
    block <- newBlock workspace (show NullContractType)
    connectToPrevious block input
  toBlockly newBlock workspace input (Commit action commit person ammount endExpiration startExpiration contract1 contract2) = do
    block <- newBlock workspace (show CommitContractType)
    connectToPrevious block input
    setField block "action_id" (show (unwrap action))
    setField block "commit_id" (show (unwrap commit))
    setField block "person_id" (show person)
    inputToBlockly newBlock workspace block "ammount" ammount
    setField block "end_expiration" (show (unwrap endExpiration))
    setField block "start_expiration" (show (unwrap startExpiration))
    inputToBlockly newBlock workspace block "contract1" contract1
    inputToBlockly newBlock workspace block "contract2" contract2
  toBlockly newBlock workspace input (Pay action commit payee ammount timeout contract1 contract2) = do
    block <- newBlock workspace (show PayContractType)
    connectToPrevious block input
    setField block "action_id" (show (unwrap action))
    setField block "commit_id" (show (unwrap commit))
    setField block "payee_id" (show payee)
    inputToBlockly newBlock workspace block "ammount" ammount
    setField block "timeout" (show timeout)
    inputToBlockly newBlock workspace block "contract1" contract1
    inputToBlockly newBlock workspace block "contract2" contract2
  toBlockly newBlock workspace input (Both contract1 contract2) = do
    block <- newBlock workspace (show BothContractType)
    connectToPrevious block input
    inputToBlockly newBlock workspace block "contract1" contract1
    inputToBlockly newBlock workspace block "contract2" contract2
  toBlockly newBlock workspace input (Choice observation contract1 contract2) = do
    block <- newBlock workspace (show ChoiceContractType)
    connectToPrevious block input
    inputToBlockly newBlock workspace block "observation" observation
    inputToBlockly newBlock workspace block "contract1" contract1
    inputToBlockly newBlock workspace block "contract2" contract2
  toBlockly newBlock workspace input (When observation timeout contract1 contract2) = do
    block <- newBlock workspace (show WhenContractType)
    connectToPrevious block input
    inputToBlockly newBlock workspace block "observation" observation
    setField block "timeout" (show timeout)
    inputToBlockly newBlock workspace block "contract1" contract1
    inputToBlockly newBlock workspace block "contract2" contract2
  toBlockly newBlock workspace input (While observation timeout contract1 contract2) = do
    block <- newBlock workspace (show WhileContractType)
    connectToPrevious block input
    inputToBlockly newBlock workspace block "observation" observation
    setField block "timeout" (show timeout)
    inputToBlockly newBlock workspace block "contract1" contract1
    inputToBlockly newBlock workspace block "contract2" contract2
  toBlockly newBlock workspace input (Scale v1 v2 v3 contract) = do
    block <- newBlock workspace (show ScaleContractType)
    connectToPrevious block input
    inputToBlockly newBlock workspace block "scale1" v1
    inputToBlockly newBlock workspace block "scale2" v2
    inputToBlockly newBlock workspace block "scale3" v3
    inputToBlockly newBlock workspace block "contract" contract
  toBlockly newBlock workspace input (Let label contract1 contract2) = do
    block <- newBlock workspace (show LetContractType)
    connectToPrevious block input
    setField block "let_label" (show label)
    inputToBlockly newBlock workspace block "contract1" contract1
    inputToBlockly newBlock workspace block "contract2" contract2
  toBlockly newBlock workspace input (Use label) = do
    block <- newBlock workspace (show UseContractType)
    connectToPrevious block input
    setField block "let_label" (show label)

instance toBlocklyObservation :: ToBlockly Observation where
  toBlockly newBlock workspace input (BelowTimeout timeout) = do
    block <- newBlock workspace (show BelowTimeoutObservationType)
    connectToOutput block input
    setField block "timeout" (show timeout)
  toBlockly newBlock workspace input (AndObs observation1 observation2) = do
    block <- newBlock workspace (show AndObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "observation1" observation1
    inputToBlockly newBlock workspace block "observation2" observation2
  toBlockly newBlock workspace input (OrObs observation1 observation2) = do
    block <- newBlock workspace (show OrObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "observation1" observation1
    inputToBlockly newBlock workspace block "observation2" observation2
  toBlockly newBlock workspace input (NotObs observation) = do
    block <- newBlock workspace (show NotObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "observation" observation
  toBlockly newBlock workspace input (ChoseThis choiceId choice) = do
    block <- newBlock workspace (show ChoseThisObservationType)
    connectToOutput block input
    setField block "choice_id" (show (unwrap choiceId).choice)
    setField block "person_id" (show (unwrap choiceId).person)
    setField block "choice" (show choice)
  toBlockly newBlock workspace input (ChoseSomething choiceId) = do
    block <- newBlock workspace (show ChoseObservationType)
    connectToOutput block input
    setField block "choice_id" (show (unwrap choiceId).choice)
    setField block "person_id" (show (unwrap choiceId).person)
  toBlockly newBlock workspace input (ValueGE v1 v2) = do
    block <- newBlock workspace (show ValueGEObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (ValueGT v1 v2) = do
    block <- newBlock workspace (show ValueGObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (ValueLT v1 v2) = do
    block <- newBlock workspace (show ValueLObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (ValueLE v1 v2) = do
    block <- newBlock workspace (show ValueLEObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (ValueEQ v1 v2) = do
    block <- newBlock workspace (show ValueEqObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input TrueObs = do
    block <- newBlock workspace (show TrueObservationType)
    connectToOutput block input
  toBlockly newBlock workspace input FalseObs = do
    block <- newBlock workspace (show FalseObservationType)
    connectToOutput block input

instance toBlocklyValue :: ToBlockly Value where
  toBlockly newBlock workspace input CurrentBlock = do
    block <- newBlock workspace (show CurrentBlockType)
    connectToOutput block input
  toBlockly newBlock workspace input (Committed v) = do
    block <- newBlock workspace (show CommittedValueType)
    connectToOutput block input
    setField block "commit_id" (show v)
  toBlockly newBlock workspace input (Constant v) = do
    block <- newBlock workspace (show ConstValueType)
    connectToOutput block input
    setField block "constant" (show v)
  toBlockly newBlock workspace input (NegValue v) = do
    block <- newBlock workspace (show NegValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value" v
  toBlockly newBlock workspace input (AddValue v1 v2) = do
    block <- newBlock workspace (show AddValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (SubValue v1 v2) = do
    block <- newBlock workspace (show SubValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (MulValue v1 v2) = do
    block <- newBlock workspace (show MulValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (DivValue v1 v2 v3) = do
    block <- newBlock workspace (show DivValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
    inputToBlockly newBlock workspace block "value3" v3
  toBlockly newBlock workspace input (ModValue v1 v2 v3) = do
    block <- newBlock workspace (show ModValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
    inputToBlockly newBlock workspace block "value3" v3
  toBlockly newBlock workspace input (ValueFromChoice v1 v2) = do
    block <- newBlock workspace (show FromChoiceValueType)
    connectToOutput block input
    setField block "choice_id" (show (unwrap v1).choice)
    setField block "person_id" (show (unwrap v1).person)
    inputToBlockly newBlock workspace block "value" v2
  toBlockly newBlock workspace input (ValueFromOracle v1 v2) = do
    block <- newBlock workspace (show FromOracleValueType)
    connectToOutput block input
    setField block "oracle_id" (show (unwrap v1))
    inputToBlockly newBlock workspace block "value" v2
