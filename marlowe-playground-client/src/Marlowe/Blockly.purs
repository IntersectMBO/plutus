module Marlowe.Blockly where

import Prelude
import Blockly (AlignDirection(..), Arg(..), BlockDefinition(..), block, blockType, category, colour, defaultBlockDefinition, getBlockById, initializeWorkspace, name, render, style, x, xml, y)
import Blockly.Generator (Connection, Generator, Input, NewBlockFunction, clearWorkspace, connect, connectToOutput, connectToPrevious, fieldName, fieldRow, getBlockInputConnectedTo, getFieldValue, getInputWithName, getType, inputList, inputName, inputType, insertGeneratorFunction, mkGenerator, nextBlock, nextConnection, previousConnection, setFieldText, statementToCode)
import Blockly.Types (Block, BlocklyState, Workspace)
import Control.Alternative ((<|>))
import Control.Monad.ST as ST
import Control.Monad.ST.Internal (ST, STRef)
import Control.Monad.ST.Ref as STRef
import Data.Array (filter, head, uncons, (:))
import Data.Array as Array
import Data.Bifunctor (lmap, rmap)
import Data.Either (Either, note)
import Data.Either as Either
import Data.Enum (class BoundedEnum, class Enum, upFromIncluding)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Bounded (genericBottom, genericTop)
import Data.Generic.Rep.Enum (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Generic.Rep.Show (genericShow)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse, traverse_)
import Halogen.HTML (HTML)
import Halogen.HTML.Properties (id_)
import Marlowe.Parser as Parser
import Marlowe.Semantics (AccountId(..), Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Observation(..), Payee(..), Party(..), Token(..), Value(..), ValueId(..))
import Record (merge)
import Text.Parsing.StringParser (Parser)
import Text.Parsing.StringParser.Basic (parens, runParser')

data ActionType
  = DepositActionType
  | ChoiceActionType
  | NotifyActionType

derive instance genericActionType :: Generic ActionType _

instance showActionType :: Show ActionType where
  show = genericShow

instance eqActionType :: Eq ActionType where
  eq = genericEq

instance ordActionType :: Ord ActionType where
  compare = genericCompare

instance enumActionType :: Enum ActionType where
  succ = genericSucc
  pred = genericPred

instance boundedActionType :: Bounded ActionType where
  bottom = genericBottom
  top = genericTop

instance boundedEnumActionType :: BoundedEnum ActionType where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

actionTypes :: Array ActionType
actionTypes = upFromIncluding bottom

data PayeeType
  = AccountPayeeType
  | PartyPayeeType

derive instance genericPayeeType :: Generic PayeeType _

instance showPayeeType :: Show PayeeType where
  show = genericShow

instance eqPayeeType :: Eq PayeeType where
  eq = genericEq

instance ordPayeeType :: Ord PayeeType where
  compare = genericCompare

instance enumPayeeType :: Enum PayeeType where
  succ = genericSucc
  pred = genericPred

instance boundedPayeeType :: Bounded PayeeType where
  bottom = genericBottom
  top = genericTop

instance boundedEnumPayeeType :: BoundedEnum PayeeType where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

payeeTypes :: Array PayeeType
payeeTypes = upFromIncluding bottom

data PartyType
  = PKPartyType
  | RolePartyType

derive instance genericPartyType :: Generic PartyType _

instance showPartyType :: Show PartyType where
  show = genericShow

instance eqPartyType :: Eq PartyType where
  eq = genericEq

instance ordPartyType :: Ord PartyType where
  compare = genericCompare

instance enumPartyType :: Enum PartyType where
  succ = genericSucc
  pred = genericPred

instance boundedPartyType :: Bounded PartyType where
  bottom = genericBottom
  top = genericTop

instance boundedEnumPartyType :: BoundedEnum PartyType where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

partyTypes :: Array PartyType
partyTypes = upFromIncluding bottom

data TokenType
  = CustomTokenType

derive instance genericTokenType :: Generic TokenType _

instance showTokenType :: Show TokenType where
  show = genericShow

instance eqTokenType :: Eq TokenType where
  eq = genericEq

instance ordTokenType :: Ord TokenType where
  compare = genericCompare

instance enumTokenType :: Enum TokenType where
  succ = genericSucc
  pred = genericPred

instance boundedTokenType :: Bounded TokenType where
  bottom = genericBottom
  top = genericTop

instance boundedEnumTokenType :: BoundedEnum TokenType where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

tokenTypes :: Array TokenType
tokenTypes = upFromIncluding bottom

data ContractType
  = WhenContractType
  | PayContractType
  | IfContractType
  | LetContractType
  | CloseContractType

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
  = AndObservationType
  | OrObservationType
  | NotObservationType
  | ChoseSomethingObservationType
  | ValueGEObservationType
  | ValueGTObservationType
  | ValueLTObservationType
  | ValueLEObservationType
  | ValueEQObservationType
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
  = AvailableMoneyValueType
  | ConstantValueType
  | NegValueValueType
  | AddValueValueType
  | SubValueValueType
  | ChoiceValueValueType
  | SlotIntervalStartValueType
  | SlotIntervalEndValueType
  | UseValueValueType

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
  | BoundsType
  | ActionType ActionType
  | ContractType ContractType
  | ObservationType ObservationType
  | ValueType ValueType
  | PayeeType PayeeType
  | PartyType PartyType
  | TokenType TokenType

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
  show BoundsType = "BoundsType"
  show (ContractType c) = show c
  show (ObservationType ot) = show ot
  show (ValueType vt) = show vt
  show (PayeeType pt) = show pt
  show (PartyType pt) = show pt
  show (TokenType tt) = show tt
  show (ActionType at) = show at

blockDefinitions :: Array BlockDefinition
blockDefinitions = map toDefinition (upFromIncluding bottom)

toDefinition :: BlockType -> BlockDefinition
toDefinition BaseContractType =
  BlockDefinition
    $ merge
        { type: show BaseContractType
        , message0: "%1 CONTRACT %2 %3 %4 %5"
        , args0:
          [ DummyRight
          , DummyRight
          , DummyRight
          , Statement { name: (show BaseContractType), check: (show BaseContractType), align: Right }
          , DummyRight
          ]
        , colour: "45"
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition BoundsType =
  BlockDefinition
    $ merge
        { type: show BoundsType
        , message0: "between %1 and %2"
        , args0:
          [ Number { name: "from", value: 1.0, min: Nothing, max: Nothing, precision: Nothing }
          , Number { name: "to", value: 2.0, min: Nothing, max: Nothing, precision: Nothing }
          ]
        , colour: "75"
        , previousStatement: Just (show BoundsType)
        , nextStatement: Just (show BoundsType)
        }
        defaultBlockDefinition

-- Action
toDefinition (ActionType DepositActionType) =
  BlockDefinition
    $ merge
        { type: show DepositActionType
        , message0: "Deposit %1 the amount of %2 units of token %3 into the account %4 %5 with owner %6 from %7 continue as %8 %9"
        , args0:
          [ DummyCentre
          , Value { name: "amount", check: "value", align: Right }
          , Value { name: "token", check: "token", align: Right }
          , Number { name: "account_number", value: 0.0, min: Nothing, max: Nothing, precision: Nothing }
          , DummyRight
          , Value { name: "account_owner", check: "party", align: Right }
          , Value { name: "party", check: "party", align: Right }
          , DummyLeft
          , Statement { name: "contract", check: (show BaseContractType), align: Right }
          ]
        , colour: "290"
        , previousStatement: Just "ActionType"
        , nextStatement: Just "ActionType"
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition (ActionType ChoiceActionType) =
  BlockDefinition
    $ merge
        { type: show ChoiceActionType
        , message0: "Choice name %1 %2 choice owner %3 choice bounds %4 %5 continue as %6 %7"
        , args0:
          [ Input { name: "choice_name", text: "Name", spellcheck: false }
          , DummyLeft
          , Value { name: "choice_owner", check: "party", align: Right }
          , DummyLeft
          , Statement { name: "bounds", check: (show BoundsType), align: Right }
          , DummyLeft
          , Statement { name: "contract", check: (show BaseContractType), align: Right }
          ]
        , colour: "290"
        , previousStatement: Just "ActionType"
        , nextStatement: Just "ActionType"
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition (ActionType NotifyActionType) =
  BlockDefinition
    $ merge
        { type: show NotifyActionType
        , message0: "Notification of %1 continue as %2 %3"
        , args0:
          [ Value { name: "observation", check: "observation", align: Right }
          , DummyLeft
          , Statement { name: "contract", check: (show BaseContractType), align: Right }
          ]
        , colour: "290"
        , previousStatement: Just "ActionType"
        , nextStatement: Just "ActionType"
        , inputsInline: Just false
        }
        defaultBlockDefinition

-- Payee
toDefinition (PayeeType AccountPayeeType) =
  BlockDefinition
    $ merge
        { type: show AccountPayeeType
        , message0: "Account %1 with Owner %2"
        , args0:
          [ Number { name: "account_number", value: 1.0, min: Nothing, max: Nothing, precision: Nothing }
          , Value { name: "account_owner", check: "party", align: Right }
          ]
        , colour: "210"
        , output: Just "payee"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (PayeeType PartyPayeeType) =
  BlockDefinition
    $ merge
        { type: show PartyPayeeType
        , message0: "Party %1"
        , args0:
          [ Value { name: "party", check: "party", align: Right }
          ]
        , colour: "210"
        , output: Just "payee"
        , inputsInline: Just true
        }
        defaultBlockDefinition

-- Party
toDefinition (PartyType PKPartyType) =
  BlockDefinition
    $ merge
        { type: show PKPartyType
        , message0: "Public Key %1"
        , args0:
          [ Input { name: "pubkey", text: "pubkey", spellcheck: false }
          ]
        , colour: "180"
        , output: Just "party"
        , inputsInline: Just true
        }
        defaultBlockDefinition

-- Custom Token type
toDefinition (TokenType CustomTokenType) =
  BlockDefinition
    $ merge
        { type: show CustomTokenType
        , message0: "Token with currency %1 and token name %2"
        , args0:
          [ Input { name: "currency_symbol", text: "", spellcheck: false }
          , Input { name: "token_name", text: "", spellcheck: false }
          ]
        , colour: "255"
        , output: Just "token"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (PartyType RolePartyType) =
  BlockDefinition
    $ merge
        { type: show RolePartyType
        , message0: "Role %1"
        , args0:
          [ Input { name: "role", text: "role", spellcheck: false }
          ]
        , colour: "180"
        , output: Just "party"
        , inputsInline: Just true
        }
        defaultBlockDefinition

-- Contracts
toDefinition (ContractType CloseContractType) =
  BlockDefinition
    $ merge
        { type: show CloseContractType
        , message0: "Close"
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        }
        defaultBlockDefinition

toDefinition (ContractType PayContractType) =
  BlockDefinition
    $ merge
        { type: show PayContractType
        , message0: "Pay %1 party %2 the amount of %3 of currency %4 from the account %5 %6 with owner %7 continue as %8 %9"
        , args0:
          [ DummyCentre
          , Value { name: "payee", check: "payee", align: Right }
          , Value { name: "amount", check: "value", align: Right }
          , Value { name: "token", check: "token", align: Right }
          , Number { name: "account_number", value: 1.0, min: Nothing, max: Nothing, precision: Nothing }
          , DummyRight
          , Value { name: "account_owner", check: "party", align: Right }
          , DummyLeft
          , Statement { name: "contract", check: (show BaseContractType), align: Right }
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition (ContractType IfContractType) =
  BlockDefinition
    $ merge
        { type: show IfContractType
        , message0: "If observation %1 then %2 %3 else %4 %5"
        , args0:
          [ Value { name: "observation", check: "observation", align: Right }
          , DummyLeft
          , Statement { name: "contract1", check: (show BaseContractType), align: Right }
          , DummyLeft
          , Statement { name: "contract2", check: (show BaseContractType), align: Right }
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition (ContractType WhenContractType) =
  BlockDefinition
    $ merge
        { type: show WhenContractType
        , message0: "When %1 %2 after slot %3 %4 continue as %5 %6"
        , args0:
          [ DummyCentre
          , Statement { name: "case", check: "ActionType", align: Left }
          , Number { name: "timeout", value: 0.0, min: Nothing, max: Nothing, precision: Nothing }
          , DummyLeft
          , DummyLeft
          , Statement { name: "contract", check: (show BaseContractType), align: Right }
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition (ContractType LetContractType) =
  BlockDefinition
    $ merge
        { type: show LetContractType
        , message0: "Let %1 be %2 continue as %3 %4"
        , args0:
          [ Input { name: "value_id", text: "value", spellcheck: false }
          , Value { name: "value", check: "value", align: Right }
          , DummyLeft
          , Statement { name: "contract", check: (show BaseContractType), align: Right }
          ]
        , colour: "0"
        , previousStatement: Just (show BaseContractType)
        }
        defaultBlockDefinition

-- Observations
toDefinition (ObservationType AndObservationType) =
  BlockDefinition
    $ merge
        { type: show AndObservationType
        , message0: "%1 and %2"
        , args0:
          [ Value { name: "observation1", check: "observation", align: Right }
          , Value { name: "observation2", check: "observation", align: Right }
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ObservationType OrObservationType) =
  BlockDefinition
    $ merge
        { type: show OrObservationType
        , message0: "%1 or %2"
        , args0:
          [ Value { name: "observation1", check: "observation", align: Right }
          , Value { name: "observation2", check: "observation", align: Right }
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ObservationType NotObservationType) =
  BlockDefinition
    $ merge
        { type: show NotObservationType
        , message0: "Not %1"
        , args0:
          [ Value { name: "observation", check: "observation", align: Right }
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ObservationType ChoseSomethingObservationType) =
  BlockDefinition
    $ merge
        { type: show ChoseSomethingObservationType
        , message0: "chose id %1 for person %2"
        , args0:
          [ Input { name: "choice_name", text: "Name", spellcheck: false }
          , Value { name: "choice_owner", check: "party", align: Right }
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ObservationType ValueGEObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueGEObservationType
        , message0: "value %1 is greater than or equal to %2"
        , args0:
          [ Value { name: "value1", check: "value", align: Right }
          , Value { name: "value2", check: "value", align: Right }
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ObservationType ValueGTObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueGTObservationType
        , message0: "value %1 is greater than %2"
        , args0:
          [ Value { name: "value1", check: "value", align: Right }
          , Value { name: "value2", check: "value", align: Right }
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ObservationType ValueLEObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueLEObservationType
        , message0: "value %1 is less than or equal to %2"
        , args0:
          [ Value { name: "value1", check: "value", align: Right }
          , Value { name: "value2", check: "value", align: Right }
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ObservationType ValueLTObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueLTObservationType
        , message0: "value %1 is less than %2"
        , args0:
          [ Value { name: "value1", check: "value", align: Right }
          , Value { name: "value2", check: "value", align: Right }
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ObservationType ValueEQObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueEQObservationType
        , message0: "value %1 is equal to %2"
        , args0:
          [ Value { name: "value1", check: "value", align: Right }
          , Value { name: "value2", check: "value", align: Right }
          ]
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ObservationType TrueObservationType) =
  BlockDefinition
    $ merge
        { type: show TrueObservationType
        , message0: "true"
        , lastDummyAlign0: Centre
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ObservationType FalseObservationType) =
  BlockDefinition
    $ merge
        { type: show FalseObservationType
        , message0: "false"
        , lastDummyAlign0: Centre
        , colour: "230"
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

-- Values
toDefinition (ValueType AvailableMoneyValueType) =
  BlockDefinition
    $ merge
        { type: show AvailableMoneyValueType
        , message0: "Available Money %1 of currency %2 from account number %3 %4 with owner %5 %6"
        , args0:
          [ DummyRight
          , Value { name: "token", check: "token", align: Right }
          , Number { name: "account_number", value: 1.0, min: Nothing, max: Nothing, precision: Nothing }
          , DummyRight
          , Value { name: "account_owner", check: "party", align: Right }
          , DummyRight
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ValueType ConstantValueType) =
  BlockDefinition
    $ merge
        { type: show ConstantValueType
        , message0: "Constant Value %1"
        , args0:
          [ Number { name: "constant", value: 1.0, min: Nothing, max: Nothing, precision: Nothing }
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ValueType NegValueValueType) =
  BlockDefinition
    $ merge
        { type: show NegValueValueType
        , message0: "Negate Value %1"
        , args0:
          [ Value { name: "value", check: "value", align: Right }
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ValueType AddValueValueType) =
  BlockDefinition
    $ merge
        { type: show AddValueValueType
        , message0: "%1 + %2"
        , args0:
          [ Value { name: "value1", check: "value", align: Right }
          , Value { name: "value2", check: "value", align: Right }
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ValueType SubValueValueType) =
  BlockDefinition
    $ merge
        { type: show SubValueValueType
        , message0: "%1 - %2"
        , args0:
          [ Value { name: "value1", check: "value", align: Right }
          , Value { name: "value2", check: "value", align: Right }
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ValueType ChoiceValueValueType) =
  BlockDefinition
    $ merge
        { type: show ChoiceValueValueType
        , message0: "use value of choice with id: %1 chosen by participant with id: %2 if no choice was made use: %3"
        , args0:
          [ Input { name: "choice_name", text: "Name", spellcheck: false }
          , Value { name: "choice_owner", check: "party", align: Right }
          , Value { name: "value", check: "value", align: Right }
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ValueType SlotIntervalStartValueType) =
  BlockDefinition
    $ merge
        { type: show SlotIntervalStartValueType
        , message0: "Slot Interval Start"
        , lastDummyAlign0: Centre
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ValueType SlotIntervalEndValueType) =
  BlockDefinition
    $ merge
        { type: show SlotIntervalEndValueType
        , message0: "Slot Interval End"
        , lastDummyAlign0: Centre
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition (ValueType UseValueValueType) =
  BlockDefinition
    $ merge
        { type: show UseValueValueType
        , message0: "Use Value with ID %1"
        , args0:
          [ Input { name: "value_id", text: "value", spellcheck: false }
          ]
        , colour: "135"
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toolbox :: forall a b. HTML a b
toolbox =
  xml [ id_ "blocklyToolbox", style "display:none" ]
    [ category [ name "Contracts", colour "0" ] (map mkBlock contractTypes)
    , category [ name "Observations", colour "230" ] (map mkBlock observationTypes)
    , category [ name "Actions", colour "290" ] (map mkBlock actionTypes)
    , category [ name "Values", colour "135" ] (map mkBlock valueTypes)
    , category [ name "Payee", colour "210" ] (map mkBlock payeeTypes)
    , category [ name "Party", colour "180" ] (map mkBlock partyTypes)
    , category [ name "Token", colour "255" ] (map mkBlock tokenTypes)
    , category [ name "Bounds", colour "75" ] (map mkBlock [ BoundsType ])
    ]
  where
  mkBlock :: forall t. Show t => t -> _
  mkBlock t = block [ blockType (show t) ] []

workspaceBlocks :: forall a b. HTML a b
workspaceBlocks =
  xml [ id_ "workspaceBlocks", style "display:none" ]
    [ block [ blockType (show BaseContractType), x "13", y "187", id_ "root_contract" ] []
    ]

parse :: forall a. Parser a -> String -> Either String a
parse p = lmap show <<< runParser' (parens p <|> p)

buildGenerator :: BlocklyState -> Generator
buildGenerator blocklyState =
  ST.run
    ( do
        gRef <- mkGenerator blocklyState "Marlowe"
        g <- STRef.read gRef
        traverse_ (\t -> mkGenFun gRef t (baseContractDefinition g)) [ BaseContractType ]
        traverse_ (\t -> mkGenFun gRef t (blockDefinition t g)) contractTypes
        traverse_ (\t -> mkGenFun gRef t (blockDefinition t g)) payeeTypes
        traverse_ (\t -> mkGenFun gRef t (blockDefinition t g)) partyTypes
        traverse_ (\t -> mkGenFun gRef t (blockDefinition t g)) tokenTypes
        traverse_ (\t -> mkGenFun gRef t (blockDefinition t g)) observationTypes
        traverse_ (\t -> mkGenFun gRef t (blockDefinition t g)) valueTypes
        traverse_ (\t -> mkGenFun gRef t (blockDefinition t g)) actionTypes
        traverse_ (\t -> mkGenFun gRef t (boundsDefinition g)) [ BoundsType ]
        STRef.read gRef
    )

mkGenFun :: forall a r t. Show a => Show t => STRef r Generator -> t -> (Block -> Either String a) -> ST r Unit
mkGenFun generator blockType f = insertGeneratorFunction generator (show blockType) ((rmap show) <<< f)

class HasBlockDefinition a b | a -> b where
  blockDefinition :: a -> Generator -> Block -> Either String b

baseContractDefinition :: Generator -> Block -> Either String Contract
baseContractDefinition g block = parse Parser.contractValue =<< statementToCode g block (show BaseContractType)

getAllBlocks :: Block -> Array Block
getAllBlocks currentBlock =
  currentBlock
    : ( case nextBlock currentBlock of
          Nothing -> []
          Just nextBlock' -> getAllBlocks nextBlock'
      )

caseDefinition :: Generator -> Block -> Either String Case
caseDefinition g block =
  let
    maybeActionType = case getType block of
      "DepositActionType" -> Just DepositActionType
      "ChoiceActionType" -> Just ChoiceActionType
      "NotifyActionType" -> Just NotifyActionType
      _ -> Nothing
  in
    case maybeActionType of
      Nothing -> Either.Left "Could not parse ActionType in caseDefinition function"
      Just actionType -> blockDefinition actionType g block

casesDefinition :: Generator -> Block -> Either String (Array Case)
casesDefinition g block = traverse (caseDefinition g) (getAllBlocks block)

boundDefinition :: Generator -> Block -> Either String Bound
boundDefinition g block = do
  from <- parse Parser.bigInteger =<< getFieldValue block "from"
  to <- parse Parser.bigInteger =<< getFieldValue block "to"
  pure (Bound from to)

boundsDefinition :: Generator -> Block -> Either String (Array Bound)
boundsDefinition g block = traverse (boundDefinition g) (getAllBlocks block)

instance hasBlockDefinitionAction :: HasBlockDefinition ActionType Case where
  blockDefinition DepositActionType g block = do
    accountNumber <- parse Parser.bigInteger =<< getFieldValue block "account_number"
    accountOwner <- parse (Parser.parseToValue Parser.party) =<< statementToCode g block "account_owner"
    tok <- parse (Parser.parseToValue Parser.token) =<< statementToCode g block "token"
    let
      accountId = AccountId accountNumber accountOwner
    party <- parse (Parser.parseToValue Parser.party) =<< statementToCode g block "party"
    amount <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "amount"
    contract <- parse (Parser.parseToValue Parser.contract) =<< statementToCode g block "contract"
    pure (Case (Deposit accountId party tok amount) contract)
  blockDefinition ChoiceActionType g block = do
    choiceName <- getFieldValue block "choice_name"
    choiceOwner <- parse (Parser.parseToValue Parser.party) =<< statementToCode g block "choice_owner"
    let
      choiceId = ChoiceId choiceName choiceOwner

      inputs = inputList block
    boundsInput <- note "No Input with name \"bound\" found" $ getInputWithName inputs "bounds"
    topboundBlock <- getBlockInputConnectedTo boundsInput
    bounds <- boundsDefinition g topboundBlock
    contract <- parse (Parser.parseToValue Parser.contract) =<< statementToCode g block "contract"
    pure (Case (Choice choiceId bounds) contract)
  blockDefinition NotifyActionType g block = do
    observation <- parse (Parser.parseToValue Parser.observation) =<< statementToCode g block "observation"
    contract <- parse (Parser.parseToValue Parser.contract) =<< statementToCode g block "contract"
    pure (Case (Notify observation) contract)

instance hasBlockDefinitionPayee :: HasBlockDefinition PayeeType Payee where
  blockDefinition AccountPayeeType g block = do
    accountNumber <- parse Parser.bigInteger =<< getFieldValue block "account_number"
    accountOwner <- parse (Parser.parseToValue Parser.party) =<< statementToCode g block "account_owner"
    let
      accountId = AccountId accountNumber accountOwner
    pure (Account accountId)
  blockDefinition PartyPayeeType g block = do
    party <- parse (Parser.parseToValue Parser.party) =<< statementToCode g block "party"
    pure (Party party)

instance hasBlockDefinitionParty :: HasBlockDefinition PartyType Party where
  blockDefinition PKPartyType g block = do
    pk <- getFieldValue block "pubkey"
    pure (PK pk)
  blockDefinition RolePartyType g block = do
    role <- getFieldValue block "role"
    pure (Role role)

instance hasBlockDefinitionToken :: HasBlockDefinition TokenType Token where
  blockDefinition CustomTokenType g block = do
    currSym <- getFieldValue block "currency_symbol"
    tokName <- getFieldValue block "token_name"
    pure (Token currSym tokName)

instance hasBlockDefinitionContract :: HasBlockDefinition ContractType Contract where
  blockDefinition CloseContractType _ _ = pure Close
  blockDefinition PayContractType g block = do
    accountNumber <- parse Parser.bigInteger =<< getFieldValue block "account_number"
    accountOwner <- parse (Parser.parseToValue Parser.party) =<< statementToCode g block "account_owner"
    tok <- parse (Parser.parseToValue Parser.token) =<< statementToCode g block "token"
    let
      accountId = AccountId accountNumber accountOwner
    payee <- parse (Parser.parseToValue Parser.payee) =<< statementToCode g block "payee"
    value <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "amount"
    contract <- parse (Parser.parseToValue Parser.contract) =<< statementToCode g block "contract"
    pure (Pay accountId payee tok value contract)
  blockDefinition IfContractType g block = do
    observation <- parse (Parser.parseToValue Parser.observation) =<< statementToCode g block "observation"
    contract1 <- parse (Parser.parseToValue Parser.contract) =<< statementToCode g block "contract1"
    contract2 <- parse (Parser.parseToValue Parser.contract) =<< statementToCode g block "contract2"
    pure (If observation contract1 contract2)
  blockDefinition WhenContractType g block = do
    let
      inputs = inputList block
    casesInput <- note "No Input with name \"case\" found" $ getInputWithName inputs "case"
    let
      eTopCaseBlock = getBlockInputConnectedTo casesInput
    cases <- case eTopCaseBlock of
      Either.Right topCaseBlock -> casesDefinition g topCaseBlock
      Either.Left _ -> pure []
    timeout <- parse Parser.timeout =<< getFieldValue block "timeout"
    contract <- parse (Parser.parseToValue Parser.contract) =<< statementToCode g block "contract"
    pure (When cases timeout contract)
  blockDefinition LetContractType g block = do
    valueId <- ValueId <$> getFieldValue block "value_id"
    value <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value"
    contract <- parse (Parser.parseToValue Parser.contract) =<< statementToCode g block "contract"
    pure (Let valueId value contract)

instance hasBlockDefinitionObservation :: HasBlockDefinition ObservationType Observation where
  blockDefinition AndObservationType g block = do
    observation1 <- parse (Parser.parseToValue Parser.observation) =<< statementToCode g block "observation1"
    observation2 <- parse (Parser.parseToValue Parser.observation) =<< statementToCode g block "observation2"
    pure (AndObs observation1 observation2)
  blockDefinition OrObservationType g block = do
    observation1 <- parse (Parser.parseToValue Parser.observation) =<< statementToCode g block "observation1"
    observation2 <- parse (Parser.parseToValue Parser.observation) =<< statementToCode g block "observation2"
    pure (OrObs observation1 observation2)
  blockDefinition NotObservationType g block = do
    observation <- parse (Parser.parseToValue Parser.observation) =<< statementToCode g block "observation"
    pure (NotObs observation)
  blockDefinition ChoseSomethingObservationType g block = do
    choiceName <- getFieldValue block "choice_name"
    choiceOwner <- parse (Parser.parseToValue Parser.party) =<< statementToCode g block "choice_owner"
    let
      choiceId = ChoiceId choiceName choiceOwner
    pure (ChoseSomething choiceId)
  blockDefinition ValueGEObservationType g block = do
    value1 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value1"
    value2 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value2"
    pure (ValueGE value1 value2)
  blockDefinition ValueGTObservationType g block = do
    value1 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value1"
    value2 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value2"
    pure (ValueGT value1 value2)
  blockDefinition ValueLEObservationType g block = do
    value1 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value1"
    value2 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value2"
    pure (ValueLE value1 value2)
  blockDefinition ValueLTObservationType g block = do
    value1 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value1"
    value2 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value2"
    pure (ValueLT value1 value2)
  blockDefinition ValueEQObservationType g block = do
    value1 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value1"
    value2 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value2"
    pure (ValueEQ value1 value2)
  blockDefinition TrueObservationType g block = pure TrueObs
  blockDefinition FalseObservationType g block = pure FalseObs

instance hasBlockDefinitionValue :: HasBlockDefinition ValueType Value where
  blockDefinition AvailableMoneyValueType g block = do
    accountNumber <- parse Parser.bigInteger =<< getFieldValue block "account_number"
    accountOwner <- parse (Parser.parseToValue Parser.party) =<< statementToCode g block "account_owner"
    tok <- parse (Parser.parseToValue Parser.token) =<< statementToCode g block "token"
    let
      accountId = AccountId accountNumber accountOwner
    pure (AvailableMoney accountId tok)
  blockDefinition ConstantValueType g block = do
    constant <- parse Parser.bigInteger =<< getFieldValue block "constant"
    pure (Constant constant)
  blockDefinition NegValueValueType g block = do
    value <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value"
    pure (NegValue value)
  blockDefinition AddValueValueType g block = do
    value1 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value1"
    value2 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value2"
    pure (AddValue value1 value2)
  blockDefinition SubValueValueType g block = do
    value1 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value1"
    value2 <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value2"
    pure (SubValue value1 value2)
  blockDefinition ChoiceValueValueType g block = do
    choiceName <- getFieldValue block "choice_name"
    choiceOwner <- parse (Parser.parseToValue Parser.party) =<< statementToCode g block "choice_owner"
    let
      choiceId = ChoiceId choiceName choiceOwner
    value <- parse (Parser.parseToValue Parser.value) =<< statementToCode g block "value"
    pure (ChoiceValue choiceId value)
  blockDefinition SlotIntervalStartValueType g block = pure SlotIntervalStart
  blockDefinition SlotIntervalEndValueType g block = pure SlotIntervalEnd
  blockDefinition UseValueValueType g block = do
    valueId <- ValueId <$> getFieldValue block "value_id"
    pure (UseValue valueId)

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

getNextInput :: forall r. STRef r Block -> ST r (Maybe Input)
getNextInput blockRef = do
  block <- STRef.read blockRef
  let
    inputs = inputList block

    nextConInputs = filter (\input -> inputType input == 5) inputs
  pure (head nextConInputs)

inputToBlockly :: forall a r. ToBlockly a => NewBlockFunction r -> (STRef r Workspace) -> STRef r Block -> String -> a -> ST r Unit
inputToBlockly newBlock workspaceRef blockRef name value = do
  block <- STRef.read blockRef
  case Array.find (\i -> inputName i == name) (inputList block) of
    Nothing -> pure unit
    Just input -> toBlockly newBlock workspaceRef input value

class ToBlockly a where
  toBlockly :: forall r. NewBlockFunction r -> STRef r Workspace -> Input -> a -> ST r Unit

instance toBlocklyPayee :: ToBlockly Payee where
  toBlockly newBlock workspace input (Account (AccountId accountNumber accountOwner)) = do
    block <- newBlock workspace (show AccountPayeeType)
    connectToOutput block input
    setField block "account_number" (show accountNumber)
    inputToBlockly newBlock workspace block "account_owner" accountOwner
  toBlockly newBlock workspace input (Party party) = do
    block <- newBlock workspace (show PartyPayeeType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "party" party

instance toBlocklyParty :: ToBlockly Party where
  toBlockly newBlock workspace input (PK pk) = do
    block <- newBlock workspace (show PKPartyType)
    connectToOutput block input
    setField block "pubkey" pk
  toBlockly newBlock workspace input (Role role) = do
    block <- newBlock workspace (show RolePartyType)
    connectToOutput block input
    setField block "role" role

instance toBlocklyToken :: ToBlockly Token where
  toBlockly newBlock workspace input (Token currSym tokName) = do
    block <- newBlock workspace (show CustomTokenType)
    connectToOutput block input
    setField block "currency_symbol" currSym
    setField block "token_name" tokName

nextBound :: forall r. NewBlockFunction r -> STRef r Workspace -> Connection -> Array Bound -> ST r Unit
nextBound newBlock workspace fromConnection bounds = do
  case uncons bounds of
    Nothing -> pure unit
    Just { head: (Bound from to), tail } -> do
      block <- newBlock workspace (show BoundsType)
      setField block "from" (show from)
      setField block "to" (show to)
      toConnection <- previousConnection block
      connect fromConnection toConnection
      nextFromConnection <- nextConnection block
      nextBound newBlock workspace nextFromConnection tail

instance toBlocklyBounds :: ToBlockly (Array Bound) where
  toBlockly newBlock workspace input bounds = do
    case uncons bounds of
      Nothing -> pure unit
      Just { head: (Bound from to), tail } -> do
        block <- newBlock workspace (show BoundsType)
        setField block "from" (show from)
        setField block "to" (show to)
        connectToPrevious block input
        fromConnection <- nextConnection block
        nextBound newBlock workspace fromConnection tail

oneCaseToBlockly :: forall r. NewBlockFunction r -> STRef r Workspace -> Case -> ST r (STRef r Block)
oneCaseToBlockly newBlock workspace (Case (Deposit (AccountId accountNumber accountOwner) party tok value) cont) = do
  block <- newBlock workspace (show DepositActionType)
  setField block "account_number" (show accountNumber)
  inputToBlockly newBlock workspace block "account_owner" accountOwner
  inputToBlockly newBlock workspace block "token" tok
  inputToBlockly newBlock workspace block "party" party
  inputToBlockly newBlock workspace block "amount" value
  inputToBlockly newBlock workspace block "contract" cont
  pure block

oneCaseToBlockly newBlock workspace (Case (Choice (ChoiceId choiceName choiceOwner) bounds) cont) = do
  block <- newBlock workspace (show ChoiceActionType)
  setField block "choice_name" choiceName
  inputToBlockly newBlock workspace block "choice_owner" choiceOwner
  inputToBlockly newBlock workspace block "bounds" bounds
  inputToBlockly newBlock workspace block "contract" cont
  pure block

oneCaseToBlockly newBlock workspace (Case (Notify observation) cont) = do
  block <- newBlock workspace (show NotifyActionType)
  inputToBlockly newBlock workspace block "observation" observation
  inputToBlockly newBlock workspace block "contract" cont
  pure block

nextCase :: forall r. NewBlockFunction r -> STRef r Workspace -> Connection -> Array Case -> ST r Unit
nextCase newBlock workspace fromConnection cases = do
  case uncons cases of
    Nothing -> pure unit
    Just { head: (Case action contract), tail } -> do
      block <- oneCaseToBlockly newBlock workspace (Case action contract)
      toConnection <- previousConnection block
      connect fromConnection toConnection
      nextFromConnection <- nextConnection block
      nextCase newBlock workspace nextFromConnection tail

instance toBlocklyCases :: ToBlockly (Array Case) where
  toBlockly newBlock workspace input cases = do
    case uncons cases of
      Nothing -> pure unit
      Just { head: (Case action contract), tail } -> do
        block <- oneCaseToBlockly newBlock workspace (Case action contract)
        connectToPrevious block input
        fromConnection <- nextConnection block
        nextCase newBlock workspace fromConnection tail

instance toBlocklyContract :: ToBlockly Contract where
  toBlockly newBlock workspace input Close = do
    block <- newBlock workspace (show CloseContractType)
    connectToPrevious block input
  toBlockly newBlock workspace input (Pay (AccountId accountNumber accountOwner) payee tok value contract) = do
    block <- newBlock workspace (show PayContractType)
    connectToPrevious block input
    setField block "account_number" (show accountNumber)
    inputToBlockly newBlock workspace block "account_owner" accountOwner
    inputToBlockly newBlock workspace block "token" tok
    inputToBlockly newBlock workspace block "payee" payee
    inputToBlockly newBlock workspace block "amount" value
    inputToBlockly newBlock workspace block "contract" contract
  toBlockly newBlock workspace input (If observation contract1 contract2) = do
    block <- newBlock workspace (show IfContractType)
    connectToPrevious block input
    inputToBlockly newBlock workspace block "observation" observation
    inputToBlockly newBlock workspace block "contract1" contract1
    inputToBlockly newBlock workspace block "contract2" contract2
  toBlockly newBlock workspace input (When cases timeout contract) = do
    block <- newBlock workspace (show WhenContractType)
    connectToPrevious block input
    inputToBlockly newBlock workspace block "case" cases
    setField block "timeout" (show timeout)
    inputToBlockly newBlock workspace block "contract" contract
  toBlockly newBlock workspace input (Let (ValueId valueId) value contract) = do
    block <- newBlock workspace (show LetContractType)
    connectToPrevious block input
    setField block "value_id" valueId
    inputToBlockly newBlock workspace block "value" value
    inputToBlockly newBlock workspace block "contract" contract

instance toBlocklyObservation :: ToBlockly Observation where
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
  toBlockly newBlock workspace input (ChoseSomething (ChoiceId choiceName choiceOwner)) = do
    block <- newBlock workspace (show ChoseSomethingObservationType)
    connectToOutput block input
    setField block "choice_name" choiceName
    inputToBlockly newBlock workspace block "choice_owner" choiceOwner
  toBlockly newBlock workspace input (ValueGE v1 v2) = do
    block <- newBlock workspace (show ValueGEObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (ValueGT v1 v2) = do
    block <- newBlock workspace (show ValueGTObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (ValueLT v1 v2) = do
    block <- newBlock workspace (show ValueLTObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (ValueLE v1 v2) = do
    block <- newBlock workspace (show ValueLEObservationType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (ValueEQ v1 v2) = do
    block <- newBlock workspace (show ValueEQObservationType)
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
  toBlockly newBlock workspace input (AvailableMoney (AccountId accountNumber accountOwner) tok) = do
    block <- newBlock workspace (show AvailableMoneyValueType)
    connectToOutput block input
    setField block "account_number" (show accountNumber)
    inputToBlockly newBlock workspace block "account_owner" accountOwner
    inputToBlockly newBlock workspace block "token" tok
  toBlockly newBlock workspace input (Constant v) = do
    block <- newBlock workspace (show ConstantValueType)
    connectToOutput block input
    setField block "constant" (show v)
  toBlockly newBlock workspace input (NegValue v) = do
    block <- newBlock workspace (show NegValueValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value" v
  toBlockly newBlock workspace input (AddValue v1 v2) = do
    block <- newBlock workspace (show AddValueValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (SubValue v1 v2) = do
    block <- newBlock workspace (show SubValueValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (ChoiceValue (ChoiceId choiceName choiceOwner) value) = do
    block <- newBlock workspace (show ChoiceValueValueType)
    connectToOutput block input
    setField block "choice_name" choiceName
    inputToBlockly newBlock workspace block "choice_owner" choiceOwner
    inputToBlockly newBlock workspace block "value" value
  toBlockly newBlock workspace input SlotIntervalStart = do
    block <- newBlock workspace (show SlotIntervalStartValueType)
    connectToOutput block input
  toBlockly newBlock workspace input SlotIntervalEnd = do
    block <- newBlock workspace (show SlotIntervalEndValueType)
    connectToOutput block input
  toBlockly newBlock workspace input (UseValue (ValueId valueId)) = do
    block <- newBlock workspace (show UseValueValueType)
    connectToOutput block input
    setField block "value_id" valueId
