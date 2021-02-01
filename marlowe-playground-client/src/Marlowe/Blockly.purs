module Marlowe.Blockly where

import Prelude
import Blockly.Generator (Connection, Generator, Input, NewBlockFunction, clearWorkspace, connect, connectToOutput, connectToPrevious, fieldName, fieldRow, getBlockInputConnectedTo, getFieldValue, getInputWithName, getType, inputList, inputName, inputType, insertGeneratorFunction, mkGenerator, nextBlock, nextConnection, previousConnection, setFieldText, statementToCode)
import Blockly.Internal (AlignDirection(..), Arg(..), BlockDefinition(..), block, blockType, category, colour, defaultBlockDefinition, getBlockById, initializeWorkspace, name, render, style, x, xml, y)
import Blockly.Types (Block, Blockly, BlocklyState, Workspace)
import Control.Alternative ((<|>))
import Data.Array (filter, head, uncons, (:))
import Data.Array as Array
import Data.Bifunctor (lmap, rmap)
import Data.Either (Either, note)
import Data.Either as Either
import Data.Enum (class BoundedEnum, class Enum, upFromIncluding)
import Data.Foldable (for_)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Bounded (genericBottom, genericTop)
import Data.Generic.Rep.Enum (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Generic.Rep.Show (genericShow)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse, traverse_)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Halogen.HTML (HTML)
import Halogen.HTML.Properties (id_)
import Marlowe.Holes (Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Observation(..), Party(..), Payee(..), Term(..), TermWrapper(..), Token(..), Value(..), ValueId(..), mkDefaultTerm, mkDefaultTermWrapper)
import Marlowe.Parser as Parser
import Marlowe.Semantics (Rational(..))
import Record (merge)
import Text.Parsing.StringParser (Parser)
import Text.Parsing.StringParser.Basic (parens, runParser')
import Type.Proxy (Proxy(..))

rootBlockName :: String
rootBlockName = "root_contract"

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
  = AdaTokenType
  | CustomTokenType

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
  | AssertContractType
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
  | MulValueValueType
  | ScaleValueType
  | ChoiceValueValueType
  | SlotIntervalStartValueType
  | SlotIntervalEndValueType
  | UseValueValueType
  | CondObservationValueValueType

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

contractColour :: String
contractColour = "#a380bc"

boundsColour :: String
boundsColour = "#1a7b84"

actionColour :: String
actionColour = "#e6aa00"

observationColour :: String
observationColour = "#1fc1c3"

valueColour :: String
valueColour = "#eb2256"

payeeColour :: String
payeeColour = "#709cf0"

partyColour :: String
partyColour = "#f69ab2"

tokenColour :: String
tokenColour = "#eb4a22"

blockColour :: BlockType -> String
blockColour BaseContractType = contractColour

blockColour BoundsType = boundsColour

blockColour (ActionType _) = actionColour

blockColour (ContractType _) = contractColour

blockColour (ObservationType _) = observationColour

blockColour (ValueType _) = valueColour

blockColour (PayeeType _) = payeeColour

blockColour (PartyType _) = partyColour

blockColour (TokenType _) = tokenColour

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
        , colour: blockColour BaseContractType
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
        , colour: blockColour BoundsType
        , previousStatement: Just (show BoundsType)
        , nextStatement: Just (show BoundsType)
        }
        defaultBlockDefinition

-- Action
toDefinition blockType@(ActionType DepositActionType) =
  BlockDefinition
    $ merge
        { type: show DepositActionType
        , message0: "Deposit %1 by %2 the amount of %3 currency %4 into account of %5 continue as %6 %7"
        , args0:
            [ DummyCentre
            , Value { name: "from_party", check: "party", align: Right }
            , Value { name: "value", check: "value", align: Right }
            , Value { name: "token", check: "token", align: Right }
            , Value { name: "party", check: "party", align: Right }
            , DummyLeft
            , Statement { name: "contract", check: (show BaseContractType), align: Right }
            ]
        , colour: blockColour blockType
        , previousStatement: Just "ActionType"
        , nextStatement: Just "ActionType"
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition blockType@(ActionType ChoiceActionType) =
  BlockDefinition
    $ merge
        { type: show ChoiceActionType
        , message0: "Choice name %1 %2 choice owner %3 choice bounds %4 %5 continue as %6 %7"
        , args0:
            [ Input { name: "choice_name", text: "name", spellcheck: false }
            , DummyLeft
            , Value { name: "party", check: "party", align: Right }
            , DummyLeft
            , Statement { name: "bounds", check: (show BoundsType), align: Right }
            , DummyLeft
            , Statement { name: "contract", check: (show BaseContractType), align: Right }
            ]
        , colour: blockColour blockType
        , previousStatement: Just "ActionType"
        , nextStatement: Just "ActionType"
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition blockType@(ActionType NotifyActionType) =
  BlockDefinition
    $ merge
        { type: show NotifyActionType
        , message0: "Notification of %1 continue as %2 %3"
        , args0:
            [ Value { name: "observation", check: "observation", align: Right }
            , DummyLeft
            , Statement { name: "contract", check: (show BaseContractType), align: Right }
            ]
        , colour: blockColour blockType
        , previousStatement: Just "ActionType"
        , nextStatement: Just "ActionType"
        , inputsInline: Just false
        }
        defaultBlockDefinition

-- Payee
toDefinition blockType@(PayeeType AccountPayeeType) =
  BlockDefinition
    $ merge
        { type: show AccountPayeeType
        , message0: "Account of %1 %2"
        , args0:
            [ DummyLeft
            , Value { name: "party", check: "party", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "payee"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(PayeeType PartyPayeeType) =
  BlockDefinition
    $ merge
        { type: show PartyPayeeType
        , message0: "Party %1"
        , args0:
            [ Value { name: "party", check: "party", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "payee"
        , inputsInline: Just true
        }
        defaultBlockDefinition

-- Party
toDefinition blockType@(PartyType PKPartyType) =
  BlockDefinition
    $ merge
        { type: show PKPartyType
        , message0: "Public Key %1"
        , args0:
            [ Input { name: "pubkey", text: "pubkey", spellcheck: false }
            ]
        , colour: blockColour blockType
        , output: Just "party"
        , inputsInline: Just true
        }
        defaultBlockDefinition

-- Ada Token type
toDefinition blockType@(TokenType AdaTokenType) =
  BlockDefinition
    $ merge
        { type: show AdaTokenType
        , message0: "ada"
        , args0: []
        , colour: blockColour blockType
        , output: Just "token"
        , inputsInline: Just true
        }
        defaultBlockDefinition

-- Custom Token type
toDefinition blockType@(TokenType CustomTokenType) =
  BlockDefinition
    $ merge
        { type: show CustomTokenType
        , message0: "Token with currency %1 and token name %2"
        , args0:
            [ Input { name: "currency_symbol", text: "", spellcheck: false }
            , Input { name: "token_name", text: "", spellcheck: false }
            ]
        , colour: blockColour blockType
        , output: Just "token"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(PartyType RolePartyType) =
  BlockDefinition
    $ merge
        { type: show RolePartyType
        , message0: "Role %1"
        , args0:
            [ Input { name: "role", text: "role", spellcheck: false }
            ]
        , colour: blockColour blockType
        , output: Just "party"
        , inputsInline: Just true
        }
        defaultBlockDefinition

-- Contracts
toDefinition blockType@(ContractType CloseContractType) =
  BlockDefinition
    $ merge
        { type: show CloseContractType
        , message0: "Close"
        , colour: blockColour blockType
        , previousStatement: Just (show BaseContractType)
        }
        defaultBlockDefinition

toDefinition blockType@(ContractType PayContractType) =
  BlockDefinition
    $ merge
        { type: show PayContractType
        , message0: "Pay %1 payee %2 the amount of %3 of currency %4 from account of %5 continue as %6 %7"
        , args0:
            [ DummyCentre
            , Value { name: "payee", check: "payee", align: Right }
            , Value { name: "value", check: "value", align: Right }
            , Value { name: "token", check: "token", align: Right }
            , Value { name: "party", check: "party", align: Right }
            , DummyLeft
            , Statement { name: "contract", check: (show BaseContractType), align: Right }
            ]
        , colour: blockColour blockType
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition blockType@(ContractType IfContractType) =
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
        , colour: blockColour blockType
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition blockType@(ContractType WhenContractType) =
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
        , colour: blockColour blockType
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        }
        defaultBlockDefinition

toDefinition blockType@(ContractType LetContractType) =
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
        , colour: blockColour blockType
        , previousStatement: Just (show BaseContractType)
        }
        defaultBlockDefinition

toDefinition blockType@(ContractType AssertContractType) =
  BlockDefinition
    $ merge
        { type: show AssertContractType
        , message0: "Assert %1 check that %2 continue as %3 %4"
        , args0:
            [ DummyCentre
            , Value { name: "observation", check: "observation", align: Right }
            , DummyLeft
            , Statement { name: "contract", check: (show BaseContractType), align: Right }
            ]
        , colour: blockColour blockType
        , previousStatement: Just (show BaseContractType)
        , inputsInline: Just false
        }
        defaultBlockDefinition

-- Observations
toDefinition blockType@(ObservationType AndObservationType) =
  BlockDefinition
    $ merge
        { type: show AndObservationType
        , message0: "%1 and %2"
        , args0:
            [ Value { name: "observation1", check: "observation", align: Right }
            , Value { name: "observation2", check: "observation", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ObservationType OrObservationType) =
  BlockDefinition
    $ merge
        { type: show OrObservationType
        , message0: "%1 or %2"
        , args0:
            [ Value { name: "observation1", check: "observation", align: Right }
            , Value { name: "observation2", check: "observation", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ObservationType NotObservationType) =
  BlockDefinition
    $ merge
        { type: show NotObservationType
        , message0: "not %1"
        , args0:
            [ Value { name: "observation", check: "observation", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ObservationType ChoseSomethingObservationType) =
  BlockDefinition
    $ merge
        { type: show ChoseSomethingObservationType
        , message0: "party %1 made choice %2"
        , args0:
            [ Value { name: "party", check: "party", align: Right }
            , Input { name: "choice_name", text: "name", spellcheck: false }
            ]
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ObservationType ValueGEObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueGEObservationType
        , message0: "value %1 is greater than or equal to %2"
        , args0:
            [ Value { name: "value1", check: "value", align: Right }
            , Value { name: "value2", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ObservationType ValueGTObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueGTObservationType
        , message0: "value %1 is greater than %2"
        , args0:
            [ Value { name: "value1", check: "value", align: Right }
            , Value { name: "value2", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ObservationType ValueLEObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueLEObservationType
        , message0: "value %1 is less than or equal to %2"
        , args0:
            [ Value { name: "value1", check: "value", align: Right }
            , Value { name: "value2", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ObservationType ValueLTObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueLTObservationType
        , message0: "value %1 is less than %2"
        , args0:
            [ Value { name: "value1", check: "value", align: Right }
            , Value { name: "value2", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ObservationType ValueEQObservationType) =
  BlockDefinition
    $ merge
        { type: show ValueEQObservationType
        , message0: "value %1 is equal to %2"
        , args0:
            [ Value { name: "value1", check: "value", align: Right }
            , Value { name: "value2", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ObservationType TrueObservationType) =
  BlockDefinition
    $ merge
        { type: show TrueObservationType
        , message0: "true"
        , lastDummyAlign0: Centre
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ObservationType FalseObservationType) =
  BlockDefinition
    $ merge
        { type: show FalseObservationType
        , message0: "false"
        , lastDummyAlign0: Centre
        , colour: blockColour blockType
        , output: Just "observation"
        , inputsInline: Just true
        }
        defaultBlockDefinition

-- Values
toDefinition blockType@(ValueType AvailableMoneyValueType) =
  BlockDefinition
    $ merge
        { type: show AvailableMoneyValueType
        , message0: "Available currency %1 from account of %2 %3 %4 %5"
        , args0:
            [ Value { name: "token", check: "token", align: Right }
            , DummyRight
            , DummyRight
            , Value { name: "party", check: "party", align: Right }
            , DummyRight
            ]
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType ConstantValueType) =
  BlockDefinition
    $ merge
        { type: show ConstantValueType
        , message0: "Constant %1"
        , args0:
            [ Number { name: "constant", value: 1.0, min: Nothing, max: Nothing, precision: Nothing }
            ]
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType NegValueValueType) =
  BlockDefinition
    $ merge
        { type: show NegValueValueType
        , message0: "- %1"
        , args0:
            [ Value { name: "value", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType AddValueValueType) =
  BlockDefinition
    $ merge
        { type: show AddValueValueType
        , message0: "%1 + %2"
        , args0:
            [ Value { name: "value1", check: "value", align: Right }
            , Value { name: "value2", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType MulValueValueType) =
  BlockDefinition
    $ merge
        { type: show MulValueValueType
        , message0: "%1 * %2"
        , args0:
            [ Value { name: "value1", check: "value", align: Right }
            , Value { name: "value2", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType CondObservationValueValueType) =
  BlockDefinition
    $ merge
        { type: show CondObservationValueValueType
        , message0: "if %1 then %2 else %3"
        , args0:
            [ Value { name: "condition", check: "observation", align: Right }
            , Value { name: "then", check: "value", align: Right }
            , Value { name: "else", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType SubValueValueType) =
  BlockDefinition
    $ merge
        { type: show SubValueValueType
        , message0: "%1 - %2"
        , args0:
            [ Value { name: "value1", check: "value", align: Right }
            , Value { name: "value2", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType ScaleValueType) =
  BlockDefinition
    $ merge
        { type: show ScaleValueType
        , message0: "(%1 / %2) * %3"
        , args0:
            [ Number { name: "numerator", value: 1.0, min: Nothing, max: Nothing, precision: Nothing }
            , Number { name: "denominator", value: 1.0, min: Just 1.0, max: Nothing, precision: Nothing }
            , Value { name: "value", check: "value", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType ChoiceValueValueType) =
  BlockDefinition
    $ merge
        { type: show ChoiceValueValueType
        , message0: "Choice %1 by %2"
        , args0:
            [ Input { name: "choice_name", text: "name", spellcheck: false }
            , Value { name: "party", check: "party", align: Right }
            ]
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType SlotIntervalStartValueType) =
  BlockDefinition
    $ merge
        { type: show SlotIntervalStartValueType
        , message0: "Slot Interval Start"
        , lastDummyAlign0: Centre
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType SlotIntervalEndValueType) =
  BlockDefinition
    $ merge
        { type: show SlotIntervalEndValueType
        , message0: "Slot Interval End"
        , lastDummyAlign0: Centre
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toDefinition blockType@(ValueType UseValueValueType) =
  BlockDefinition
    $ merge
        { type: show UseValueValueType
        , message0: "Use name %1"
        , args0:
            [ Input { name: "value_id", text: "value", spellcheck: false }
            ]
        , colour: blockColour blockType
        , output: Just "value"
        , inputsInline: Just true
        }
        defaultBlockDefinition

toolbox :: forall a b. HTML a b
toolbox =
  xml [ id_ "blocklyToolbox", style "display:none" ]
    [ category [ name "Contracts", colour contractColour ] (map mkBlock contractTypes)
    , category [ name "Observations", colour observationColour ] (map mkBlock observationTypes)
    , category [ name "Actions", colour actionColour ] (map mkBlock actionTypes)
    , category [ name "Values", colour valueColour ] (map mkBlock valueTypes)
    , category [ name "Payee", colour payeeColour ] (map mkBlock payeeTypes)
    , category [ name "Party", colour partyColour ] (map mkBlock partyTypes)
    , category [ name "Token", colour tokenColour ] (map mkBlock tokenTypes)
    , category [ name "Bounds", colour boundsColour ] (map mkBlock [ BoundsType ])
    ]
  where
  mkBlock :: forall t. Show t => t -> _
  mkBlock t = block [ blockType (show t) ] []

workspaceBlocks :: forall a b. HTML a b
workspaceBlocks =
  xml [ id_ "workspaceBlocks", style "display:none" ]
    [ block [ blockType (show BaseContractType), x "13", y "187", id_ rootBlockName ] []
    ]

parse :: forall a. Parser a -> String -> Either String a
parse p = lmap show <<< runParser' (parens p <|> p)

buildGenerator :: Blockly -> Effect Generator
buildGenerator blockly = do
  generator <- mkGenerator blockly "Marlowe"
  let
    mkGenFun :: forall a t. Show a => Show t => t -> (Block -> Either String a) -> Effect Unit
    mkGenFun blockType f = insertGeneratorFunction generator (show blockType) ((rmap show) <<< f)
  traverse_ (\t -> mkGenFun t (baseContractDefinition generator)) [ BaseContractType ]
  traverse_ (\t -> mkGenFun t (blockDefinition t generator)) contractTypes
  traverse_ (\t -> mkGenFun t (blockDefinition t generator)) payeeTypes
  traverse_ (\t -> mkGenFun t (blockDefinition t generator)) partyTypes
  traverse_ (\t -> mkGenFun t (blockDefinition t generator)) tokenTypes
  traverse_ (\t -> mkGenFun t (blockDefinition t generator)) observationTypes
  traverse_ (\t -> mkGenFun t (blockDefinition t generator)) valueTypes
  traverse_ (\t -> mkGenFun t (blockDefinition t generator)) actionTypes
  traverse_ (\t -> mkGenFun t (boundsDefinition generator)) [ BoundsType ]
  pure generator

class HasBlockDefinition a b | a -> b where
  blockDefinition :: a -> Generator -> Block -> Either String b

baseContractDefinition :: Generator -> Block -> Either String (Term Contract)
baseContractDefinition g block = case statementToCode g block (show BaseContractType) of
  Either.Left _ -> pure $ Hole "contract" Proxy zero
  Either.Right s -> parse (mkDefaultTerm <$> Parser.contract) s

getAllBlocks :: Block -> Array Block
getAllBlocks currentBlock =
  currentBlock
    : ( case nextBlock currentBlock of
          Nothing -> []
          Just nextBlock' -> getAllBlocks nextBlock'
      )

caseDefinition :: Generator -> Block -> Either String (Term Case)
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

casesDefinition :: Generator -> Block -> Either String (Array (Term Case))
casesDefinition g block = traverse (caseDefinition g) (getAllBlocks block)

boundDefinition :: Generator -> Block -> Either String (Term Bound)
boundDefinition g block = do
  from <- parse Parser.bigInteger =<< getFieldValue block "from"
  to <- parse Parser.bigInteger =<< getFieldValue block "to"
  pure (mkDefaultTerm (Bound from to))

boundsDefinition :: Generator -> Block -> Either String (Array (Term Bound))
boundsDefinition g block = traverse (boundDefinition g) (getAllBlocks block)

statementToTerm :: forall a. Generator -> Block -> String -> Parser a -> Either String (Term a)
statementToTerm g block name p = case statementToCode g block name of
  Either.Left _ -> pure $ Hole name Proxy zero
  Either.Right s -> parse (mkDefaultTerm <$> p) s

instance hasBlockDefinitionAction :: HasBlockDefinition ActionType (Term Case) where
  blockDefinition DepositActionType g block = do
    accountOwner <- statementToTerm g block "party" Parser.partyExtended
    tok <- statementToTerm g block "token" Parser.token
    party <- statementToTerm g block "from_party" Parser.partyExtended
    amount <- statementToTerm g block "value" (Parser.value unit)
    contract <- statementToTerm g block "contract" Parser.contract
    pure $ mkDefaultTerm (Case (mkDefaultTerm (Deposit accountOwner party tok amount)) contract)
  blockDefinition ChoiceActionType g block = do
    choiceName <- getFieldValue block "choice_name"
    choiceOwner <- statementToTerm g block "party" Parser.partyExtended
    let
      choiceId = ChoiceId choiceName choiceOwner

      inputs = inputList block
    boundsInput <- note "No Input with name \"bound\" found" $ getInputWithName inputs "bounds"
    let
      mTopboundBlock = getBlockInputConnectedTo boundsInput
    bounds <- case mTopboundBlock of
      Either.Left _ -> pure [ Hole "bounds" Proxy zero ]
      Either.Right topboundBlock -> boundsDefinition g topboundBlock
    contract <- statementToTerm g block "contract" Parser.contract
    pure $ mkDefaultTerm (Case (mkDefaultTerm (Choice choiceId bounds)) contract)
  blockDefinition NotifyActionType g block = do
    observation <- statementToTerm g block "observation" Parser.observation
    contract <- statementToTerm g block "contract" Parser.contract
    pure $ mkDefaultTerm (Case (mkDefaultTerm (Notify observation)) contract)

instance hasBlockDefinitionPayee :: HasBlockDefinition PayeeType (Term Payee) where
  blockDefinition AccountPayeeType g block = do
    accountOwner <- statementToTerm g block "party" Parser.partyExtended
    pure $ mkDefaultTerm (Account accountOwner)
  blockDefinition PartyPayeeType g block = do
    party <- statementToTerm g block "party" Parser.partyExtended
    pure $ mkDefaultTerm (Party party)

instance hasBlockDefinitionParty :: HasBlockDefinition PartyType (Term Party) where
  blockDefinition PKPartyType g block = do
    case getFieldValue block "pubkey" of
      Either.Left _ -> pure $ Hole "n" Proxy zero
      Either.Right pk -> pure $ mkDefaultTerm (PK pk)
  blockDefinition RolePartyType g block = do
    role <- getFieldValue block "role"
    pure $ mkDefaultTerm (Role role)

instance hasBlockDefinitionToken :: HasBlockDefinition TokenType (Term Token) where
  blockDefinition AdaTokenType g block = do
    pure $ mkDefaultTerm (Token "" "")
  blockDefinition CustomTokenType g block = do
    currSym <- getFieldValue block "currency_symbol"
    tokName <- getFieldValue block "token_name"
    pure $ mkDefaultTerm (Token currSym tokName)

instance hasBlockDefinitionContract :: HasBlockDefinition ContractType (Term Contract) where
  blockDefinition CloseContractType _ _ = pure $ mkDefaultTerm Close
  blockDefinition PayContractType g block = do
    accountOwner <- statementToTerm g block "party" Parser.partyExtended
    tok <- statementToTerm g block "token" Parser.token
    payee <- statementToTerm g block "payee" Parser.payeeExtended
    value <- statementToTerm g block "value" (Parser.value unit)
    contract <- statementToTerm g block "contract" Parser.contract
    pure $ mkDefaultTerm (Pay accountOwner payee tok value contract)
  blockDefinition IfContractType g block = do
    observation <- statementToTerm g block "observation" Parser.observation
    contract1 <- statementToTerm g block "contract1" Parser.contract
    contract2 <- statementToTerm g block "contract2" Parser.contract
    pure $ mkDefaultTerm (If observation contract1 contract2)
  blockDefinition WhenContractType g block = do
    let
      inputs = inputList block
    casesInput <- note "No Input with name \"case\" found" $ getInputWithName inputs "case"
    let
      eTopCaseBlock = getBlockInputConnectedTo casesInput
    cases <- case eTopCaseBlock of
      Either.Right topCaseBlock -> casesDefinition g topCaseBlock
      Either.Left _ -> pure []
    slot <- parse Parser.timeout =<< getFieldValue block "timeout"
    contract <- statementToTerm g block "contract" Parser.contract
    pure $ mkDefaultTerm (When cases slot contract)
  blockDefinition LetContractType g block = do
    valueId <- mkDefaultTermWrapper <<< ValueId <$> getFieldValue block "value_id"
    value <- statementToTerm g block "value" (Parser.value unit)
    contract <- statementToTerm g block "contract" Parser.contract
    pure $ mkDefaultTerm (Let valueId value contract)
  blockDefinition AssertContractType g block = do
    observation <- statementToTerm g block "observation" Parser.observation
    contract <- statementToTerm g block "contract" Parser.contract
    pure $ mkDefaultTerm (Assert observation contract)

instance hasBlockDefinitionObservation :: HasBlockDefinition ObservationType (Term Observation) where
  blockDefinition AndObservationType g block = do
    observation1 <- statementToTerm g block "observation1" Parser.observation
    observation2 <- statementToTerm g block "observation2" Parser.observation
    pure $ mkDefaultTerm (AndObs observation1 observation2)
  blockDefinition OrObservationType g block = do
    observation1 <- statementToTerm g block "observation1" Parser.observation
    observation2 <- statementToTerm g block "observation2" Parser.observation
    pure $ mkDefaultTerm (OrObs observation1 observation2)
  blockDefinition NotObservationType g block = do
    observation <- statementToTerm g block "observation" Parser.observation
    pure $ mkDefaultTerm (NotObs observation)
  blockDefinition ChoseSomethingObservationType g block = do
    choiceName <- getFieldValue block "choice_name"
    choiceOwner <- statementToTerm g block "party" Parser.partyExtended
    let
      choiceId = ChoiceId choiceName choiceOwner
    pure $ mkDefaultTerm (ChoseSomething choiceId)
  blockDefinition ValueGEObservationType g block = do
    value1 <- statementToTerm g block "value1" (Parser.value unit)
    value2 <- statementToTerm g block "value2" (Parser.value unit)
    pure $ mkDefaultTerm (ValueGE value1 value2)
  blockDefinition ValueGTObservationType g block = do
    value1 <- statementToTerm g block "value1" (Parser.value unit)
    value2 <- statementToTerm g block "value2" (Parser.value unit)
    pure $ mkDefaultTerm (ValueGT value1 value2)
  blockDefinition ValueLEObservationType g block = do
    value1 <- statementToTerm g block "value1" (Parser.value unit)
    value2 <- statementToTerm g block "value2" (Parser.value unit)
    pure $ mkDefaultTerm (ValueLE value1 value2)
  blockDefinition ValueLTObservationType g block = do
    value1 <- statementToTerm g block "value1" (Parser.value unit)
    value2 <- statementToTerm g block "value2" (Parser.value unit)
    pure $ mkDefaultTerm (ValueLT value1 value2)
  blockDefinition ValueEQObservationType g block = do
    value1 <- statementToTerm g block "value1" (Parser.value unit)
    value2 <- statementToTerm g block "value2" (Parser.value unit)
    pure $ mkDefaultTerm (ValueEQ value1 value2)
  blockDefinition TrueObservationType g block = pure $ mkDefaultTerm TrueObs
  blockDefinition FalseObservationType g block = pure $ mkDefaultTerm FalseObs

instance hasBlockDefinitionValue :: HasBlockDefinition ValueType (Term Value) where
  blockDefinition AvailableMoneyValueType g block = do
    accountOwner <- statementToTerm g block "party" Parser.partyExtended
    tok <- statementToTerm g block "token" Parser.token
    pure $ mkDefaultTerm (AvailableMoney accountOwner tok)
  blockDefinition ConstantValueType g block = do
    constant <- parse Parser.bigInteger =<< getFieldValue block "constant"
    pure $ mkDefaultTerm (Constant constant)
  blockDefinition NegValueValueType g block = do
    value <- statementToTerm g block "value" (Parser.value unit)
    pure $ mkDefaultTerm (NegValue value)
  blockDefinition AddValueValueType g block = do
    value1 <- statementToTerm g block "value1" (Parser.value unit)
    value2 <- statementToTerm g block "value2" (Parser.value unit)
    pure $ mkDefaultTerm (AddValue value1 value2)
  blockDefinition SubValueValueType g block = do
    value1 <- statementToTerm g block "value1" (Parser.value unit)
    value2 <- statementToTerm g block "value2" (Parser.value unit)
    pure $ mkDefaultTerm (SubValue value1 value2)
  blockDefinition MulValueValueType g block = do
    value1 <- statementToTerm g block "value1" (Parser.value unit)
    value2 <- statementToTerm g block "value2" (Parser.value unit)
    pure $ mkDefaultTerm (MulValue value1 value2)
  blockDefinition ScaleValueType g block = do
    numerator <- parse Parser.bigInteger =<< getFieldValue block "numerator"
    denominator <- parse Parser.bigInteger =<< getFieldValue block "denominator"
    value <- statementToTerm g block "value" (Parser.value unit)
    pure $ mkDefaultTerm (Scale (mkDefaultTermWrapper (Rational numerator denominator)) value)
  blockDefinition ChoiceValueValueType g block = do
    choiceName <- getFieldValue block "choice_name"
    choiceOwner <- statementToTerm g block "party" Parser.partyExtended
    let
      choiceId = ChoiceId choiceName choiceOwner
    pure $ mkDefaultTerm (ChoiceValue choiceId)
  blockDefinition SlotIntervalStartValueType g block = pure $ mkDefaultTerm SlotIntervalStart
  blockDefinition SlotIntervalEndValueType g block = pure $ mkDefaultTerm SlotIntervalEnd
  blockDefinition UseValueValueType g block = do
    valueId <- mkDefaultTermWrapper <<< ValueId <$> getFieldValue block "value_id"
    pure $ mkDefaultTerm (UseValue valueId)
  blockDefinition CondObservationValueValueType g block = do
    condition <- statementToTerm g block "condition" Parser.observation
    thn <- statementToTerm g block "then" (Parser.value unit)
    els <- statementToTerm g block "else" (Parser.value unit)
    pure $ mkDefaultTerm (Cond condition thn els)

buildBlocks :: NewBlockFunction -> BlocklyState -> Term Contract -> Effect Unit
buildBlocks newBlock bs contract = do
  clearWorkspace bs.workspace
  initializeWorkspace bs.blockly bs.workspace
  -- Get or create rootBlock
  mRootBlock <- getBlockById bs.workspace bs.rootBlockName
  rootBlock <- case mRootBlock of
    Nothing -> newBlock bs.workspace (show BaseContractType)
    Just block -> pure block
  let
    inputs = inputList rootBlock

    mInput = getInputWithName inputs (show BaseContractType)
  for_ mInput \input -> do
    toBlockly newBlock bs.workspace input contract
    render bs.workspace

setField :: Block -> String -> String -> Effect Unit
setField block name value = do
  let
    fields = inputList block >>= fieldRow
  case Array.find (\f -> fieldName f == name) fields of
    Nothing -> pure unit
    Just field -> setFieldText field value

getNextInput :: Block -> Effect (Maybe Input)
getNextInput block = do
  let
    inputs = inputList block

    nextConInputs = filter (\input -> inputType input == 5) inputs
  pure (head nextConInputs)

inputToBlockly :: forall a. ToBlockly a => NewBlockFunction -> Workspace -> Block -> String -> a -> Effect Unit
inputToBlockly newBlock workspace block name value = do
  case Array.find (\i -> inputName i == name) (inputList block) of
    Nothing -> pure unit
    Just input -> toBlockly newBlock workspace input value

class ToBlockly a where
  toBlockly :: NewBlockFunction -> Workspace -> Input -> a -> Effect Unit

instance toBlocklyTerm :: ToBlockly a => ToBlockly (Term a) where
  toBlockly newBlock workspace input (Term a _) = toBlockly newBlock workspace input a
  toBlockly newBlock workspace input _ = pure unit

instance toBlocklyPayee :: ToBlockly Payee where
  toBlockly newBlock workspace input (Account accountOwner) = do
    block <- newBlock workspace (show AccountPayeeType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "party" accountOwner
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
  toBlockly newBlock workspace input (Token "" "") = do
    block <- newBlock workspace (show AdaTokenType)
    connectToOutput block input
  toBlockly newBlock workspace input (Token currSym tokName) = do
    block <- newBlock workspace (show CustomTokenType)
    connectToOutput block input
    setField block "currency_symbol" currSym
    setField block "token_name" tokName

nextBound :: NewBlockFunction -> Workspace -> Connection -> Array (Term Bound) -> Effect Unit
nextBound newBlock workspace fromConnection bounds = do
  case uncons bounds of
    Nothing -> pure unit
    Just { head: (Hole _ _ _) } -> pure unit
    Just { head: (Term (Bound from to) _), tail } -> do
      block <- newBlock workspace (show BoundsType)
      setField block "from" (show from)
      setField block "to" (show to)
      toConnection <- previousConnection block
      connect fromConnection toConnection
      nextFromConnection <- nextConnection block
      nextBound newBlock workspace nextFromConnection tail

instance toBlocklyBounds :: ToBlockly (Array (Term Bound)) where
  toBlockly newBlock workspace input bounds = do
    case uncons bounds of
      Nothing -> pure unit
      Just { head: (Hole _ _ _) } -> pure unit
      Just { head: (Term (Bound from to) _), tail } -> do
        block <- newBlock workspace (show BoundsType)
        setField block "from" (show from)
        setField block "to" (show to)
        connectToPrevious block input
        fromConnection <- nextConnection block
        nextBound newBlock workspace fromConnection tail

oneCaseToBlockly :: NewBlockFunction -> Workspace -> Case -> Effect Block
oneCaseToBlockly newBlock workspace (Case (Term (Deposit accountOwner party tok value) _) cont) = do
  block <- newBlock workspace (show DepositActionType)
  inputToBlockly newBlock workspace block "party" accountOwner
  inputToBlockly newBlock workspace block "token" tok
  inputToBlockly newBlock workspace block "from_party" party
  inputToBlockly newBlock workspace block "value" value
  inputToBlockly newBlock workspace block "contract" cont
  pure block

oneCaseToBlockly newBlock workspace (Case (Term (Choice (ChoiceId choiceName choiceOwner) bounds) _) cont) = do
  block <- newBlock workspace (show ChoiceActionType)
  setField block "choice_name" choiceName
  inputToBlockly newBlock workspace block "party" choiceOwner
  inputToBlockly newBlock workspace block "bounds" bounds
  inputToBlockly newBlock workspace block "contract" cont
  pure block

oneCaseToBlockly newBlock workspace (Case (Term (Notify observation) _) cont) = do
  block <- newBlock workspace (show NotifyActionType)
  inputToBlockly newBlock workspace block "observation" observation
  inputToBlockly newBlock workspace block "contract" cont
  pure block

-- This is a temporary hack to cover a mismatch between blockly and holes
-- Case is a pair of an Action and a Contract so to make code easy to write in the simulation
-- we allow `Case ?action ?contract` however that doesn't fit in with Blockly which doesn't
-- have a `Case` block type but instead flattens things out. So in the case of `Case ?action ?contract`
-- we will allow blockly to fill in a default Notify action
oneCaseToBlockly newBlock workspace _ = newBlock workspace (show NotifyActionType)

nextCase :: NewBlockFunction -> Workspace -> Connection -> Array (Term Case) -> Effect Unit
nextCase newBlock workspace fromConnection cases = do
  case uncons cases of
    Nothing -> pure unit
    Just { head: (Hole _ _ _) } -> pure unit
    Just { head: (Term (Case action contract) _), tail } -> do
      block <- oneCaseToBlockly newBlock workspace (Case action contract)
      toConnection <- previousConnection block
      connect fromConnection toConnection
      nextFromConnection <- nextConnection block
      nextCase newBlock workspace nextFromConnection tail

instance toBlocklyCases :: ToBlockly (Array (Term Case)) where
  toBlockly newBlock workspace input cases = do
    case uncons cases of
      Nothing -> pure unit
      Just { head: (Hole _ _ _) } -> pure unit
      Just { head: (Term (Case action contract) _), tail } -> do
        block <- oneCaseToBlockly newBlock workspace (Case action contract)
        connectToPrevious block input
        fromConnection <- nextConnection block
        nextCase newBlock workspace fromConnection tail

instance toBlocklyContract :: ToBlockly Contract where
  toBlockly newBlock workspace input Close = do
    block <- newBlock workspace (show CloseContractType)
    connectToPrevious block input
  toBlockly newBlock workspace input (Pay accountOwner payee tok value contract) = do
    block <- newBlock workspace (show PayContractType)
    connectToPrevious block input
    inputToBlockly newBlock workspace block "party" accountOwner
    inputToBlockly newBlock workspace block "token" tok
    inputToBlockly newBlock workspace block "payee" payee
    inputToBlockly newBlock workspace block "value" value
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
  toBlockly newBlock workspace input (Let (TermWrapper (ValueId valueId) _) value contract) = do
    block <- newBlock workspace (show LetContractType)
    connectToPrevious block input
    setField block "value_id" valueId
    inputToBlockly newBlock workspace block "value" value
    inputToBlockly newBlock workspace block "contract" contract
  toBlockly newBlock workspace input (Assert observation contract) = do
    block <- newBlock workspace (show AssertContractType)
    connectToPrevious block input
    inputToBlockly newBlock workspace block "observation" observation
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
    inputToBlockly newBlock workspace block "party" choiceOwner
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
  toBlockly newBlock workspace input (AvailableMoney accountOwner tok) = do
    block <- newBlock workspace (show AvailableMoneyValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "party" accountOwner
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
  toBlockly newBlock workspace input (MulValue v1 v2) = do
    block <- newBlock workspace (show MulValueValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "value1" v1
    inputToBlockly newBlock workspace block "value2" v2
  toBlockly newBlock workspace input (Scale (TermWrapper (Rational numerator denominator) _) value) = do
    block <- newBlock workspace (show ScaleValueType)
    connectToOutput block input
    -- this makes sure the `-` sign is always on the top
    let
      (Tuple fixedNumerator fixedDenominator) =
        if denominator > zero then
          Tuple numerator denominator
        else
          Tuple (-numerator) (-denominator)
    setField block "numerator" (show fixedNumerator)
    setField block "denominator" (show fixedDenominator)
    inputToBlockly newBlock workspace block "value" value
  toBlockly newBlock workspace input (ChoiceValue (ChoiceId choiceName choiceOwner)) = do
    block <- newBlock workspace (show ChoiceValueValueType)
    connectToOutput block input
    setField block "choice_name" choiceName
    inputToBlockly newBlock workspace block "party" choiceOwner
  toBlockly newBlock workspace input SlotIntervalStart = do
    block <- newBlock workspace (show SlotIntervalStartValueType)
    connectToOutput block input
  toBlockly newBlock workspace input SlotIntervalEnd = do
    block <- newBlock workspace (show SlotIntervalEndValueType)
    connectToOutput block input
  toBlockly newBlock workspace input (UseValue (TermWrapper (ValueId valueId) _)) = do
    block <- newBlock workspace (show UseValueValueType)
    connectToOutput block input
    setField block "value_id" valueId
  toBlockly newBlock workspace input (Cond cond thn els) = do
    block <- newBlock workspace (show CondObservationValueValueType)
    connectToOutput block input
    inputToBlockly newBlock workspace block "condition" cond
    inputToBlockly newBlock workspace block "then" thn
    inputToBlockly newBlock workspace block "else" els
