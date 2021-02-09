-- Blockly lets you use workspaceToDom to inspect the Dom representation of the created blocks.
-- The result of calling the function is a Web.DOM.Element function which is "hard" to work with, as
-- it is the same API for working with HTML nodes.
--
-- This module offers some helpers so we can interpret the results of workspaceToDom in a single
-- effectful computation and later on work with the representation without the need for Effect.
--
-- The decision to use this intermediate representation instead of parsing the nodes directly was made
-- because both ActusBlockly and MarloweBlockly have the same representation.
--
--
-- We can use the following Marlowe contract and it's XML representation to understand the
-- different constructors we expose.
--
-- Let
--     "value"
--     (Constant 0)
--     (When
--         []
--         10 Close
--     )
--
-- <xml>
--     <block type="BaseContractType" id="root_contract" deletable="false" x="13" y="187">
--         <statement name="BaseContractType">
--             <block type="LetContractType" id="B,h$QnT-yvh}n$mayQ(G">
--                 <field name="value_id">value</field>
--                 <value name="value">
--                     <block type="ConstantValueType" id="+wL`m?B;F`DCz#TQp?y)">
--                         <field name="constant">0</field>
--                     </block>
--                 </value>
--                 <statement name="contract">
--                     <block type="WhenContractType" id="LA$!CNdK@V{WOo,R2$re">
--                         <field name="timeout">10</field>
--                         <statement name="contract">
--                             <block type="CloseContractType" id=";FLEJsyB3D;Hj%vS]SY]"></block>
--                         </statement>
--                     </block>
--                 </statement>
--             </block>
--         </statement>
--     </block>
-- </xml>
module Blockly.Dom where

import Prelude
import Blockly.Internal (workspaceToDom)
import Blockly.Types (Blockly, Workspace)
import Control.Monad.Error.Extra (toMonadThrow)
import Control.Monad.Except (runExceptT, throwError)
import Control.Monad.Except.Trans (class MonadThrow)
import Data.Array (length)
import Data.Array.Partial as UnsafeArray
import Data.Either (Either(..), note')
import Data.Foldable (fold)
import Data.Maybe (Maybe, maybe')
import Data.Traversable (traverse)
import Debug.Trace (spy)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Partial.Unsafe (unsafePartial)
import Web.DOM (Element, Node)
import Web.DOM.Element as Element
import Web.DOM.HTMLCollection as HTMLCollection
import Web.DOM.Node as Node
import Web.DOM.NodeList as NodeList
import Web.DOM.ParentNode as ParentNode
import Web.DOM.Text (Text)
import Web.DOM.Text as Text

newtype Block
  = Block
  { id :: String
  , type :: String
  , children :: Array BlockChildren
  }

data BlockChildren
  -- A BcField has a `name` and and a `value`, both strings.
  -- It is visually represented as a label and an editable field, for example
  -- the "timeout" inside a When block, or the value inside a Constant block
  = BcField String String
  -- A BcValue has a `name` and and a `value`.
  -- It is visually represented as a label in the block that can be attached to a new block. For
  -- example "by", "the amount of" and "currency" in the Deposit block
  | BcValue String Block
  -- A BcStatement also has a `name` and a `value`.
  -- It is visually represented as the pluggable insides of a block. For example the contract inside
  -- the root block or the Actions inside of a When block.
  | BcStatement String Block
  -- When a statement element has multiple children, for example the when clause. Instead of having an
  -- array of blocks, it represents it with a "next" element in the children.
  -- FIXME: I should probably change the representation of the BcStatement to be an arary and "complicate"
  --       the reading of the blocks, rather than later the parsing of the interpretation.
  | BcNext Block

data ReadDomError
  = TypeMismatch Element String
  | MissingProperty Element String
  | SingleChildExpected Element Int

-- TODO: Change signature to Effect String and traverse the parents of the element to provide error location information.
explainError :: ReadDomError -> String
explainError (TypeMismatch element expectedType) = "Element is of the wrong type (" <> show expectedType <> " expected, " <> show (Element.tagName element) <> " received)"

explainError (MissingProperty element missingProperty) = "Element is missing required property " <> show missingProperty

explainError (SingleChildExpected element elementCount) = "Element was expected to have a single child, and it had " <> show elementCount

getDom :: Blockly -> Workspace -> Effect (Either ReadDomError Block)
getDom blockly workspace = do
  rootElement <- spy "xml?" <$> workspaceToDom blockly workspace
  if Element.tagName rootElement /= "xml" then
    pure $ Left $ TypeMismatch rootElement "xml"
  else
    runExceptT do
      child <- getSingleChild rootElement
      readAsBlock child
  where
  readAsBlock :: forall m. MonadEffect m => MonadThrow ReadDomError m => Element -> m Block
  readAsBlock element =
    if Element.tagName element /= "block" then
      throwError $ TypeMismatch element "block"
    else do
      blockId <- liftEffect $ Element.id element
      blockType <- getAttribute "type" element
      elementChildren <- getChildElements element
      children <- traverse readAsBlockChild elementChildren
      pure
        $ Block
            { id: blockId
            , type: blockType
            , children
            }

  readAsBlockChild :: forall m. MonadEffect m => MonadThrow ReadDomError m => Element -> m BlockChildren
  readAsBlockChild element = do
    case Element.tagName element of
      "field" -> do
        name <- getAttribute "name" element
        value <- getElementText element
        pure $ BcField name value
      "statement" -> do
        name <- getAttribute "name" element
        child <- getSingleChild element
        value <- readAsBlock child
        pure $ BcStatement name value
      "value" -> do
        name <- getAttribute "name" element
        child <- getSingleChild element
        value <- readAsBlock child
        pure $ BcValue name value
      "next" -> do
        child <- getSingleChild element
        value <- readAsBlock child
        pure $ BcNext value
      _ -> throwError $ TypeMismatch element "field, statement, value, next"

  getSingleChild :: forall m. MonadEffect m => MonadThrow ReadDomError m => Element -> m Element
  getSingleChild element = do
    children <- getChildElements element
    if length children /= 1 then
      throwError $ SingleChildExpected element $ length children
    else do
      pure $ unsafePartial $ UnsafeArray.head children

  getChildElements :: forall m. MonadEffect m => Element -> m (Array Element)
  getChildElements element =
    liftEffect do
      elements <- (ParentNode.children <<< Element.toParentNode) element
      HTMLCollection.toArray elements

  getChildNodes :: forall m. MonadEffect m => Element -> m (Array Node)
  getChildNodes element =
    liftEffect do
      nodes <- (Node.childNodes <<< Element.toNode) element
      NodeList.toArray nodes

  getElementText :: forall m. MonadEffect m => Element -> m String
  getElementText element = do
    nodes <- getChildNodes element
    let
      textNodes :: Array (Maybe Text)
      textNodes = Text.fromNode <$> nodes

      maybeGetText :: (Maybe Text) -> m String
      maybeGetText = maybe' (\_ -> pure "") (liftEffect <<< Text.wholeText)
    fold <$> traverse maybeGetText textNodes

  getAttribute :: forall m. MonadEffect m => MonadThrow ReadDomError m => String -> Element -> m String
  getAttribute attr element = do
    mValue <- liftEffect $ Element.getAttribute attr element
    toMonadThrow $ note' (\_ -> MissingProperty element attr) mValue
