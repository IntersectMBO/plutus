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
-- When
--   [ Case (Notify TrueObs ) Close
--   , Case
--       (Choice
--         (ChoiceId "name" (Role "role") )
--         [(Bound 0 0)]
--       ) Close
--   ]
--   0 Close
--
-- <xml>
--     <block type="BaseContractType" id="root_contract" deletable="false" x="13" y="187">
--         <statement name="BaseContractType">
--             <block type="WhenContractType" id="yy!Q^=B5;V_Sk@546gjk">
--                 <field name="timeout">0</field>
--                 <statement name="case">
--                     <block type="NotifyActionType" id=":!;w+=o^v3QU%M+zAaI^">
--                         <value name="observation">
--                             <block type="TrueObservationType" id="@}aK]jjhxi=2LLj*5g}."></block>
--                         </value>
--                         <statement name="contract">
--                             <block type="CloseContractType" id="Yd_ab!Vtyb88H@?Eqj9E"></block>
--                         </statement>
--                         <next>
--                             <block type="ChoiceActionType" id=")z[fYD/@_GoEtKS}/48t">
--                                 <field name="choice_name">name</field>
--                                 <value name="party">
--                                     <block type="RolePartyType" id="`blYZ~JOFle+tRT_@;KS">
--                                         <field name="role">role</field>
--                                     </block>
--                                 </value>
--                                 <statement name="bounds">
--                                     <block type="BoundsType" id="5x$vp,OGm^;CWEYL;l_u">
--                                         <field name="from">0</field>
--                                         <field name="to">0</field>
--                                     </block>
--                                 </statement>
--                                 <statement name="contract">
--                                     <block type="CloseContractType" id="VkYy9=B7eZ/AZAd@6jr)"></block>
--                                 </statement>
--                             </block>
--                         </next>
--                     </block>
--                 </statement>
--                 <statement name="contract">
--                     <block type="CloseContractType" id="dzm~uz;1}9ZF,+L^UbCX"></block>
--                 </statement>
--             </block>
--         </statement>
--     </block>
-- </xml>
module Blockly.Dom where

import Prelude
import Blockly.Internal (workspaceToDom)
import Blockly.Types (BlocklyState)
import Control.Monad.Error.Extra (toMonadThrow)
import Control.Monad.Except (runExceptT, throwError)
import Control.Monad.Except.Trans (class MonadThrow)
import Data.Array (find, length)
import Data.Array.Partial as UnsafeArray
import Data.Compactable (separate)
import Data.Either (Either(..), note')
import Data.Generic.Rep (class Generic)
import Data.Lens (Lens', _1, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Foreign.Generic (class Encode, defaultOptions, genericEncode)
import Foreign.Object (Object)
import Foreign.Object as Object
import Partial.Unsafe (unsafePartial)
import Web.DOM (Element, Node)
import Web.DOM.Element as Element
import Web.DOM.HTMLCollection as HTMLCollection
import Web.DOM.Node as Node
import Web.DOM.NodeList as NodeList
import Web.DOM.ParentNode as ParentNode

newtype Block
  = Block
  { id :: String
  , type :: String
  -- In the XML the children of a block are stored/represented as an array of elements, but to simplify
  -- consumption we use a JS native Object (like a `Map String a` but with better performance).
  -- This decision implies that we cannot have two childs properties with the same `name`, but I think we shouldn't
  -- anyway, and if we do, we are going to have the same kind of error later on, while transforming from Dom -> Term
  , children :: Object BlockChild
  }

-- FIXME: Show only for dev, remove
derive instance genericBlock :: Generic Block _

instance encodeBlock :: Encode Block where
  encode value = genericEncode defaultOptions value

-- END FIXME
derive instance newtypeBlock :: Newtype Block _

_id :: Lens' Block String
_id = _Newtype <<< prop (SProxy :: SProxy "id")

data BlockChild
  -- A Field is visually represented as a label and an editable field, for example
  -- the "timeout" inside a "When block", or the value inside a "Constant block".
  = Field String
  -- A Value is visually represented as a label in the block that can be attached to a new block on the side.
  -- For example "by", "the amount of" and "currency" in the "Deposit block"
  | Value Block
  -- A Statement is visually represented as the pluggable elements inside of a block. For example the contract inside
  -- the root block or the Actions inside of a When block.
  -- We represent the statement children as an Array of Blocks, but as you can see in the top level XML example,
  -- each `<statement>` has a single block child, and siblings are represented by a `<next>` node nested inside.
  -- In the initial version of this module, Next was a BlockChild constructor, making it easier to parse the
  -- XML, but knowing that it would complicate the translation to Term, I decided to flatten the statement's childs
  -- while parsing.
  | Statement (Array Block)

-- FIXME: Show only for dev, remove
derive instance genericBlockChildren :: Generic BlockChild _

instance encodeBlockChildren :: Encode BlockChild where
  encode value = genericEncode defaultOptions value

-- ENDFIXME
type ChildWithName
  = Tuple String BlockChild

data ReadDomError
  = TypeMismatch Element String
  | MissingProperty Element String
  | SingleChildExpected Element Int
  | RootElementNotFound String
  | IncorrectSiblingNesting String

-- TODO: Change signature to Effect String and traverse the parents of the element to provide error location information.
explainError :: ReadDomError -> String
explainError (TypeMismatch element expectedType) = "Element is of the wrong type (" <> show expectedType <> " expected, " <> show (Element.tagName element) <> " received)"

explainError (MissingProperty element missingProperty) = "Element is missing required property " <> show missingProperty

explainError (SingleChildExpected element elementCount) = "Element was expected to have a single child, and it had " <> show elementCount

explainError (RootElementNotFound rootBlockName) = "The element with id " <> show rootBlockName <> " was not found."

explainError (IncorrectSiblingNesting node) = "Incorrect <next> element found outside the scope of a <statement> and inside of a " <> node <> " node"

-- | Read and parse the DOM nodes of a blockly workspace.
getDom :: BlocklyState -> Effect (Either ReadDomError Block)
getDom { blockly, workspace, rootBlockName } =
  runExceptT do
    -- FIXME: remove the spy
    rootElement <- liftEffect $ workspaceToDom blockly workspace
    if Element.tagName rootElement /= "xml" then
      throwError $ TypeMismatch rootElement "xml"
    else do
      -- The workspace can have many elements at the top level, we parse them all
      -- but only return the one that has the same id as rootBlockName
      childrens <- getChildrens rootElement
      blocks <- traverse readAsBlock childrens
      case find (eq rootBlockName <<< view (_1 <<< _id)) blocks of
        Nothing -> throwError $ RootElementNotFound rootBlockName
        Just (Tuple block nexts) ->
          if length nexts /= 0 then
            throwError $ IncorrectSiblingNesting "root"
          else
            pure block
  where
  -- Tries to read an Element as a Block node. It returns a tuple with the parsed Block and an Array of Block's which
  -- are the parsed <next> elements which represent the siblings of a parent Statement.
  readAsBlock :: forall m. MonadEffect m => MonadThrow ReadDomError m => Element -> m (Tuple Block (Array Block))
  readAsBlock element =
    if Element.tagName element /= "block" then
      throwError $ TypeMismatch element "block"
    else do
      blockId <- liftEffect $ Element.id element
      blockType <- getAttribute "type" element
      elementChildren <- getChildrens element
      -- Parse each child element, which can be Either a BlockChild (field, value, statement) or a list of
      -- siblings to pass to my parent
      { left, right } <- separate <$> traverse readAsBlockChild elementChildren
      let
        children = Object.fromFoldable left
      pure
        $ Tuple
            (Block { id: blockId, type: blockType, children })
            (join right)

  -- Tries to read an Element as the children of a Block node. The Left hand side of the return represents a Block direct children
  -- while the Right hand side represents the parsed `<next>` elements which should be appended to a parents Statement.
  readAsBlockChild ::
    forall m.
    MonadEffect m =>
    MonadThrow ReadDomError m =>
    Element ->
    m (Either ChildWithName (Array Block))
  readAsBlockChild element = do
    case Element.tagName element of
      "field" -> do
        name <- getAttribute "name" element
        value <- getElementText element
        pure $ Left $ Tuple name $ Field value
      "statement" -> do
        name <- getAttribute "name" element
        child <- getSingleChild element
        Tuple block nexts <- readAsBlock child
        pure $ Left $ Tuple name $ Statement ([ block ] <> nexts)
      "value" -> do
        name <- getAttribute "name" element
        child <- getSingleChild element
        Tuple block nexts <- readAsBlock child
        -- Even if a value can have a Block appended, it should have a single block child and no "siblings"
        if length nexts /= 0 then
          throwError $ IncorrectSiblingNesting "value"
        else
          pure $ Left $ Tuple name $ Value block
      "next" -> do
        child <- getSingleChild element
        Tuple block nexts <- readAsBlock child
        pure $ Right ([ block ] <> nexts)
      _ -> throwError $ TypeMismatch element "field, statement, value, next"

  getSingleChild :: forall m. MonadEffect m => MonadThrow ReadDomError m => Element -> m Element
  getSingleChild element = do
    children <- getChildrens element
    if length children /= 1 then
      throwError $ SingleChildExpected element $ length children
    else do
      pure $ unsafePartial $ UnsafeArray.head children

  getChildrens :: forall m. MonadEffect m => Element -> m (Array Element)
  getChildrens element =
    liftEffect do
      elements <- (ParentNode.children <<< Element.toParentNode) element
      HTMLCollection.toArray elements

  getChildNodes :: forall m. MonadEffect m => Element -> m (Array Node)
  getChildNodes element =
    liftEffect do
      nodes <- (Node.childNodes <<< Element.toNode) element
      NodeList.toArray nodes

  getElementText :: forall m. MonadEffect m => Element -> m String
  getElementText element = liftEffect $ (Node.textContent <<< Element.toNode) element

  getAttribute :: forall m. MonadEffect m => MonadThrow ReadDomError m => String -> Element -> m String
  getAttribute attr element = do
    mValue <- liftEffect $ Element.getAttribute attr element
    toMonadThrow $ note' (\_ -> MissingProperty element attr) mValue
