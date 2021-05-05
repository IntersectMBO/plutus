module Blockly.Internal where

import Prelude
import Blockly.Toolbox (Toolbox, encodeToolbox)
import Blockly.Types (Block, Blockly, BlocklyState, Workspace)
import Data.Argonaut.Core (Json)
import Data.Array (catMaybes)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Data.Symbol (SProxy(..))
import Data.Traversable (class Foldable, traverse_)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, EffectFn4, runEffectFn1, runEffectFn2, runEffectFn3, runEffectFn4)
import Foreign (Foreign)
import Global (infinity)
import Halogen.HTML (AttrName(..), ElemName(..), Node)
import Halogen.HTML.Elements (element)
import Halogen.HTML.Properties (IProp, attr)
import Record as Record
import Simple.JSON (class WriteForeign)
import Simple.JSON as JSON
import Web.DOM (Element)
import Web.Event.EventTarget (EventListener)
import Web.HTML (HTMLElement)

type GridConfig
  = { spacing :: Int
    , length :: Int
    , colour :: String
    , snap :: Boolean
    }

type ZoomConfig
  = { controls :: Boolean
    , wheel :: Boolean
    , startScale :: Number
    , maxScale :: Number
    , minScale :: Number
    , scaleSpeed :: Number
    }

type Move
  = { scrollbars :: Boolean
    , drag :: Boolean
    , wheel :: Boolean
    }

type WorkspaceConfig
  = { toolbox :: Json
    , collapse :: Boolean
    , comments :: Boolean
    , disable :: Boolean
    , maxBlocks :: Number
    , trashcan :: Boolean
    , horizontalLayout :: Boolean
    , toolboxPosition :: String
    , css :: Boolean
    , media :: String
    , rtl :: Boolean
    , sounds :: Boolean
    , oneBasedIndex :: Boolean
    , move :: Move
    , zoom :: ZoomConfig
    , grid :: GridConfig
    }

newtype XML
  = XML String

derive instance newtypeXML :: Newtype XML _

derive newtype instance semigroupXML :: Semigroup XML

derive newtype instance monoidXML :: Monoid XML

derive newtype instance eqXML :: Eq XML

foreign import getElementById_ :: EffectFn1 String HTMLElement

foreign import createBlocklyInstance_ :: Effect Blockly

foreign import createWorkspace_ :: EffectFn3 Blockly String WorkspaceConfig Workspace

foreign import resizeBlockly_ :: EffectFn2 Blockly Workspace Unit

foreign import addBlockType_ :: EffectFn3 Blockly String Foreign Unit

foreign import initializeWorkspace_ :: EffectFn2 Blockly Workspace Unit

foreign import addChangeListener_ :: EffectFn2 Workspace EventListener Unit

foreign import removeChangeListener_ :: EffectFn2 Workspace EventListener Unit

foreign import render_ :: EffectFn1 Workspace Unit

foreign import getBlockById_ :: forall a. EffectFn4 (a -> Maybe a) (Maybe a) Workspace String (Maybe Block)

foreign import workspaceXML_ :: EffectFn2 Blockly Workspace XML

foreign import loadWorkspace_ :: EffectFn3 Blockly Workspace XML Unit

-- This function exposes the blockly state in the global window so it's easier to debug/test functionalities
-- It is only called once per editor at the creation of the editor, so it doesn't consume resources and
-- could be left enabled.
foreign import debugBlockly_ :: EffectFn2 String BlocklyState Unit

foreign import workspaceToDom_ :: EffectFn2 Blockly Workspace Element

foreign import select_ :: EffectFn1 Block Unit

foreign import centerOnBlock_ :: EffectFn2 Workspace String Unit

foreign import hideChaff_ :: EffectFn1 Blockly Unit

foreign import getBlockType_ :: EffectFn1 Block String

foreign import updateToolbox_ :: EffectFn2 Json Workspace Unit

foreign import clearUndoStack_ :: EffectFn1 Workspace Unit

newtype ElementId
  = ElementId String

derive instance newtypeElementId :: Newtype ElementId _

createBlocklyInstance :: String -> ElementId -> Toolbox -> Effect BlocklyState
createBlocklyInstance rootBlockName workspaceElementId toolbox = do
  blockly <- createBlocklyInstance_
  workspace <- runEffectFn3 createWorkspace_ blockly (unwrap workspaceElementId) config
  runEffectFn2 debugBlockly_ (unwrap workspaceElementId) { blockly, workspace, rootBlockName }
  pure { blockly, workspace, rootBlockName }
  where
  config =
    { toolbox: encodeToolbox toolbox
    , collapse: true
    , comments: true
    , disable: true
    , maxBlocks: infinity
    , trashcan: true
    , horizontalLayout: false
    , toolboxPosition: "start"
    , css: true
    , media: "https://blockly-demo.appspot.com/static/media/"
    , rtl: false
    , sounds: true
    , oneBasedIndex: true
    , move:
        { scrollbars: true
        , drag: true
        , wheel: true
        }
    , zoom:
        { controls: true
        , wheel: false
        , startScale: 1.0
        , maxScale: 3.0
        , minScale: 0.3
        , scaleSpeed: 1.2
        }
    , grid:
        { spacing: 20
        , length: 3
        , colour: "#ccc"
        , snap: true
        }
    }

resize :: Blockly -> Workspace -> Effect Unit
resize = runEffectFn2 resizeBlockly_

addBlockType :: Blockly -> BlockDefinition -> Effect Unit
addBlockType blockly (BlockDefinition fields) =
  let
    definition = JSON.write $ Record.delete type_ fields

    type' = fields.type
  in
    runEffectFn3 addBlockType_ blockly type' definition

addBlockTypes :: forall f. Foldable f => Blockly -> f BlockDefinition -> Effect Unit
addBlockTypes blocklyState = traverse_ (addBlockType blocklyState)

initializeWorkspace :: Blockly -> Workspace -> Effect Unit
initializeWorkspace = runEffectFn2 initializeWorkspace_

addChangeListener :: Workspace -> EventListener -> Effect Unit
addChangeListener = runEffectFn2 addChangeListener_

removeChangeListener :: Workspace -> EventListener -> Effect Unit
removeChangeListener = runEffectFn2 removeChangeListener_

render :: Workspace -> Effect Unit
render = runEffectFn1 render_

getBlockById :: Workspace -> String -> Effect (Maybe Block)
getBlockById = runEffectFn4 getBlockById_ Just Nothing

workspaceXML :: Blockly -> Workspace -> Effect XML
workspaceXML = runEffectFn2 workspaceXML_

loadWorkspace :: Blockly -> Workspace -> XML -> Effect Unit
loadWorkspace = runEffectFn3 loadWorkspace_

workspaceToDom :: Blockly -> Workspace -> Effect Element
workspaceToDom = runEffectFn2 workspaceToDom_

select :: Block -> Effect Unit
select = runEffectFn1 select_

centerOnBlock :: Workspace -> String -> Effect Unit
centerOnBlock = runEffectFn2 centerOnBlock_

hideChaff :: Blockly -> Effect Unit
hideChaff = runEffectFn1 hideChaff_

getBlockType :: Block -> Effect String
getBlockType = runEffectFn1 getBlockType_

updateToolbox :: Toolbox -> Workspace -> Effect Unit
updateToolbox toolbox = runEffectFn2 updateToolbox_ (encodeToolbox toolbox)

clearUndoStack :: Workspace -> Effect Unit
clearUndoStack = runEffectFn1 clearUndoStack_

data Pair
  = Pair String String

instance writeForeignPair :: WriteForeign Pair where
  writeImpl (Pair first second) = JSON.write [ first, second ]

data Arg
  = Input { name :: String, text :: String, spellcheck :: Boolean }
  | Dropdown { name :: String, options :: Array Pair }
  | Checkbox { name :: String, checked :: Boolean }
  | Colour { name :: String, colour :: String }
  | Number { name :: String, value :: Number, min :: Maybe Number, max :: Maybe Number, precision :: Maybe Number }
  | Angle { name :: String, angle :: Number }
  | Variable { name :: String, variable :: String }
  -- Dates don't work in Blockly, see: https://developers.google.com/blockly/guides/create-custom-blocks/fields/built-in-fields/date
  | Date { name :: String, date :: String }
  | Label { text :: Maybe String, class :: Maybe String }
  | Image { src :: String, width :: Number, height :: Number, alt :: String }
  | Value { name :: String, check :: String, align :: AlignDirection }
  | Statement { name :: String, check :: String, align :: AlignDirection }
  | DummyRight
  | DummyLeft
  | DummyCentre

argType :: Arg -> Maybe { name :: String, check :: String }
argType (Value { name, check }) = Just { name, check }

argType (Statement { name, check }) = Just { name, check }

argType _ = Nothing

type_ :: SProxy "type"
type_ = SProxy

instance writeForeignArg :: WriteForeign Arg where
  writeImpl (Input fields) = JSON.write $ Record.insert type_ "field_input" fields
  writeImpl (Dropdown fields) = JSON.write $ Record.insert type_ "field_dropdown" fields
  writeImpl (Checkbox fields) = JSON.write $ Record.insert type_ "field_checkbox" fields
  writeImpl (Colour fields) = JSON.write $ Record.insert type_ "field_colour" fields
  writeImpl (Number fields) = JSON.write $ Record.insert type_ "field_number" fields
  writeImpl (Angle fields) = JSON.write $ Record.insert type_ "field_angle" fields
  writeImpl (Variable fields) = JSON.write $ Record.insert type_ "field_variable" fields
  writeImpl (Date fields) = JSON.write $ Record.insert type_ "field_date" fields
  writeImpl (Label fields) = JSON.write $ Record.insert type_ "field_label" fields
  writeImpl (Image fields) = JSON.write $ Record.insert type_ "field_image" fields
  writeImpl (Value fields) = JSON.write $ Record.insert type_ "input_value" fields
  writeImpl (Statement fields) = JSON.write $ Record.insert type_ "input_statement" fields
  writeImpl DummyRight = JSON.write $ { type: "input_dummy", align: Right }
  writeImpl DummyLeft = JSON.write $ { type: "input_dummy", align: Left }
  writeImpl DummyCentre = JSON.write $ { type: "input_dummy", align: Centre }

data AlignDirection
  = Left
  | Centre
  | Right

instance writeForeignAlignDirection :: WriteForeign AlignDirection where
  writeImpl Left = JSON.write "LEFT"
  writeImpl Centre = JSON.write "CENTRE"
  writeImpl Right = JSON.write "RIGHT"

type BasicBlockDefinition r
  = ( message0 :: String
    , args0 :: Array Arg
    , lastDummyAlign0 :: AlignDirection
    , colour :: String
    , fieldValue :: Maybe Pair
    , helpUrl :: String
    , inputsInline :: Maybe Boolean
    , nextStatement :: Maybe String
    , output :: Maybe String
    , previousStatement :: Maybe String
    , tooltip :: Maybe String
    , extensions :: Array String
    , mutator :: Maybe String
    | r
    )

newtype BlockDefinition
  = BlockDefinition (Record (BasicBlockDefinition ( type :: String )))

derive instance newtypeBlockDefinition :: Newtype BlockDefinition _

instance writeForeignBlockDefinition :: WriteForeign BlockDefinition where
  writeImpl (BlockDefinition fields) = JSON.write fields

defaultBlockDefinition ::
  { extensions :: Array String
  , lastDummyAlign0 :: AlignDirection
  , args0 :: Array Arg
  , fieldValue :: Maybe Pair
  , helpUrl :: String
  , inputsInline :: Maybe Boolean
  , mutator :: Maybe String
  , nextStatement :: Maybe String
  , output :: Maybe String
  , previousStatement :: Maybe String
  , tooltip :: Maybe String
  }
defaultBlockDefinition =
  { fieldValue: Nothing
  , lastDummyAlign0: Left
  , args0: []
  , helpUrl: ""
  , inputsInline: Just true
  , nextStatement: Nothing
  , output: Nothing
  , previousStatement: Nothing
  , tooltip: Nothing
  , extensions: []
  , mutator: Nothing
  }

typedArguments :: BlockDefinition -> Array { name :: String, check :: String }
typedArguments (BlockDefinition { args0 }) = catMaybes $ argType <$> args0

xml :: forall p i. Node ( id :: String, style :: String ) p i
xml = element (ElemName "xml")

block :: forall p i. Node ( id :: String, type :: String, x :: String, y :: String ) p i
block = element (ElemName "block")

blockType :: forall i r. String -> IProp ( type :: String | r ) i
blockType = attr (AttrName "type")

style :: forall i r. String -> IProp ( style :: String | r ) i
style = attr (AttrName "style")

colour :: forall i r. String -> IProp ( colour :: String | r ) i
colour = attr (AttrName "colour")

name :: forall i r. String -> IProp ( name :: String | r ) i
name = attr (AttrName "name")

x :: forall i r. String -> IProp ( x :: String | r ) i
x = attr (AttrName "x")

y :: forall i r. String -> IProp ( y :: String | r ) i
y = attr (AttrName "y")
