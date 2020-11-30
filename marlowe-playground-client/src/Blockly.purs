module Blockly where

import Prelude
import Blockly.Types (Block, Blockly, BlocklyState, Workspace)
import Control.Monad.ST.Internal (ST, STRef)
import Data.Function.Uncurried (Fn1, Fn2, Fn3, Fn4, runFn1, runFn2, runFn3, runFn4)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Data.Symbol (SProxy(..))
import Data.Traversable (class Foldable, traverse_)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)
import Foreign (Foreign)
import Global (infinity)
import Halogen.HTML (AttrName(..), ElemName(..), Node)
import Halogen.HTML.Elements (element)
import Halogen.HTML.Properties (IProp, attr)
import Record as Record
import Simple.JSON (class WriteForeign)
import Simple.JSON as JSON
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
  = { toolbox :: HTMLElement
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

-- Functions that mutate values always work on STRefs rather than regular values
foreign import getElementById_ :: EffectFn1 String HTMLElement

foreign import createBlocklyInstance_ :: Effect Blockly

foreign import createWorkspace_ :: EffectFn3 Blockly String WorkspaceConfig Workspace

foreign import resizeBlockly_ :: forall r. Fn2 Blockly (STRef r Workspace) (ST r Unit)

foreign import addBlockType_ :: forall r. Fn3 (STRef r Blockly) String Foreign (ST r Unit)

foreign import initializeWorkspace_ :: forall r. Fn2 Blockly (STRef r Workspace) (ST r Unit)

foreign import addChangeListener_ :: EffectFn2 Workspace EventListener Unit

foreign import removeChangeListener_ :: EffectFn2 Workspace EventListener Unit

foreign import render_ :: forall r. Fn1 (STRef r Workspace) (ST r Unit)

foreign import getBlockById_ :: forall a. Fn4 (a -> Maybe a) (Maybe a) Workspace String (Maybe Block)

foreign import workspaceXML_ :: Fn2 Blockly Workspace XML

foreign import loadWorkspace_ :: forall r. Fn3 Blockly (STRef r Workspace) XML (ST r Unit)

newtype ElementId
  = ElementId String

derive instance newtypeElementId :: Newtype ElementId _

createBlocklyInstance :: String -> ElementId -> ElementId -> Effect BlocklyState
createBlocklyInstance rootBlockName workspaceElementId toolboxElementId = do
  blockly <- createBlocklyInstance_
  toolbox <- runEffectFn1 getElementById_ (unwrap toolboxElementId)
  workspace <- runEffectFn3 createWorkspace_ blockly (unwrap workspaceElementId) (config toolbox)
  pure { blockly, workspace, rootBlockName, hasUnsavedChanges: false }
  where
  config toolbox =
    { toolbox: toolbox
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

resize :: forall r. Blockly -> STRef r Workspace -> ST r Unit
resize = runFn2 resizeBlockly_

addBlockType :: forall r. STRef r Blockly -> BlockDefinition -> ST r Unit
addBlockType blocklyRef (BlockDefinition fields) =
  let
    definition = JSON.write $ Record.delete type_ fields

    type' = fields.type
  in
    runFn3 addBlockType_ blocklyRef type' definition

addBlockTypes :: forall f r. Foldable f => STRef r Blockly -> f BlockDefinition -> ST r Unit
addBlockTypes blocklyState = traverse_ (addBlockType blocklyState)

initializeWorkspace :: forall r. Blockly -> STRef r Workspace -> ST r Unit
initializeWorkspace = runFn2 initializeWorkspace_

addChangeListener :: Workspace -> EventListener -> Effect Unit
addChangeListener = runEffectFn2 addChangeListener_

removeChangeListener :: Workspace -> EventListener -> Effect Unit
removeChangeListener = runEffectFn2 removeChangeListener_

render :: forall r. (STRef r Workspace) -> ST r Unit
render = runFn1 render_

getBlockById :: Workspace -> String -> Maybe Block
getBlockById = runFn4 getBlockById_ Just Nothing

workspaceXML :: Blockly -> Workspace -> XML
workspaceXML = runFn2 workspaceXML_

loadWorkspace :: forall r. Blockly -> (STRef r Workspace) -> XML -> ST r Unit
loadWorkspace = runFn3 loadWorkspace_

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

xml :: forall p i. Node ( id :: String, style :: String ) p i
xml = element (ElemName "xml")

category :: forall p i. Node ( name :: String, colour :: String ) p i
category = element (ElemName "category")

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
