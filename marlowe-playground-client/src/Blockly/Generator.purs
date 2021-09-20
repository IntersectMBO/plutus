module Blockly.Generator where

-- FIXME: SCP-1881 Remove the Generator functionality once we refactor Actus to use Blockly.Dom
import Prelude
import Blockly.Types (Block, Blockly, Workspace)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn1, Fn3, Fn4, Fn5, Fn6, runFn1, runFn3, runFn4, runFn5, runFn6)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, EffectFn4, runEffectFn1, runEffectFn2, runEffectFn3, runEffectFn4)
import Partial.Unsafe (unsafePartial)

type GeneratorFunction
  = Block -> Either String String

-- FIXME: Do we still need a NewBlockFunction type? or was it because the ST code? can we use Blockly.Generator.newBlock directly?
--        In any case we may get rid of Generator altogether in a second step of the refactor.
type NewBlockFunction
  = Workspace -> String -> Effect Block

data Order
  = Atomic
  | None

toNumber :: Order -> Number
toNumber Atomic = 0.0

toNumber None = 99.0

foreign import data Generator :: Type

foreign import data Input :: Type

foreign import data Field :: Type

foreign import data Connection :: Type

-- FIXME: This should probably be EffectFn3, but read top level comment.
foreign import nextBlock_ :: Fn3 (Block -> Maybe Block) (Maybe Block) Block (Maybe Block)

foreign import getType_ :: Fn1 Block String

-- FIXME: This should probably be EffectFn4, but read top level comment.
foreign import getFieldValue_ :: forall a. Fn4 (String -> Either String a) (a -> Either String a) Block String (Either String String)

-- FIXME: This should probably be EffectFn5, but read top level comment.
foreign import statementToCode_ :: forall a. Fn5 (String -> Either String a) (a -> Either String a) Generator Block String (Either String String)

-- FIXME: This should probably be EffectFn6, but read top level comment.
foreign import valueToCode_ :: forall a. Fn6 (String -> Either String a) (a -> Either String a) Generator Block String Number (Either String String)

foreign import mkGenerator_ :: EffectFn2 Blockly String Generator

-- FIXME: should the callback be (Block -> Effect String)?
foreign import insertGeneratorFunction_ :: EffectFn3 Generator String (Block -> String) Unit

foreign import blockToCode_ :: forall a b. EffectFn4 (a -> Either a b) (b -> Either a b) Block Generator (Either String String)

foreign import inputList_ :: Fn1 Block (Array Input)

foreign import connectToPrevious_ :: EffectFn2 Block Input Unit

foreign import previousConnection_ :: EffectFn1 Block Connection

foreign import nextConnection_ :: EffectFn1 Block Connection

foreign import connect_ :: EffectFn2 Connection Connection Unit

foreign import connectToOutput_ :: EffectFn2 Block Input Unit

foreign import newBlock_ :: EffectFn2 Workspace String Block

-- FIXME: This should probably be EffectFn1, but read top level comment.
foreign import inputName_ :: Fn1 Input String

-- FIXME: This should probably be EffectFn1, but read top level comment.
foreign import inputType_ :: Fn1 Input Int

foreign import clearWorkspace_ :: EffectFn1 Workspace Unit

-- FIXME: This should probably be EffectFn1, but read top level comment.
foreign import fieldRow_ :: Fn1 Input (Array Field)

foreign import setFieldText_ :: EffectFn2 Field String Unit

-- FIXME: This should probably be EffectFn1, but read top level comment.
foreign import fieldName_ :: Fn1 Field String

foreign import unsafeThrowError_ :: forall a. Fn1 String a

-- FIXME: This should probably be EffectFn3, but read top level comment.
foreign import getBlockInputConnectedTo_ :: forall a b. Fn3 (a -> Either a b) (b -> Either a b) Input (Either String Block)

nextBlock :: Block -> Maybe Block
nextBlock = runFn3 nextBlock_ Just Nothing

getType :: Block -> String
getType = runFn1 getType_

getFieldValue :: Block -> String -> Either String String
getFieldValue = runFn4 getFieldValue_ Left Right

statementToCode :: Generator -> Block -> String -> Either String String
statementToCode = runFn5 statementToCode_ Left Right

valueToCode :: Generator -> Block -> String -> Order -> Either String String
valueToCode g b v o = runFn6 valueToCode_ Left Right g b v (toNumber o)

mkGenerator :: Blockly -> String -> Effect Generator
mkGenerator = runEffectFn2 mkGenerator_

insertGeneratorFunction :: Generator -> String -> (Block -> Either String String) -> Effect Unit
insertGeneratorFunction generator key f = runEffectFn3 insertGeneratorFunction_ generator key ((unsafePartial unsafeFromRight) <<< f)

-- | This will throw the Left value in a result as a runtime exception
unsafeFromRight :: forall a. Partial => Either String a -> a
unsafeFromRight (Right a) = a

unsafeFromRight (Left e) = runFn1 unsafeThrowError_ e

blockToCode :: Block -> Generator -> Effect (Either String String)
blockToCode = runEffectFn4 blockToCode_ Left Right

inputList :: Block -> Array Input
inputList = runFn1 inputList_

connectToPrevious :: Block -> Input -> Effect Unit
connectToPrevious = runEffectFn2 connectToPrevious_

previousConnection :: Block -> Effect Connection
previousConnection = runEffectFn1 previousConnection_

nextConnection :: Block -> Effect Connection
nextConnection = runEffectFn1 nextConnection_

connect :: Connection -> Connection -> Effect Unit
connect = runEffectFn2 connect_

connectToOutput :: Block -> Input -> Effect Unit
connectToOutput = runEffectFn2 connectToOutput_

newBlock :: Workspace -> String -> Effect Block
newBlock = runEffectFn2 newBlock_

inputName :: Input -> String
inputName = runFn1 inputName_

inputType :: Input -> Int
inputType = runFn1 inputType_

getInputWithName :: Array Input -> String -> Maybe Input
getInputWithName inputs name = do
  idx <- Array.findIndex (\i -> (inputName i) == name) inputs
  Array.index inputs idx

clearWorkspace :: Workspace -> Effect Unit
clearWorkspace = runEffectFn1 clearWorkspace_

fieldRow :: Input -> Array Field
fieldRow = runFn1 fieldRow_

setFieldText :: Field -> String -> Effect Unit
setFieldText = runEffectFn2 setFieldText_

fieldName :: Field -> String
fieldName = runFn1 fieldName_

getBlockInputConnectedTo :: Input -> Either String Block
getBlockInputConnectedTo = runFn3 getBlockInputConnectedTo_ Left Right
