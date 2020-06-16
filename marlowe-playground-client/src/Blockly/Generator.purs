module Blockly.Generator where

import Prelude
import Blockly.Types (Block, BlocklyState, Workspace)
import Control.Monad.ST (ST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Data.Array as Array
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn1, Fn2, Fn3, Fn4, Fn5, Fn6, runFn1, runFn2, runFn3, runFn4, runFn5, runFn6)
import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafePartial)

type GeneratorFunction
  = Block -> Either String String

type NewBlockFunction r
  = (STRef r Workspace) -> String -> ST r (STRef r Block)

type NewSTRefFunction
  = (forall a r. a -> ST r (STRef r a))

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

-- Functions that mutate values always work on STRefs rather than regular values
foreign import nextBlock_ :: Fn3 (Block -> Maybe Block) (Maybe Block) Block (Maybe Block)

foreign import getType_ :: Fn1 Block String

foreign import getFieldValue_ :: forall a. Fn4 (String -> Either String a) (a -> Either String a) Block String (Either String String)

foreign import statementToCode_ :: forall a. Fn5 (String -> Either String a) (a -> Either String a) Generator Block String (Either String String)

foreign import valueToCode_ :: forall a. Fn6 (String -> Either String a) (a -> Either String a) Generator Block String Number (Either String String)

foreign import mkGenerator_ :: forall r. Fn3 NewSTRefFunction BlocklyState String (ST r (STRef r Generator))

foreign import insertGeneratorFunction_ :: forall r. Fn3 (STRef r Generator) String (Block -> String) (ST r Unit)

foreign import blockToCode_ :: forall a b. Fn4 (a -> Either a b) (b -> Either a b) Block Generator (Either String String)

foreign import inputList_ :: Fn1 Block (Array Input)

foreign import connectToPrevious_ :: forall r. Fn2 (STRef r Block) Input (ST r Unit)

foreign import previousConnection_ :: forall r. Fn1 (STRef r Block) (ST r Connection)

foreign import nextConnection_ :: forall r. Fn1 (STRef r Block) (ST r Connection)

foreign import connect_ :: forall r. Fn2 Connection Connection (ST r Unit)

foreign import connectToOutput_ :: forall r. Fn2 (STRef r Block) Input (ST r Unit)

foreign import newBlock_ :: forall r. Fn3 NewSTRefFunction (STRef r Workspace) String (ST r (STRef r Block))

foreign import inputName_ :: Fn1 Input String

foreign import inputType_ :: Fn1 Input Int

foreign import clearWorkspace_ :: forall r. Fn1 (STRef r Workspace) (ST r Unit)

foreign import fieldRow_ :: Fn1 Input (Array Field)

foreign import setFieldText_ :: forall r. Fn2 (STRef r Field) String (ST r Unit)

foreign import fieldName_ :: Fn1 Field String

foreign import unsafeThrowError_ :: forall a. Fn1 String a

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

mkGenerator :: forall r. BlocklyState -> String -> ST r (STRef r Generator)
mkGenerator = runFn3 mkGenerator_ STRef.new

insertGeneratorFunction :: forall r. STRef r Generator -> String -> (Block -> Either String String) -> ST r Unit
insertGeneratorFunction generator key f = runFn3 insertGeneratorFunction_ generator key ((unsafePartial unsafeFromRight) <<< f)

-- | This will throw the Left value in a result as a runtime exception
unsafeFromRight :: forall a. Partial => Either String a -> a
unsafeFromRight (Right a) = a

unsafeFromRight (Left e) = runFn1 unsafeThrowError_ e

blockToCode :: Block -> Generator -> Either String String
blockToCode = runFn4 blockToCode_ Left Right

inputList :: Block -> Array Input
inputList = runFn1 inputList_

connectToPrevious :: forall r. (STRef r Block) -> Input -> ST r Unit
connectToPrevious = runFn2 connectToPrevious_

previousConnection :: forall r. (STRef r Block) -> ST r Connection
previousConnection = runFn1 previousConnection_

nextConnection :: forall r. (STRef r Block) -> ST r Connection
nextConnection = runFn1 nextConnection_

connect :: forall r. Connection -> Connection -> ST r Unit
connect from to = runFn2 connect_ from to

connectToOutput :: forall r. (STRef r Block) -> Input -> ST r Unit
connectToOutput = runFn2 connectToOutput_

newBlock :: forall r. (STRef r Workspace) -> String -> ST r (STRef r Block)
newBlock = runFn3 newBlock_ STRef.new

inputName :: Input -> String
inputName = runFn1 inputName_

inputType :: Input -> Int
inputType = runFn1 inputType_

getInputWithName :: Array Input -> String -> Maybe Input
getInputWithName inputs name = do
  idx <- Array.findIndex (\i -> (inputName i) == name) inputs
  Array.index inputs idx

clearWorkspace :: forall r. STRef r Workspace -> ST r Unit
clearWorkspace = runFn1 clearWorkspace_

fieldRow :: Input -> Array Field
fieldRow = runFn1 fieldRow_

setFieldText :: forall r. (STRef r Field) -> String -> ST r Unit
setFieldText = runFn2 setFieldText_

fieldName :: Field -> String
fieldName = runFn1 fieldName_

getBlockInputConnectedTo :: Input -> Either String Block
getBlockInputConnectedTo = runFn3 getBlockInputConnectedTo_ Left Right
