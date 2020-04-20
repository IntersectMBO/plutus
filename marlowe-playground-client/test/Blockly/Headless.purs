module Blockly.Headless where

import Prelude
import Blockly.Generator (NewSTRefFunction)
import Blockly.Types (Block, Blockly, BlocklyState, Workspace)
import Control.Monad.ST.Internal (ST, STRef)
import Control.Monad.ST.Ref as STRef
import Data.Function.Uncurried (Fn3, runFn3)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)

foreign import createBlocklyInstance_ :: Effect Blockly

foreign import createWorkspace_ :: EffectFn1 Blockly Workspace

foreign import initializeWorkspace_ :: EffectFn2 Blockly Workspace Unit

foreign import newBlock_ :: forall r. Fn3 NewSTRefFunction (STRef r Workspace) String (ST r (STRef r Block))

initializeWorkspace :: BlocklyState -> Effect Unit
initializeWorkspace state = runEffectFn2 initializeWorkspace_ state.blockly state.workspace

createBlocklyInstance :: Effect BlocklyState
createBlocklyInstance = do
  blockly <- createBlocklyInstance_
  workspace <- runEffectFn1 createWorkspace_ blockly
  let
    rootBlockName = "root_contract"
  pure { blockly, workspace, rootBlockName }

newBlock :: forall r. STRef r Workspace -> String -> ST r (STRef r Block)
newBlock = runFn3 newBlock_ STRef.new
