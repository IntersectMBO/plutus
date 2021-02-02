module Blockly.Headless where

import Prelude
import Blockly.Types (Block, Blockly, BlocklyState, Workspace)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)

foreign import createBlocklyInstance_ :: Effect Blockly

foreign import createWorkspace_ :: EffectFn1 Blockly Workspace

foreign import initializeWorkspace_ :: EffectFn2 Blockly Workspace Unit

foreign import newBlock_ :: EffectFn2 Workspace String Block

initializeWorkspace :: BlocklyState -> Effect Unit
initializeWorkspace state = runEffectFn2 initializeWorkspace_ state.blockly state.workspace

createBlocklyInstance :: String -> Effect BlocklyState
createBlocklyInstance rootBlockName = do
  blockly <- createBlocklyInstance_
  workspace <- runEffectFn1 createWorkspace_ blockly
  pure { blockly, workspace, rootBlockName }

newBlock :: Workspace -> String -> Effect Block
newBlock = runEffectFn2 newBlock_
