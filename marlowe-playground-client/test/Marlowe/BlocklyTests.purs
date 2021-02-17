module Marlowe.BlocklyTests where

import Prelude
import Blockly.Generator (Generator, getInputWithName, inputList, blockToCode)
import Blockly.Headless as Headless
import Blockly.Internal (getBlockById)
import Blockly.Internal as Blockly
import Blockly.Types (BlocklyState)
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Bifunctor (lmap, rmap)
import Data.Either (Either, note)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Unsafe (unsafePerformEffect)
import Marlowe.Blockly (blockDefinitions, buildGenerator, rootBlockName, toBlockly)
import Marlowe.Gen (genContract, genTerm)
import Marlowe.GenWithHoles (GenWithHoles, unGenWithHoles)
import Marlowe.Holes (Contract, Term)
import Marlowe.Parser as Parser
import Test.QuickCheck (class Testable, Result, (===))
import Test.Unit (Test, TestSuite, suite, test)
import Test.Unit.QuickCheck (quickCheck)
import Text.Extra (stripParens)

all :: TestSuite
all =
  suite "Marlowe.Blockly" do
    test "codeToBlocklyToCode" $ quickCheckGen codeToBlocklyToCode

quickCheckGen :: forall prop. Testable prop => GenWithHoles prop -> Test
quickCheckGen g = quickCheck $ runReaderT (unGenWithHoles g) true

mkTestState :: forall m. MonadEffect m => m { blocklyState :: BlocklyState, generator :: Generator }
mkTestState = do
  blocklyState <- liftEffect $ Headless.createBlocklyInstance rootBlockName
  liftEffect do
    Blockly.addBlockTypes blocklyState.blockly blockDefinitions
    Headless.initializeWorkspace blocklyState
  generator <- liftEffect $ buildGenerator blocklyState.blockly
  pure { blocklyState: blocklyState, generator: generator }

-- Here we keep using `show` because the Term range is intentionally incorrect when converting from blockly
-- It uses zero to create a dummy range. By using `show` we can reasonably compare contracts
codeToBlocklyToCode :: GenWithHoles Result
codeToBlocklyToCode = do
  contract <- genTerm "contract" genContract
  let
    positionedContract = rmap show $ lmap show $ Parser.parseContract (stripParens $ show contract)

    -- Unfortunately quickcheck runs the concrete Gen monad and it would need to be re-written to use MonadGen
    -- https://github.com/purescript/purescript-quickcheck/blob/v5.0.0/src/Test/QuickCheck.purs#L97
    -- I made the executive decision that it's not worth my time to do it in this specific case hence unsafePerformEffect
    -- I have created https://github.com/purescript/purescript-quickcheck/issues/102
    result = rmap show $ unsafePerformEffect $ runContract contract
  pure (result === positionedContract)

runContract :: Term Contract -> Effect (Either String (Term Contract))
runContract contract = do
  state <- liftEffect mkTestState
  liftEffect $ buildBlocks state.blocklyState contract
  runExceptT do
    rootBlock <- ExceptT $ note "failed to get root block" <$> getBlockById state.blocklyState.workspace state.blocklyState.rootBlockName
    code <- ExceptT $ blockToCode rootBlock state.generator
    ExceptT $ pure $ lmap show $ Parser.parseContract (stripParens code)

buildBlocks :: BlocklyState -> Term Contract -> Effect Unit
buildBlocks bs contract = do
  mContract <- getBlockById bs.workspace rootBlockName
  rootBlock <- case mContract of
    Nothing -> Headless.newBlock bs.workspace "BaseContractType"
    Just block -> pure block
  let
    inputs = inputList rootBlock
  for_ (getInputWithName inputs "BaseContractType") \input -> toBlockly Headless.newBlock bs.workspace input contract
