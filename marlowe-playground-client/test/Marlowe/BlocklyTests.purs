module Marlowe.BlocklyTests where

import Prelude
import Blockly (getBlockById)
import Blockly as Blockly
import Blockly.Generator (Generator, getInputWithName, inputList, workspaceToCode)
import Blockly.Headless as Headless
import Blockly.Types (BlocklyState)
import Control.Alt ((<|>))
import Control.Lazy (class Lazy)
import Control.Monad.Gen (class MonadGen)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Unsafe (unsafePerformEffect)
import Marlowe.Blockly (blockDefinitions, buildGenerator, toBlockly)
import Marlowe.Gen (genContract)
import Marlowe.Parser as Parser
import Marlowe.Types (Contract, Observation, Value)
import Test.QuickCheck (class Testable, Result, (===))
import Test.QuickCheck.Gen (Gen)
import Test.Unit (Test, TestSuite, suite, test)
import Test.Unit.QuickCheck (quickCheck)
import Text.Parsing.Parser (runParser)
import Text.Parsing.Parser.Basic (parens)

all :: TestSuite
all =
  suite "Marlowe.Blockly" do
    test "c2b2c" $ quickCheckGen c2b2c

quickCheckGen :: forall prop. Testable prop => Gen prop -> Test
quickCheckGen = quickCheck

mkTestState :: forall m. MonadEffect m => m { blocklyState :: BlocklyState, generator :: Generator }
mkTestState = do
  blocklyState <- liftEffect $ Headless.createBlocklyInstance
  let
    _ =
      ST.run
        ( do
            blocklyRef <- STRef.new blocklyState.blockly
            Blockly.addBlockTypes blocklyRef blockDefinitions
        )
  liftEffect $ Headless.initializeWorkspace blocklyState
  let
    generator = buildGenerator blocklyState
  pure { blocklyState: blocklyState, generator: generator }

c2b2c :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => Lazy (m Observation) => Lazy (m Contract) => m Result
c2b2c = do
  contract <- genContract
  -- Unfortunately quickcheck runs the concrete Gen monad and it would need to be re-written to use MonadGen
  -- https://github.com/purescript/purescript-quickcheck/blob/v5.0.0/src/Test/QuickCheck.purs#L97
  -- I made the executive decision that it's not worth my time to do it in this specific case
  -- I have created https://github.com/purescript/purescript-quickcheck/issues/102
  let
    result = unsafePerformEffect $ runContract contract
  pure (result === Right contract)

runContract :: Contract -> Effect (Either String Contract)
runContract contract = do
  state <- liftEffect mkTestState
  pure $ ST.run (buildBlocks state.blocklyState contract)
  let
    eCode = workspaceToCode state.blocklyState state.generator
  pure
    $ case eCode of
        Right code -> lmap show $ runParser code (parens Parser.contract <|> Parser.contract)
        Left err -> Left err

buildBlocks :: forall r. BlocklyState -> Contract -> ST r Unit
buildBlocks bs contract = do
  workspaceRef <- STRef.new bs.workspace
  let
    mContract = getBlockById bs.workspace "root_contract"
  rootBlock <- case mContract of
    Nothing -> Headless.newBlock workspaceRef "BaseContractType" >>= STRef.read
    Just block -> pure block
  let
    inputs = inputList rootBlock
  for_ (getInputWithName inputs "BaseContractType") \input -> toBlockly Headless.newBlock workspaceRef input contract
