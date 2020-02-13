module Marlowe.BlocklyTests where

import Prelude
import Blockly (getBlockById)
import Blockly as Blockly
import Blockly.Generator (Generator, getInputWithName, inputList, workspaceToCode)
import Blockly.Headless as Headless
import Blockly.Types (BlocklyState)
import Control.Alt ((<|>))
import Control.Monad.Reader (runReaderT)
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
import Marlowe.GenWithHoles (GenWithHoles, unGenWithHoles)
import Marlowe.Holes as Holes
import Marlowe.Parser as Parser
import Marlowe.Semantics (Contract)
import Test.QuickCheck (class Testable, Result(..), (===))
import Test.Unit (Test, TestSuite, suite, test)
import Test.Unit.QuickCheck (quickCheck)
import Text.Parsing.StringParser (runParser)
import Text.Parsing.StringParser.Basic (parens)

all :: TestSuite
all =
  suite "Marlowe.Blockly" do
    test "c2b2c" $ quickCheckGen c2b2c

quickCheckGen :: forall prop. Testable prop => GenWithHoles prop -> Test
quickCheckGen g = quickCheck $ runReaderT (unGenWithHoles g) false

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

c2b2c :: GenWithHoles Result
c2b2c = do
  termContract <- genContract
  case Holes.fromTerm termContract of
    -- Unfortunately quickcheck runs the concrete Gen monad and it would need to be re-written to use MonadGen
    -- https://github.com/purescript/purescript-quickcheck/blob/v5.0.0/src/Test/QuickCheck.purs#L97
    -- I made the executive decision that it's not worth my time to do it in this specific case
    -- I have created https://github.com/purescript/purescript-quickcheck/issues/102
    Just contract -> let result = unsafePerformEffect $ runContract contract in pure (result === Right contract)
    Nothing -> pure $ Failed $ "Contract could not be coerced from a Term contract" <> show termContract

runContract :: Contract -> Effect (Either String Contract)
runContract contract = do
  state <- liftEffect mkTestState
  pure $ ST.run (buildBlocks state.blocklyState contract)
  let
    eCode = workspaceToCode state.blocklyState state.generator
  pure
    $ case eCode of
        Right code -> lmap show $ runParser (parens Parser.contractValue <|> Parser.contractValue) code
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
