module Marlowe.BlocklyTests where

import Prelude
import Blockly (getBlockById)
import Blockly as Blockly
import Blockly.Generator (Generator, getInputWithName, inputList, blockToCode)
import Blockly.Headless as Headless
import Blockly.Types (BlocklyState)
import Control.Monad.Reader (runReaderT)
import Control.Monad.ST (ST)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
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
    test "c2b2c" $ quickCheckGen c2b2c

quickCheckGen :: forall prop. Testable prop => GenWithHoles prop -> Test
quickCheckGen g = quickCheck $ runReaderT (unGenWithHoles g) true

mkTestState :: forall m. MonadEffect m => m { blocklyState :: BlocklyState, generator :: Generator }
mkTestState = do
  blocklyState <- liftEffect $ Headless.createBlocklyInstance rootBlockName
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

-- Here we keep using `show` because the Term range is intentionally incorrect when converting from blockly
-- It uses emptyRange to create a dummy range. By using `show` we can reasonably compare contracts
c2b2c :: GenWithHoles Result
c2b2c = do
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
  pure $ ST.run (buildBlocks state.blocklyState contract)
  pure do
    rootBlock <- note "failed to get root block" $ getBlockById state.blocklyState.workspace state.blocklyState.rootBlockName
    code <- blockToCode rootBlock state.generator
    lmap show $ Parser.parseContract (stripParens code)

buildBlocks :: forall r. BlocklyState -> Term Contract -> ST r Unit
buildBlocks bs contract = do
  workspaceRef <- STRef.new bs.workspace
  let
    mContract = getBlockById bs.workspace rootBlockName
  rootBlock <- case mContract of
    Nothing -> Headless.newBlock workspaceRef "BaseContractType" >>= STRef.read
    Just block -> pure block
  let
    inputs = inputList rootBlock
  for_ (getInputWithName inputs "BaseContractType") \input -> toBlockly Headless.newBlock workspaceRef input contract
