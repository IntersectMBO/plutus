module Worker where

import Prelude

import Control.Monad.Except (runExcept)
import Data.Array (drop, filter, head, take)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn0, runFn0)
import Data.Map (Map)
import Data.Maybe (Maybe(..), fromMaybe, isNothing)
import Data.String (trim)
import Data.Symbolic (checkSat, declareVars, equationModel, getEquations, solveEquation)
import Debug.Trace (trace)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Effect.Class.Console as Console
import Effect.Uncurried (EffectFn2, runEffectFn2)
import Foreign.Generic (Foreign, defaultOptions, genericDecode, genericEncode)
import Marlowe.Holes as Holes
import Marlowe.Parser as Parser
import Marlowe.Semantics (Contract(..))
import Marlowe.Symbolic (getTransactionOutput, hasWarnings)
import Text.Parsing.Parser (runParser)
import Text.Parsing.Parser.Basic (parens)
import Worker.Types (WorkerRequest(..), WorkerResponse(..))
import Z3.Internal (onZ3Initialized)
import Z3.Monad (evalString, pop, push, runZ3)

foreign import data Context :: Type

foreign import data MessageEvent :: Type

foreign import context :: Fn0 Context

foreign import postMessage_ :: EffectFn2 Context Foreign Unit

foreign import registerOnMessage_ :: EffectFn2 Context (Foreign -> Effect Unit) Unit

registerOnMessage :: Context -> (Context -> WorkerRequest -> Effect Unit) -> Effect Unit
registerOnMessage ctx f = do
  runEffectFn2 registerOnMessage_ ctx handler
  where
  handler msg = case runExcept (genericDecode defaultOptions msg) of
    Left err -> do
      Console.log (show err)
      pure unit
    Right req -> do
      Console.log (show req)
      f ctx req

postMessage :: Context -> WorkerResponse -> Effect Unit
postMessage ctx req = let msg = genericEncode defaultOptions req in runEffectFn2 postMessage_ ctx msg

handleRequest :: Context -> WorkerRequest -> Effect Unit
handleRequest ctx (AnalyseContract contractString) = do
  res <- checkContractForWarnings contractString
  trace res \_ -> pure unit
  postMessage ctx (AnalyseContractResult (show res))

handleRequest ctx InitializeZ3 = onZ3Initialized do
  Console.log "Z3 loaded"
  postMessage ctx InitializedZ3

checkContractForWarnings :: String -> Effect (Maybe (Map String String))
checkContractForWarnings contractString = do
  Console.log "Running Analysis"
  let
    contract = case runParser contractString (parens Parser.contract) of
      Left e -> Close
      Right c -> fromMaybe Close $ Holes.fromTerm c

    tree = getTransactionOutput contract

    equationsA = take 5000 $ filter (\a -> hasWarnings a.value) $ getEquations tree

    equationsB = drop 5000 $ filter (\a -> hasWarnings a.value) $ getEquations tree

    _ = trace (head equationsA) \_ -> 1
  -- FIXME: All this is batched because findM seems to blow the stack. I think we need to look into making the Z3 monad stack safe
  liftEffect do
    resA <-
      runZ3 do
        r1 <- declareVars equationsA
        findM equationsA f
    if isNothing resA then
      runZ3 do
        r1 <- declareVars equationsB
        findM equationsB f
    else
      pure resA
  where
  f a = do
    push
    _ <- solveEquation a
    isSat <- (evalString $ show checkSat)
    res <- if trim isSat == "sat" then Just <$> equationModel a else pure Nothing
    pop
    pure res

-- | Find the first Just occurance of a function applied to an element in an array
findM :: forall m a b. Monad m => Array a -> (a -> m (Maybe b)) -> m (Maybe b)
findM array f = case Array.uncons array of
  Just { head, tail } -> do
    mRes <- f head
    case mRes of
      Just res -> pure $ Just res
      Nothing -> findM tail f
  Nothing -> pure Nothing

-- handler needs to recieve messages that are a map of type and body (string) and pattern match on the type
-- need to coerce to {messageType: "AnalyseContract|InitializeZ3", body: contractString|null }
main ::
  Effect Unit
main = do
  ctx <- pure $ runFn0 context
  registerOnMessage ctx handleRequest
  log "Worker Loaded"
