module Worker where

import Prelude
import Control.Monad.Except (runExcept)
import Data.Array (filter, head)
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn0, runFn0)
import Data.Map (Map)
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.String (trim)
import Data.Symbolic (Equation, checkSat, declareVars, equationModel, getEquations, solveEquation)
import Data.Traversable (traverse)
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
import Z3.Monad (Z3, evalString, runZ3)

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
handleRequest ctx (AnalyseContractRequest contractString) = do
  res <- checkContractForWarnings contractString
  postMessage ctx (AnalyseContractResult (show res))

handleRequest ctx InitializeZ3 =
  onZ3Initialized do
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

    equations = filter (\a -> hasWarnings a.value) $ getEquations tree
  liftEffect do
    resA <-
      runZ3 do
        r1 <- declareVars equations
        traverse f equations
    case head (filter isJust resA) of
      Nothing -> pure Nothing
      (Just Nothing) -> pure Nothing
      (Just (Just m)) -> pure $ Just m
  where
  f :: forall a. Equation a -> Z3 (Maybe (Map String String))
  f a = do
    void $ evalString "(push)"
    void $ solveEquation a
    isSat <- (evalString $ show checkSat)
    res <- if (trim isSat) == "sat" then Just <$> equationModel a else pure Nothing
    void $ evalString "(pop)"
    pure res

main ::
  Effect Unit
main = do
  ctx <- pure $ runFn0 context
  registerOnMessage ctx handleRequest
  log "Worker Loaded"
