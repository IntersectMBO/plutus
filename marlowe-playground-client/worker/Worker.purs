module Worker where

import Prelude
import Data.Array (drop, filter, head, take)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn0, Fn1, Fn2, runFn0, runFn1, runFn2)
import Data.Map (Map)
import Data.Maybe (Maybe(..), fromMaybe, isNothing)
import Data.String (trim)
import Data.Symbolic (checkSat, declareVars, equationModel, getEquations, solveEquation)
import Debug.Trace (trace)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Foreign (Foreign)
import Marlowe.Holes as Holes
import Marlowe.Parser as Parser
import Marlowe.Semantics (Contract(..))
import Marlowe.Symbolic (getTransactionOutput, hasWarnings)
import Text.Parsing.Parser (runParser)
import Text.Parsing.Parser.Basic (parens)
import Z3.Monad (evalString, pop, push, runZ3)

foreign import data Context :: Type

foreign import data MessageEvent :: Type

foreign import registerOnMessage :: Fn2 Context (MessageEvent -> Unit) Unit

foreign import context :: Fn0 Context

foreign import handler :: Fn1 MessageEvent Unit

foreign import getMessageData :: Fn1 MessageEvent Foreign

checkContractForWarnings :: String -> Effect (Maybe (Map String String))
checkContractForWarnings contractString = do
  let
    contract = case runParser contractString (parens Parser.contract) of
      Left e -> Close
      Right c -> fromMaybe Close $ Holes.fromTerm c

    tree = getTransactionOutput contract

    equationsA = take 10000 $ filter (\a -> hasWarnings a.value) $ getEquations tree

    equationsB = drop 10000 $ filter (\a -> hasWarnings a.value) $ getEquations tree

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
  h <- pure $ runFn1 handler
  let
    x = runFn2 registerOnMessage ctx h
  log "hi"
