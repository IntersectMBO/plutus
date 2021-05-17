{-# LANGUAGE OverloadedStrings #-}

-- Exposes a single function that converts a 'Contract' to a string that can
-- be displayed in the mermaid drawing tool:
--
--  - <https://mermaid-js.github.io/mermaid/#/>
--
-- Example usage:
--
-- >>> import Language.Marlowe.Extended
-- >>> import Marlowe.Mermaid
-- >>>
-- >>> contract = If (Constant 5 `ValueEQ` Constant 2) Close Close
-- >>>
-- >>> putStrLn $ toMermaid contract
-- ...
--
-- Or, to display a contract from the `./contracts` folder:
--
-- >>> import Marlowe.Mermaid
-- >>> import Escrow
-- >>> putStrLn $ toMermaid contract
-- ...

module Marlowe.Mermaid (toMermaid) where

import           Data.Hashable             (hash)
import           Data.List                 (nub)
import           Language.Marlowe.Extended


-- | Convert the 'Contract' DSL into a flat list (like converting from a graph
-- representation to a vertex list). The result is a list denoting the
-- connection between contracts, and a string representing what text to
-- display on this edge.
flatten :: Contract -> [(Contract, Contract, Maybe String)]
flatten Close             = []
flatten p@(Pay _ _ _ _ c) = (p, c, Nothing) : flatten c
flatten p@(Let _ _ c)     = (p, c, Nothing) : flatten c
flatten p@(Assert _ c)    = (p, c, Nothing) : flatten c
flatten p@(If _ trueContract falseContract)
  = (p, trueContract, Just "True") : flatten trueContract
  ++ (p, falseContract, Just "False") : flatten falseContract
flatten p@(When [] t c)
  =  (p, c, Just $ show $ "currentSlot >= " ++ timeoutShow t) : flatten c
-- If the timeout continuation is a Close contract, we omit that link (as it's the default)
-- Maybe later on we want to make this configurable.
flatten p@(When cases t Close)
  =  concatMap (\(Case a c') -> (p, c', Just $ actionShow a) : flatten c') cases
flatten p@(When cases t c)
  = [(p, c, Just $ show $ "currentSlot >= " ++ timeoutShow t)]
    <> flatten c <> concatMap (\(Case a c') -> (p, c', Just $ actionShow a) : flatten c') cases


-- | Escape a string for display in mermaid.  In mermaid everything needs to
-- be in quotes, so we just swap any double-quotes with single-quotes.
escape :: String -> String
escape s = "\"" ++ s' ++ "\""
  where
    s' = map (\c -> if c == '"' then '\'' else c) s


-- | A concise representation of an action for display on an edge.
actionShow :: Action -> String
actionShow = escape . showAction
  where
    showAction (Deposit accountId party tkn val) = show party ++ " deposits " ++ valueShow val ++ " lovelaces into " ++ show accountId ++ " account"
    showAction (Choice (ChoiceId id party) bnd) = show party ++ " makes a choice in " ++ show id
    showAction (Notify obs) = "A notification on " ++ observationShow obs

timeoutShow :: Timeout -> String
timeoutShow (SlotParam slotId) = show slotId
timeoutShow (Slot slotNumber)  = show slotNumber ++ " slots after start"

-- | A concise representation of an Observation for display in a node.
observationShow :: Observation -> String
observationShow = escape . repr
  where
    repr (AndObs obs1 obs2)                   = observationShow obs1 ++ " && " ++ observationShow obs2
    repr (OrObs obs1 obs2)                    = "(" ++ observationShow obs1 ++ ") || (" ++ observationShow obs2 ++ ")"
    repr (NotObs obs)                         = "!" ++ observationShow obs
    repr (ChoseSomething (ChoiceId id party)) = show party ++ " choice on " ++ show id
    repr (ValueGE val1 val2)                  = valueShow val1 ++ " >= " ++ valueShow val2
    repr (ValueGT val1 val2)                  = valueShow val1 ++ " > " ++ valueShow val2
    repr (ValueLT val1 val2)                  = valueShow val1 ++ " < " ++ valueShow val2
    repr (ValueLE val1 val2)                  = valueShow val1 ++ " <= " ++ valueShow val2
    repr (ValueEQ val1 val2)                  = valueShow val1 ++ " == " ++ valueShow val2
    repr TrueObs                              ="true"
    repr FalseObs                             = "false"


-- | A concise representaiton of an individual 'Contract' for displaying on
-- nodes in the mermaid graph.
contractShow :: Contract -> String
contractShow = escape . repr
  where
    repr Close        = "Close"
    repr (Pay from to tok v _) =
      "Pay " ++  valueShow v  ++ " from " ++ show from ++ " to " ++ show to
    repr (If obs _ _ )  = observationShow obs
    repr (When _ _ _) = "When ..."
    repr (Let (ValueId valId) val _) = "let " ++ show valId ++ " = " ++ valueShow val
    repr (Assert obs _) = observationShow obs

valueShow :: Value -> String
valueShow (Constant n)          = show n
valueShow (ConstantParam param) = show param
valueShow (AddValue val1 val2) = "(" ++ valueShow val1 ++ " + " ++ valueShow val2 ++ ")"
valueShow (NegValue val1) = "-" ++ valueShow val1
valueShow (SubValue val1 val2) = "(" ++ valueShow val1 ++ " - " ++ valueShow val2 ++ ")"
valueShow (MulValue val1 val2) = "(" ++ valueShow val1 ++ " * " ++ valueShow val2 ++ ")"
valueShow (ChoiceValue (ChoiceId id party)) = show party ++ " choice on " ++ show id
valueShow (Cond obs val1 val2) = "(" ++ observationShow obs ++ " ? " ++ valueShow val1 ++ " : " ++ valueShow val2 ++ ")"
valueShow (UseValue (ValueId id)) = show id
valueShow (Scale fraction val) = "(" ++ show fraction ++ " * " ++ valueShow val ++ ")"
valueShow other                 = show other
-- valueShow    AvailableMoney S.AccountId S.Token
-- valueShow    SlotIntervalStart
-- valueShow    SlotIntervalEnd
-- | Convert a 'Contract' into a string that can be printed and loaded into the
-- mermaid live editor: <https://mermaid-js.github.io/mermaid-live-editor/>.
toMermaid :: Contract -> String
toMermaid c = unlines . nub $ "graph TB" : map f (flatten c)
  -- Note: We use 'nub' above otherwise there are some duplicate paths leaving
  -- particular nodes. Maybe this could be cleaned up in another way; it's
  -- perhaps a bit fragile given that it depends on the string representation.
  where
    brackets Close           = ("((", "))") -- Circle
    brackets (Pay _ _ _ _ _) = ("([", "])")   -- Subrutine shape
    brackets (If  _ _ _)     = ("{", "}")   -- rhombus
    brackets (When  _ _ _)   = ("{", "}")   -- rhombus
    brackets (Let  _ _ _)    = ("[[", "]]")   -- Square
    brackets (Assert  _ _)   = (">", "]")   -- Flag
    f (a, b, mt) =
      let node n =
            let (bl, br) = brackets n
                nodeId   = "n" ++ (show $ hash $ show n)
             in nodeId ++ bl ++ contractShow n ++ br
          edgeText = maybe "Then" id mt
       in node a ++ " -->|" ++ edgeText ++ "| " ++ node b
