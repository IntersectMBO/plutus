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
flatten p@(If _ true false)
  = (p, true, Just "True?") : flatten true
  ++ (p, false, Just "False?") : flatten false
flatten p@(When cases t c)
  =  concatMap (\(Case a c') -> (p, c', Just $ actionShow a) : flatten c') cases

-- flatten p@(When cases t c)
--   = (p, c, Just $ show $ "Timeout: t >= " ++ show t)
--   : concatMap (\(Case a c') -> (p, c', Just $ actionShow a) : flatten c') cases


-- | Escape a string for display in mermaid.  In mermaid everything needs to
-- be in quotes, so we just swap any double-quotes with single-quotes.
escape :: String -> String
escape s = "\"" ++ s' ++ "\""
  where
    s' = map (\c -> if c == '"' then '\'' else c) s


-- | A concise representation of an action for display on an edge.
-- FIXME: Implement a nice version.
actionShow :: Action -> String
actionShow = escape . showAction
  where
    showAction (Deposit accountId party tkn val) = show party ++ " deposits " ++ valueShow val ++ " lovelaces into " ++ show accountId ++ " account"
    showAction (Choice (ChoiceId id party) bnd) = show party ++ " makes a choice in " ++ show id
    showAction (Notify obs) = "Notify"


-- | A concise representation of an Observation for display in a node.
-- FIXME: Implement a nice version.
observationShow :: Observation -> String
observationShow = escape . show


-- | A concise representaiton of an individual 'Contract' for displaying on
-- nodes in the mermaid graph.
contractShow :: Contract -> String
contractShow = escape . repr
  where
    repr Close        = "Close"
    repr (When _ _ _) = "When ..."
    repr (If o _ _ )  = observationShow o
    repr (Pay from to tok v _) =
      "Pay " ++  valueShow v  ++ " from " ++ show from ++ " to " ++ show to
    repr x = show x

valueShow :: Value -> String
valueShow (Constant n)          = show n
valueShow (ConstantParam param) = "$" ++ param
valueShow other                 = show other
-- valueShow    AvailableMoney S.AccountId S.Token
-- valueShow    NegValue Value
-- valueShow    AddValue Value Value
-- valueShow    SubValue Value Value
-- valueShow    MulValue Value Value
-- valueShow    Scale Rational Value
-- valueShow    ChoiceValue S.ChoiceId
-- valueShow    SlotIntervalStart
-- valueShow    SlotIntervalEnd
-- valueShow    UseValue S.ValueId
-- valueShow    Cond Observation Value Value
-- | Convert a 'Contract' into a string that can be printed and loaded into the
-- mermaid live editor: <https://mermaid-js.github.io/mermaid-live-editor/>.
toMermaid :: Contract -> String
toMermaid c = unlines . nub $ "graph TB" : map f (flatten c)
  -- Note: We use 'nub' above otherwise there are some duplicate paths leaving
  -- particular nodes. Maybe this could be cleaned up in another way; it's
  -- perhaps a bit fragile given that it depends on the string representation.
  where
    brackets Close           = ("((", "))") -- Circle
    brackets (Pay _ _ _ _ _) = ("[", "]")   -- Square
    brackets (If  _ _ _)     = ("(", ")")   -- Round
    brackets (When  _ _ _)   = ("{", "}")   -- Round
    brackets (Let  _ _ _)    = ("[", "]")   -- Square
    brackets (Assert  _ _)   = (">", "]")   -- Flag
    f (a, b, mt) =
      let node n =
            let (bl, br) = brackets n
                nodeId   = "n" ++ (show $ hash $ show n)
             in nodeId ++ bl ++ contractShow n ++ br
          edgeText = maybe "Then" id mt
       in node a ++ " -->|" ++ edgeText ++ "| " ++ node b
