{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Language.Marlowe.Util where
import           Data.List                  (foldl')
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as Map
import           Data.String

import           Language.Marlowe.Semantics
import qualified Language.PlutusTx.Prelude  as P
import           Ledger.Ada                 (adaSymbol, adaToken)
import qualified Ledger.Value               as Val

instance IsString Party where
    fromString s = Role (fromString s)

instance IsString ValueId where
    fromString = ValueId . fromString


ada :: Token
ada = Token adaSymbol adaToken

type AccountsDiff = Map Party Money


emptyAccountsDiff :: AccountsDiff
emptyAccountsDiff = Map.empty


isEmptyAccountsDiff :: AccountsDiff -> Bool
isEmptyAccountsDiff = all Val.isZero


-- Adds a value to the map of outcomes
addAccountsDiff :: Party -> Money -> AccountsDiff -> AccountsDiff
addAccountsDiff party diffValue trOut = let
    newValue = case Map.lookup party trOut of
        Just value -> value P.+ diffValue
        Nothing    -> diffValue
    in Map.insert party newValue trOut


-- | Extract total outcomes from transaction inputs and outputs
getAccountsDiff :: [Payment] -> [Input] -> AccountsDiff
getAccountsDiff payments inputs =
    foldl' (\acc (p, m) -> addAccountsDiff p m acc) emptyAccountsDiff (incomes ++ outcomes)
  where
    incomes  = [ (p,  Val.singleton cur tok m) | IDeposit _ p (Token cur tok) m <- inputs ]
    outcomes = [ (p, P.negate m) | Payment p m  <- payments ]
